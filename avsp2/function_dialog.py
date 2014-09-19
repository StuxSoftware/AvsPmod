# AvsP - an AviSynth editor
#
# Copyright 2007 Peter Jang <http://www.avisynth.org/qwerpoi>
#           2010-2014 the AvsPmod authors <https://github.com/avspmod/avspmod>
#
# Printing support based on stcprint.py from Peppy/Editra (wxWidgets license)
# Copyright 2007 Cody Precord <staff@editra.org>
#           2009 Rob McMullen <robm@users.sourceforge.net>
#
#  This program is free software; you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation; either version 2 of the License, or
#  (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program; if not, write to the Free Software
#  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA, or visit
#  http://www.gnu.org/copyleft/gpl.html .

# Dependencies:
#     Python (tested on v2.6 and 2.7)
#     wxPython (tested on v2.8 Unicode and 2.9)
#     cffi and its dependencies (only for x86-64, tested on v0.8.1)
#         pycparser
#         Visual Studio 2008
#     avisynth_c.h (only for x86-64, interface 5, or at least 3 + colorspaces
#                   from 5, tested with the header used by x264)
# Scripts:
#     wxp.py (general wxPython framework classes)
#     avisynth.py (Python AviSynth/AvxSynth wrapper, only for x86-32)
#     avisynth_cffi.py (Python AviSynth wrapper, only for x86-64)
#     pyavs.py (AvsP AviSynth support by loading AviSynth directly as a library)
#     pyavs_avifile.py (AvsP AviSynth support through Windows AVIFile routines)
#     icon.py (icons embedded in a Python script)
#     i18n.py (internationalization and localization)
#     global_vars.py (application info and other shared variables)
import os
import re
import sys
import urllib2
import collections

try:
    import cPickle
except ImportError:
    import pickle as cPickle

import wx

import wxp
from avsp2.i18nutils import _
from avsp2.sliders import AvsFilterAutoSliderInfo

class AvsFunctionDialog(wx.Dialog):
    """
    Dialog for AviSynth filter information.
    """
    def __init__(self, parent, filterDict, overrideDict, avsfilterdict,
                       presetDict, removedSet, pluginDict, shortnamesDict,
                       installed_plugins_filternames,
                       installed_avsi_filternames, functionName=None,
                       functionArgs=None, CreateDefaultPreset=None,
                       ExportFilterData=None, nag=True):
        wx.Dialog.__init__(
            self, parent, wx.ID_ANY,
            _('Add or override AviSynth functions in the database'),
            size=(500, 300), style=wx.DEFAULT_DIALOG_STYLE|wx.RESIZE_BORDER
        )
        self.parent = parent
        self.filterDict = filterDict.copy()
        self.overrideDict = overrideDict.copy()
        self.avsfilterdict = avsfilterdict.copy()
        self.presetDict = presetDict.copy()
        self.removedSet = removedSet.copy()
        self.pluginDict = pluginDict.copy()
        self.shortnamesDict = shortnamesDict.copy()
        self.installed_plugins_filternames = installed_plugins_filternames
        self.installed_avsi_filternames = installed_avsi_filternames
        self.CreateDefaultPreset = CreateDefaultPreset
        self.ExportFilterData = ExportFilterData
        self.nag = nag
        self.CreateWindowElements()
        self.CreateFilterInfoDialog()
        if functionName is not None:
            wx.FutureCall(100, self.HighlightFunction, functionName, functionArgs)

    def HighlightFunction(self, functionName, functionArgs):
        lowername = functionName.lower()
        if lowername in self.avsfilterdict:
            lowername = self.avsfilterdict[lowername][3] or lowername
            for index in xrange(self.notebook.GetPageCount()):
                panel = self.notebook.GetPage(index)
                listbox = panel.listbox
                for i in xrange(listbox.GetCount()):
                    label = listbox.GetString(i)
                    if label.split()[0].lower() == lowername:
                        self.notebook.SetSelection(index)
                        listbox.SetSelection(i)
                        self.EditFunctionInfo(arg=functionArgs, prompt=True)
                        return
        else: # functionName was not found, show dialog to define new function
            self.AddNewFunction(functionName, arg=functionArgs, prompt=True)

    def CreateWindowElements(self):
        self.notebook = wxp.Notebook(self, wx.ID_ANY, style=wx.NO_BORDER,
                                     invert_scroll=self.GetParent().options['invertscrolling'])

        class CheckListBox(wx.CheckListBox):
            def __init__(self, *args, **kwargs):
                wx.CheckListBox.__init__(self, *args, **kwargs)
                self.Bind(wx.EVT_CHECKLISTBOX, self.OnCheckListBox)
                self.removedSet = self.GetTopLevelParent().removedSet

            def Check(self, item, check=True):
                wx.CheckListBox.Check(self, item, check)
                self.UpdateRemovedSet(item)

            def OnCheckListBox(self, event):
                self.UpdateRemovedSet(event.GetInt())
                event.Skip()

            def UpdateRemovedSet(self, item):
                name = self.GetString(item).split()[0].lower()
                if self.IsChecked(item):
                    if name in self.removedSet:
                        self.removedSet.remove(name)
                else:
                    self.removedSet.add(name)

        pageInfo = (
            (_('Core filters'), 0),
            (_('Plugins'), 2),
            (_('User functions'), 3),
            (_('Script functions'), 4),
            (_('Clip properties'), 1),
        )
        pageDict = collections.defaultdict(list)
        for key in set(self.filterDict.keys()+self.overrideDict.keys()):
            name, args, ftype = self.overrideDict.get(key, (None, None, None))
            extra = ' '
            if name is None:
                try:
                    name, args, ftype = self.filterDict[key]
                except:
                    continue
            else:
                extra += '*'
            if key in self.presetDict:
                extra += '~'
            pageDict[ftype].append(name + extra)
        for title, index in pageInfo:
            panel = wx.Panel(self.notebook, wx.ID_ANY, size=(700,-1))
            self.notebook.AddPage(panel, title)
            # List box

            #~ choices = [
                #~ self.overrideDict.get(key, value)[0]
                #~ for key, value in self.filterDict.items()
                #~ if value[2] == index
            #~ ]

            #~ d1 = dict([(lowername, name) for lowername, (name,args,ftype) in self.filterDict.items() if ftype==index])
            #~ d2 = dict([(lowername, name+' *') for lowername, (name,args,ftype) in self.overrideDict.items() if ftype==index])
            #~ d1.update(d2)
            #~ choices = [value for key, value in d1.items()]

            choices = pageDict[index]
            listbox = CheckListBox(panel, wx.ID_ANY, choices=choices, size=(-1,300), style=wx.LB_SORT)
            if choices:
                listbox.SetSelection(0)
            listbox.Bind(wx.EVT_LISTBOX_DCLICK, lambda event: self.EditFunctionInfo())
            for i in xrange(listbox.GetCount()):
                name = listbox.GetString(i).split()[0]
                if name.lower() not in self.removedSet:
                    listbox.Check(i)
            title = title.lower()
            # Buttons
            buttonadd = wx.Button(panel, wx.ID_ANY, _('New function'))#, size=(100, -1))
            buttonedit = wx.Button(panel, wx.ID_ANY, _('Edit selected'))
            buttondelete = wx.Button(panel, wx.ID_ANY, _('Delete selected'))
            buttoncheckall = wx.Button(panel, wx.ID_ANY, _('Select all'))
            buttonuncheckall = wx.Button(panel, wx.ID_ANY, _('Clear all'))
            panel.Bind(wx.EVT_BUTTON, lambda event: self.AddNewFunction(ftype=-1), buttonadd)
            panel.Bind(wx.EVT_BUTTON, lambda event: self.EditFunctionInfo(), buttonedit)
            panel.Bind(wx.EVT_BUTTON, lambda event: self.DeleteFunction(), buttondelete)
            panel.Bind(wx.EVT_BUTTON, lambda event: self.CheckAllFunctions(True), buttoncheckall)
            panel.Bind(wx.EVT_BUTTON, lambda event: self.CheckAllFunctions(False), buttonuncheckall)
            buttonSizer = wx.BoxSizer(wx.VERTICAL)
            buttonSizer.Add(buttonadd, 0, wx.EXPAND|wx.TOP|wx.BOTTOM, 5)
            buttonSizer.Add(buttonedit, 0, wx.EXPAND|wx.BOTTOM, 5)
            buttonSizer.Add(buttondelete, 0, wx.EXPAND|wx.BOTTOM, 5)
            buttonSizer.Add(wx.StaticLine(panel, wx.ID_ANY, style=wx.HORIZONTAL), 0, wx.EXPAND|wx.TOP|wx.BOTTOM, 5)
            buttonSizer.Add(buttonuncheckall, 0, wx.EXPAND|wx.TOP|wx.BOTTOM, 5)
            buttonSizer.Add(buttoncheckall, 0, wx.EXPAND|wx.BOTTOM, 5)
            #~ if index == 2:
                #~ self.buttonclearlongnames = wx.Button(panel, wx.ID_ANY, _('Clear long names'))
                #~ panel.Bind(wx.EVT_BUTTON, lambda event: self.ClearLongNames(), self.buttonclearlongnames)
                #~ buttonSizer.Add(self.buttonclearlongnames, 0, wx.EXPAND|wx.BOTTOM, 5)
            if index in (2, 3):
                buttonselectinstalled = wx.Button(panel, wx.ID_ANY, _('Select installed'))
                panel.Bind(wx.EVT_BUTTON, lambda event: self.SelectInstalledFilters(), buttonselectinstalled)
                buttonSizer.Add(buttonselectinstalled, 0, wx.EXPAND|wx.BOTTOM, 5)
            # Size the elements in the panel
            listboxSizer = wx.BoxSizer(wx.HORIZONTAL)
            listboxSizer.Add(listbox, 1, wx.EXPAND|wx.RIGHT, 15)
            listboxSizer.Add(buttonSizer, 0, wx.EXPAND|wx.RIGHT, 5)
            panelSizer = wx.BoxSizer(wx.VERTICAL)
            panelSizer.Add(listboxSizer, 1, wx.EXPAND|wx.ALL, 5)
            panel.SetSizer(panelSizer)
            panelSizer.Layout()
            # Bind items to the panel itself
            panel.listbox = listbox
            panel.functiontype = index
        self.CreatePluginsContextMenu()
        # Buttons
        button0 = wx.Button(self, wx.ID_ANY, _('Import'))
        menu0 = wx.Menu()
        menuItem = menu0.Append(wx.ID_ANY, _('Import from files'))
        self.Bind(wx.EVT_MENU, lambda event: self.ImportFromFiles(), menuItem)
        menuItem = menu0.Append(wx.ID_ANY, _('Import from wiki'))
        self.Bind(wx.EVT_MENU, lambda event: self.ImportFromFiles(wiki=True), menuItem)
        self.Bind(wx.EVT_BUTTON, lambda event: button0.PopupMenu(
                    menu0, (1, button0.GetSizeTuple()[1])), button0)
        button1 = wx.Button(self, wx.ID_ANY, _('Export customizations'))
        self.Bind(wx.EVT_BUTTON, lambda event: self.ExportCustomizations(), button1)
        button2 = wx.Button(self, wx.ID_ANY, _('Clear customizations'))
        self.Bind(wx.EVT_BUTTON, lambda event: self.ClearCustomizations(), button2)
        button3 = wx.Button(self, wx.ID_ANY, _('Clear manual presets'))
        self.Bind(wx.EVT_BUTTON, lambda event: self.ClearPresets(), button3)
        buttonSizer = wx.BoxSizer(wx.HORIZONTAL)
        buttonSizer.Add(button0, 0, wx.RIGHT, 5)
        buttonSizer.Add(button1, 0, wx.RIGHT, 5)
        buttonSizer.Add(button2, 0, wx.RIGHT, 5)
        buttonSizer.Add(button3, 0, wx.RIGHT, 5)
        self.checkBox = wx.CheckBox(self, wx.ID_ANY, _("When importing, don't show the choice dialog"))
        # Standard buttons
        okay  = wx.Button(self, wx.ID_OK, _('OK'))
        #~ self.Bind(wx.EVT_BUTTON, self.OnButtonOK, okay)
        cancel = wx.Button(self, wx.ID_CANCEL, _('Cancel'))
        sdtbtns = wx.StdDialogButtonSizer()
        sdtbtns.Add(self.checkBox)
        sdtbtns.AddButton(okay)
        sdtbtns.AddButton(cancel)
        sdtbtns.Realize()
        # Size the elements
        dlgSizer = wx.BoxSizer(wx.VERTICAL)
        dlgSizer.Add(self.notebook, 1, wx.EXPAND|wx.ALL, 5)
        dlgSizer.Add(buttonSizer, 0, wx.LEFT, 5)
        dlgSizer.Add(wx.StaticLine(self, style=wx.HORIZONTAL), 0, wx.EXPAND|wx.TOP|wx.BOTTOM, 5)
        dlgSizer.Add(sdtbtns, 0, wx.EXPAND|wx.ALL, 5)
        self.SetSizer(dlgSizer)
        dlgSizer.SetSizeHints(self)
        dlgSizer.Layout()
        # Misc
        def OnPageChanged(event):
            event.GetEventObject().GetCurrentPage().SetFocus()
            event.Skip()
        self.Bind(wx.EVT_NOTEBOOK_PAGE_CHANGED, OnPageChanged)
        self.notebook.GetCurrentPage().listbox.SetFocus()
        okay.SetDefault()

    def CreateFilterInfoDialog(self, resetargsbutton=True):
        dlg = wx.Dialog(self, wx.ID_ANY, _('Edit function information'))
        staticText0 = wx.StaticText(dlg, wx.ID_ANY, _('Name:'))
        textCtrl0 = wx.TextCtrl(dlg, wx.ID_ANY, size=(200,-1))
        staticText1 = wx.StaticText(dlg, wx.ID_ANY, _('Type:'))
        choices = [_('core filter'), _('clip property'), _('plugin'), _('user function'), _('script function')]
        choiceBox1 = wx.Choice(dlg, wx.ID_ANY, choices=choices)
        staticText2 = wx.StaticText(dlg, wx.ID_ANY, _('Arguments:'))
        staticText2_4 = wx.StaticText(dlg, wx.ID_ANY, _('define sliders'))
        staticText2_5 = wx.StaticText(dlg, wx.ID_ANY, _('reset to default'))
        for eachCtrl in (staticText2_4, staticText2_5):
            font = eachCtrl.GetFont()
            font.SetUnderlined(True)
            eachCtrl.SetFont(font)
            eachCtrl.SetForegroundColour(wx.Colour(0,0,255))
            eachCtrl.SetCursor(wx.StockCursor(wx.CURSOR_HAND))
        def OnArgsEditSliders(event):
            name = textCtrl0.GetValue()
            dlg2 = AvsFilterAutoSliderInfo(dlg, self.GetParent(), name, textCtrl2.GetValue(), title=_('Slider information'))
            ID = dlg2.ShowModal()
            if ID == wx.ID_OK:
                textCtrl2.SetValue(dlg2.GetNewFilterInfo())
            dlg2.Destroy()
        staticText2_4.Bind(wx.EVT_LEFT_DOWN, OnArgsEditSliders)
        def OnClickSetToDefault(event):
            textCtrl0.SetValue(dlg.defaultName)
            textCtrl2.SetValue(dlg.defaultArgs)
        staticText2_5.Bind(wx.EVT_LEFT_DOWN, OnClickSetToDefault)
        textCtrl2 = wxp.TextCtrl(dlg, wx.ID_ANY, size=(200,200), style=wx.TE_MULTILINE|wx.HSCROLL)
        def OnArgsChange(event):
            if checkBox3.IsChecked():
                name = textCtrl0.GetValue() #dlg.defaultName
                args= textCtrl2.GetValue()
                textCtrl3.SetValue(self.CreateDefaultPreset(name, args))
        textCtrl0.Bind(wx.EVT_TEXT, OnArgsChange)
        textCtrl2.Bind(wx.EVT_TEXT, OnArgsChange)
        #~ textCtrl2.Bind(wx.EVT_LEFT_DCLICK, OnArgsEditSliders)
        staticText3 = wx.StaticText(dlg, wx.ID_ANY, _('Preset:'))
        checkBox3 = wx.CheckBox(dlg, wx.ID_ANY, _('Auto-generate'))
        def OnCheck(event):
            if checkBox3.IsChecked():
                textCtrl3.SetEditable(False)
                colour = self.GetBackgroundColour()
                textCtrl3.SetBackgroundColour(colour)
                OnArgsChange(None)
            else:
                textCtrl3.SetEditable(True)
                textCtrl3.SetBackgroundColour(wx.WHITE)
        checkBox3.Bind(wx.EVT_CHECKBOX, OnCheck)
        textCtrl3 = wxp.TextCtrl(dlg, wx.ID_ANY, size=(-1,50), style=wx.TE_MULTILINE|wx.HSCROLL)
        # Standard buttons
        okay  = wx.Button(dlg, wx.ID_OK, _('OK'))
        def OnFilterInfoDialogButtonOK(event):
            newName = textCtrl0.GetValue()
            enteredName = dlg.enteredName
            if enteredName is None:
                lowername = newName.lower()
                if lowername in self.overrideDict or lowername in self.filterDict:
                    wx.MessageBox(_('Filter name already exists!'), _('Error'), style=wx.OK|wx.ICON_ERROR)
                    textCtrl0.SetFocus()
                    return
                if not newName or newName[0].isdigit() or re.findall('\W', newName):
                    wx.MessageBox(_('Invalid filter name!'), _('Error'), style=wx.OK|wx.ICON_ERROR)
                    textCtrl0.SetFocus()
                    return
            elif newName.lower() != enteredName.lower():
                wx.MessageBox(_('Renaming not allowed!'), _('Error'), style=wx.OK|wx.ICON_ERROR)
                textCtrl0.SetFocus()
                return
            if dlg.typeBox.GetCurrentSelection() == 2 and newName.count('_') == 0:
                wx.MessageBox(_('You must use dllname_function naming format for plugins!'),
                              _('Error'), style=wx.OK|wx.ICON_ERROR)
                textCtrl0.SetFocus()
                return
            event.Skip()
        dlg.Bind(wx.EVT_BUTTON, OnFilterInfoDialogButtonOK, okay)
        cancel = wx.Button(dlg, wx.ID_CANCEL, _('Cancel'))
        btns = wx.StdDialogButtonSizer()
        btns.AddButton(okay)
        btns.AddButton(cancel)
        btns.Realize()
        # Size the elements
        sizer01 = wx.FlexGridSizer(cols=4, hgap=5, vgap=5)
        sizer01.Add(staticText0, 0, wx.ALIGN_CENTER_VERTICAL)
        sizer01.Add(textCtrl0, 0, wx.EXPAND|wx.RIGHT, 10)
        sizer01.Add(staticText1, 0, wx.ALIGN_CENTER_VERTICAL)
        sizer01.Add(choiceBox1, 0, wx.EXPAND)
        sizer2 = wx.BoxSizer(wx.HORIZONTAL)
        sizer2.Add(staticText2, 0, wx.ALL, 0)
        sizer2.Add((-1,-1), 1, wx.EXPAND|wx.ALL, 0)
        sizer2.Add(staticText2_5, 0, wx.RIGHT, 10)
        sizer2.Add(staticText2_4, 0, wx.LEFT|wx.RIGHT, 10)
        sizer3 = wx.BoxSizer(wx.HORIZONTAL)
        sizer3.Add(staticText3, 0, wx.ALL, 0)
        sizer3.Add((-1,-1), 1, wx.EXPAND|wx.ALL, 0)
        sizer3.Add(checkBox3, 0, wx.RIGHT, 10)
        dlgSizer = wx.BoxSizer(wx.VERTICAL)
        dlgSizer.Add((-1,5), 0, wx.EXPAND|wx.ALL, 0)
        dlgSizer.Add(sizer01, 0, wx.EXPAND|wx.ALL, 5)
        dlgSizer.Add(wx.StaticLine(dlg, style=wx.HORIZONTAL), 0, wx.EXPAND|wx.TOP|wx.BOTTOM, 5)
        #~ dlgSizer.Add(staticText2, 0, wx.EXPAND|wx.TOP|wx.LEFT, 5)
        dlgSizer.Add(sizer2, 0, wx.EXPAND|wx.TOP|wx.LEFT, 5)
        dlgSizer.Add(textCtrl2, 1, wx.EXPAND|wx.ALL, 5)
        #~ dlgSizer.Add(staticText3, 0, wx.TOP|wx.LEFT, 5)
        dlgSizer.Add(sizer3, 0, wx.EXPAND|wx.TOP|wx.LEFT, 5)
        dlgSizer.Add(textCtrl3, 0, wx.EXPAND|wx.ALL, 5)
        dlgSizer.Add(btns, 0, wx.EXPAND|wx.ALL, 5)
        dlg.SetSizer(dlgSizer)
        if not resetargsbutton:
            staticText2_5.Hide()
        def SetAutopreset(on=True):
            if on:
                checkBox3.SetValue(True)
                textCtrl3.SetEditable(False)
                colour = self.GetBackgroundColour()
                textCtrl3.SetBackgroundColour(colour)
            else:
                checkBox3.SetValue(False)
                textCtrl3.SetEditable(True)
                textCtrl3.SetBackgroundColour(wx.WHITE)
        dlg.SetAutopreset = SetAutopreset
        dlg.Fit()
        dlgSizer.Layout()
        # Bind variables
        dlg.nameBox = textCtrl0
        dlg.typeBox = choiceBox1
        dlg.argsBox = textCtrl2
        dlg.presetBox = textCtrl3
        dlg.resetCtrl = staticText2_5
        dlg.autopresetCheckbox = checkBox3
        dlg.cancelButton = cancel
        dlg.defaultArgs = ''
        dlg.defaultName = ''
        dlg.enteredName = ''
        self.FilterInfoDialog = dlg

    def CreatePluginsContextMenu(self):
        """Chose between long and short names"""

        def OnPluginsContextMenu(event):
            name = listbox.GetString(listbox.GetSelection()).split()[0].lower()
            item = menu.FindItemByPosition((self.pluginDict[name] + 2) % 3)
            item.Check()
            listbox.PopupMenu(menu)

        def OnContextMenuItem(event):
            id = event.GetId()
            if id in [idLong, idShort, idBoth]:
                if id == idLong:
                    value = 1
                elif id == idShort:
                    value = 2
                elif id == idBoth:
                    value = 0
                name = listbox.GetString(listbox.GetSelection())
                self.pluginDict[name.split()[0].lower()] = value
            else:
                if id == idLongOnly:
                    value = 1
                elif id == idShortOnly:
                    value = 2
                elif id == idAll:
                    value = 0
                for name in self.pluginDict:
                    self.pluginDict[name] = value

        listbox = self.notebook.GetPage(1).listbox
        listbox.Bind(wx.EVT_CONTEXT_MENU, OnPluginsContextMenu)
        idLong = wx.NewId()
        idShort = wx.NewId()
        idBoth = wx.NewId()
        idLongOnly = wx.NewId()
        idShortOnly = wx.NewId()
        idAll = wx.NewId()
        menu = wx.Menu()
        menu.AppendRadioItem(idLong, _('Long name'))
        menu.AppendRadioItem(idShort, _('Short name'))
        menu.AppendRadioItem(idBoth, _('Both'))
        menu.AppendSeparator()
        menu.Append(idLongOnly, _('Only long names'))
        menu.Append(idShortOnly, _('Only short names'))
        menu.Append(idAll, _('All names'))
        listbox.Bind(wx.EVT_MENU, OnContextMenuItem, id=idLong)
        listbox.Bind(wx.EVT_MENU, OnContextMenuItem, id=idShort)
        listbox.Bind(wx.EVT_MENU, OnContextMenuItem, id=idBoth)
        listbox.Bind(wx.EVT_MENU, OnContextMenuItem, id=idLongOnly)
        listbox.Bind(wx.EVT_MENU, OnContextMenuItem, id=idShortOnly)
        listbox.Bind(wx.EVT_MENU, OnContextMenuItem, id=idAll)

    def CheckAllFunctions(self, check=True):
        listbox = self.notebook.GetCurrentPage().listbox
        for i in xrange(listbox.GetCount()):
            listbox.Check(i, check)

    def _x_ClearLongNames(self):
        listbox = self.notebook.GetCurrentPage().listbox
        for i in xrange(listbox.GetCount()):
            if listbox.GetString(i).count('_') > 0:
                listbox.Check(i, False)

    def SelectInstalledFilters(self):
        index = self.notebook.GetSelection()
        if index == 1:
            filters = self.installed_plugins_filternames
        elif index == 2:
            filters = self.installed_avsi_filternames
        else: return
        listbox = self.notebook.GetCurrentPage().listbox
        for i in xrange(listbox.GetCount()):
            boolCheck = (listbox.GetString(i).split()[0].lower() in filters)
            listbox.Check(i, boolCheck)

    def ImportFromFiles(self, wiki=False):
        filenames, filterInfo, unrecognized = [], [], []
        if wiki:
            filenames = (self.GetParent().filterdbremote_plugins,
                         self.GetParent().filterdbremote_scripts)
        else:
            title = _('Open Customization files, Avisynth scripts or Avsp options files')
            initial_dir = self.GetParent().ExpandVars(self.GetParent().options['pluginsdir'])
            filefilter = (_('All supported') + '|*.txt;*.md;*.avsi;*.avs;*.dat|' +
                          _('Customization file') + ' (*.txt, *.md)|*.txt;*.md|' +
                          _('AviSynth script') + ' (*.avs, *.avsi)|*.avs;*.avsi|' +
                          _('AvsP data') + ' (*.dat)|*.dat|' +
                          _('All files') + ' (*.*)|*.*')
            dlg = wx.FileDialog(self, title, initial_dir, '', filefilter,
                                wx.OPEN|wx.MULTIPLE|wx.FILE_MUST_EXIST)
            ID = dlg.ShowModal()
            if ID == wx.ID_OK:
                filenames = dlg.GetPaths()
            dlg.Destroy()
            if not filenames:
                return

        for filename in filenames:
            ext = os.path.splitext(filename)[1]
            try:
                if ext in ['.avs', '.avsi']:
                    info = self.ParseAvisynthScript(filename)
                elif ext in ['.txt', '.md']:
                    info = self.ParseCustomizations(filename)
                elif ext == '.dat':
                    if filename.startswith('http'):
                        f = urllib2.urlopen(filename)
                    else:
                        f = open(filename, 'rb')
                    data = cPickle.load(f)
                    f.close()
                    info = []
                    for filtername, filterargs, ftype in data['filteroverrides'].values():
                        info.append((filename, filtername, filterargs, ftype))
                else:
                    info = None
            except (urllib2.URLError, urllib2.HTTPError), err:
                wx.MessageBox(u'\n\n'.join((os.path.basename(filename), unicode(err))),
                              _('Error'), style=wx.OK|wx.ICON_ERROR)
                continue
            except:
                info = None
            if not info:
                unrecognized.append(filename)
            else:
                filterInfo += info
        if filterInfo and (wiki or not self.checkBox.IsChecked()):
            self.SelectImportFilters(filterInfo)
        for filename, filtername, filterargs, ftype in filterInfo:
            self.EditFunctionInfo(filtername, filterargs, ftype)
        if unrecognized:
            wx.MessageBox('\n'.join(unrecognized), _('Unrecognized files'))

    def SelectImportFilters(self, filterInfo):
        choices = []
        filterInfo.sort(key=lambda fi:
                    [i.lower() if isinstance(i, basestring) else i for i in fi])
        for filename, filtername, filterargs, ftype in filterInfo:
            choices.append(os.path.basename(filename) + ' -> ' + filtername)
        dlg = wx.Dialog(self, wx.ID_ANY, _('Select the functions to import'),
                        style=wx.DEFAULT_DIALOG_STYLE|wx.RESIZE_BORDER)
        listbox = wx.CheckListBox(dlg, wx.ID_ANY, choices=choices, style=wx.LB_EXTENDED)
        customized, not_customized = [], []
        for i in range(len(choices)):
            filename, filtername = choices[i].lower().split(' -> ')
            if filtername in self.overrideDict:
                listbox.SetItemForegroundColour(i, wx.RED)
                customized.append(i)
            else:
                not_customized.append(i)
                if filename.find(filtername) != -1:
                    listbox.Check(i)
        idSelectionAll = wx.NewId()
        idAll = wx.NewId()
        idFileAll = wx.NewId()
        idNotCustomizedAll = wx.NewId()
        idSelectionNone = wx.NewId()
        idNone = wx.NewId()
        idFileNone = wx.NewId()
        idCustomizedNone = wx.NewId()

        def OnContextMenuItem(event):
            id = event.GetId()
            value = id in (idSelectionAll, idAll, idFileAll, idNotCustomizedAll)
            if id in [idSelectionAll, idSelectionNone]:
                listbox_range = listbox.GetSelections()
            elif id in [idAll, idNone]:
                listbox_range = range(len(filterInfo))
            elif id in [idFileAll, idFileNone]:
                pos = listbox.GetSelections()
                if not pos:
                    return
                filename = filterInfo[pos[0]][0]
                listbox_range = (i for i in range(len(filterInfo))
                                 if filename == filterInfo[i][0])
            elif id == idNotCustomizedAll:
                listbox_range = not_customized
            elif id == idCustomizedNone:
                listbox_range = customized
            for i in listbox_range:
                listbox.Check(i, value)

        def OnContextMenu(event):
            listbox.Bind(wx.EVT_MENU, OnContextMenuItem, id=idSelectionAll)
            listbox.Bind(wx.EVT_MENU, OnContextMenuItem, id=idAll)
            listbox.Bind(wx.EVT_MENU, OnContextMenuItem, id=idFileAll)
            listbox.Bind(wx.EVT_MENU, OnContextMenuItem, id=idNotCustomizedAll)
            listbox.Bind(wx.EVT_MENU, OnContextMenuItem, id=idSelectionNone)
            listbox.Bind(wx.EVT_MENU, OnContextMenuItem, id=idNone)
            listbox.Bind(wx.EVT_MENU, OnContextMenuItem, id=idFileNone)
            listbox.Bind(wx.EVT_MENU, OnContextMenuItem, id=idCustomizedNone)
            menu = wx.Menu()
            menu.Append(idSelectionAll, _('Check selected'))
            menu.Append(idAll, _('Check all'))
            menu.Append(idFileAll, _('Check all in this file'))
            menu.Append(idNotCustomizedAll, _('Check all not customized'))
            menu.AppendSeparator()
            menu.Append(idSelectionNone, _('Uncheck selected'))
            menu.Append(idNone, _('Uncheck all'))
            menu.Append(idFileNone, _('Uncheck all in this file'))
            menu.Append(idCustomizedNone, _('Uncheck all customized'))
            listbox.PopupMenu(menu)
            menu.Destroy()

        listbox.Bind(wx.EVT_CONTEXT_MENU, OnContextMenu)
        message = wx.StaticText(dlg, wx.ID_ANY, _('Red - a customized function already exists.'))
        okay  = wx.Button(dlg, wx.ID_OK, _('OK'))
        cancel = wx.Button(dlg, wx.ID_CANCEL, _('Cancel'))
        btns = wx.StdDialogButtonSizer()
        btns.AddButton(okay)
        btns.AddButton(cancel)
        btns.Realize()
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(listbox, 1, wx.EXPAND|wx.ALL,5)
        sizer.Add(message, 0, wx.LEFT, 5)
        sizer.Add(btns, 0, wx.EXPAND|wx.ALL,5)
        dlg.SetSizerAndFit(sizer)
        ID = dlg.ShowModal()
        for i in range(len(choices)-1, -1, -1):
            if ID != wx.ID_OK or not listbox.IsChecked(i):
                del filterInfo[i]
        dlg.Destroy()

    def ParseAvisynthScript(self, *args, **kwargs):
        return self.GetParent().ParseAvisynthScript(*args, **kwargs)

    def ParseCustomizations(self, filename):
        if filename.startswith('http'):
            f = urllib2.urlopen(filename)
        else:
            f = open(filename)
        text = '\n'.join([line.strip() for line in f.readlines()])
        f.close()
        if filename.endswith('.md'):
            text = text.split('```text\n', 1)[1].rsplit('```', 1)[0]
        filterInfo = []
        for section in text.split('\n\n['):
            title, data = section.split(']\n',1)
            title = title.strip('[]').lower()
            if title == 'clipproperties':
                for item in data.split('\n'):
                    if not item.strip():
                        continue
                    splitstring = item.split('(', 1)
                    if len(splitstring) == 2:
                        filtername = splitstring[0].strip()
                        filterargs = '('+splitstring[1].strip(' ')
                    else:
                        filtername = item
                        filterargs = ''
                    filterInfo.append((filename, filtername, filterargs, 1))
            elif title == 'scriptfunctions':
                for item in data.split('\n'):
                    if not item.strip():
                        continue
                    splitstring = item.split('(', 1)
                    if len(splitstring) == 2:
                        filtername = splitstring[0].strip()
                        filterargs = '('+splitstring[1].strip(' ')
                    else:
                        filtername = item
                        filterargs = ''
                    filterInfo.append((filename, filtername, filterargs, 4))
            elif title == 'corefilters':
                for s in data.split('\n\n'):
                    splitstring = s.split('(', 1)
                    if len(splitstring) == 2:
                        filtername = splitstring[0].strip()
                        filterargs = '('+splitstring[1].strip(' ')
                        filterInfo.append((filename, filtername, filterargs, 0))
            elif title == 'plugins':
                for s in data.split('\n\n'):
                    splitstring = s.split('(', 1)
                    if len(splitstring) == 2:
                        filtername = splitstring[0].strip()
                        if not self.parent.GetPluginFunctionShortName(filtername.lower()):
                            print>>sys.stderr, '{0}: {1}'.format(_('Error'), _('Invalid plugin '
                                'function name "{name}". Must be "pluginname_functionname".').format(name=filtername))
                            continue
                        filterargs = '('+splitstring[1].strip(' ')
                        filterInfo.append((filename, filtername, filterargs, 2))
            elif title == 'userfunctions':
                for s in data.split('\n\n'):
                    splitstring = s.split('(', 1)
                    if len(splitstring) == 2:
                        filtername = splitstring[0].strip()
                        filterargs = '('+splitstring[1].strip(' ')
                        filterInfo.append((filename, filtername, filterargs, 3))
        return filterInfo

    def ExportCustomizations(self):
        if len(self.overrideDict) == 0:
            wx.MessageBox(_('No customizations to export!'), _('Error'), style=wx.OK|wx.ICON_ERROR)
            return
        title = _('Save filter customizations')
        initial_dir = self.GetParent().programdir
        filefilter = _('Customization file') + ' (*.txt)|*.txt|' + _('All files') + ' (*.*)|*.*'
        dlg = wx.FileDialog(self, title, initial_dir, '', filefilter, wx.SAVE|wx.OVERWRITE_PROMPT)
        ID = dlg.ShowModal()
        if ID == wx.ID_OK:
            filename = dlg.GetPath()
            self.ExportFilterData(self.overrideDict, filename)
        dlg.Destroy()

    def ClearCustomizations(self):
        dlg = wx.MessageDialog(self, _('This will delete all filter customizations. Continue?'), _('Warning'), wx.YES_NO)
        ID = dlg.ShowModal()
        if ID == wx.ID_YES:
            #~ for lowername, (name, args, ftype) in self.overrideDict.items():
                #~ originalName = self.filterDict.get(lowername, [name])[0]
                #~ newName = originalName+' '
                #~ adjustedName = name+' '
                #~ if lowername in self.overrideDict:
                    #~ adjustedName += '*'
                #~ if lowername in self.presetDict:
                    #~ adjustedName += '~'
                    #~ newName += '~'
                #~ if newName != adjustedName:
                    #~ for index in xrange(self.notebook.GetPageCount()):
                        #~ panel = self.notebook.GetPage(index)
                        #~ if panel.functiontype == ftype:
                            #~ listbox = panel.listbox
                            #~ foundindex = listbox.FindString(adjustedName)
                            #~ if foundindex != wx.NOT_FOUND:
                                #~ listbox.SetString(foundindex, newName)
                            #~ break
            for lowername, (name, args, ftype) in self.overrideDict.iteritems():
                if ftype == 2 and lowername not in self.filterDict:
                    shortname = self.parent.GetPluginFunctionShortName(lowername)
                    if len(self.shortnamesDict[shortname]) == 1:
                        del self.shortnamesDict[shortname]
                    else:
                        self.shortnamesDict[shortname].remove(lowername)
            self.overrideDict = {}
            self.RefreshListNames()
        dlg.Destroy()

    def ClearPresets(self):
        dlg = wx.MessageDialog(self, _('This will delete all manually defined presets. Continue?'), _('Warning'), wx.YES_NO)
        ID = dlg.ShowModal()
        if ID == wx.ID_YES:
            #~ for lowername in self.presetDict.keys():
                #~ value = self.overrideDict.get(lowername)
                #~ if value is None:
                    #~ value = self.filterDict[lowername]
                #~ name, args, ftype = value
                #~ newName = name+' '
                #~ adjustedName = name+' '
                #~ if lowername in self.overrideDict:
                    #~ adjustedName += '*'
                    #~ newName += '*'
                #~ if lowername in self.presetDict:
                    #~ adjustedName += '~'
                #~ if newName != adjustedName:
                    #~ for index in xrange(self.notebook.GetPageCount()):
                        #~ panel = self.notebook.GetPage(index)
                        #~ if panel.functiontype == ftype:
                            #~ listbox = panel.listbox
                            #~ foundindex = listbox.FindString(adjustedName)
                            #~ if foundindex != wx.NOT_FOUND:
                                #~ listbox.SetString(foundindex, newName)
                            #~ break
            self.presetDict = {}
            self.RefreshListNames()
        dlg.Destroy()

    def RefreshListNames(self):
        for index in xrange(self.notebook.GetPageCount()):
            panel = self.notebook.GetPage(index)
            listbox = panel.listbox
            deleteIndices = []
            for i in xrange(listbox.GetCount()):
                name = listbox.GetString(i).split()[0]
                lowername = name.lower()
                extra = ' '
                if lowername in self.overrideDict:
                    extra += '*'
                elif lowername not in self.filterDict:
                    deleteIndices.append(i)
                    continue
                if lowername in self.presetDict:
                    extra += '~'
                newname = name+extra
                if listbox.GetString(i) != newname:
                    listbox.SetString(i, newname)
            deleteIndices.reverse()
            for i in deleteIndices:
                listbox.Delete(i)

    def AddNewFunction(self, name='', ftype=3, arg=None, prompt=None):
        dlg = self.FilterInfoDialog
        if ftype == -1:
            index = self.notebook.GetSelection()
            if index != wx.NOT_FOUND:
                ftype = self.notebook.GetPage(index).functiontype
            else:
                ftype = 3
        else:
            for index in xrange(self.notebook.GetPageCount()):
                panel = self.notebook.GetPage(index)
                if panel.functiontype == ftype:
                    self.notebook.SetSelection(index)
                    break
        #~ lowername = name.lower()
        #~ defaultValues = self.filterDict.get(lowername)
        #~ enteredValues = self.overrideDict.get(lowername, defaultValues)
        #~ if enteredValues is not None:
            #~ enteredName, enteredArgs, enteredType = enteredValues
            #~ defaultName, defaultArgs, defaultType = defaultValues
        #~ else:
            #~ enteredName, enteredArgs, enteredType = ('', '', 3)
            #~ defaultName, defaultArgs, defaultType = (None, None, None)
        #~ enteredPreset = self.presetDict.get(lowername)#, defaultPreset)
        #~ if enteredPreset is not None:
            #~ dlg.SetAutopreset(False)
        #~ else:
            #~ dlg.SetAutopreset(True)
            #~ enteredPreset = self.CreateDefaultPreset(name, enteredArgs)
        defaultName = name
        defaultArgs = '()' if not arg else arg
        dlg.nameBox.SetValue(defaultName)
        dlg.typeBox.SetSelection(ftype)
        dlg.typeBox.Enable()
        dlg.argsBox.SetValue(defaultArgs)
        dlg.presetBox.SetValue('')
        dlg.resetCtrl.Hide()
        dlg.SetAutopreset(True)
        dlg.cancelButton.SetFocus()
        dlg.defaultArgs = defaultArgs
        dlg.defaultName = defaultName
        dlg.enteredName = None
        if prompt is None:
            prompt = not bool(arg)
        if not prompt: ID = wx.ID_OK
        else: ID = dlg.ShowModal()
        if ID == wx.ID_OK:
            newName = dlg.nameBox.GetValue()
            newType = dlg.typeBox.GetSelection()
            newArgs = dlg.argsBox.GetValue()
            newPreset = dlg.presetBox.GetValue()
            boolAutoPreset = dlg.autopresetCheckbox.GetValue()
            for index in xrange(self.notebook.GetPageCount()):
                panel = self.notebook.GetPage(index)
                if panel.functiontype == newType:
                    self.notebook.SetSelection(index)
                    listbox = panel.listbox
                    break
            #else:
                #return
            extra = ' '
            # Update the override dict
            #~ if (newName != defaultName) or (newArgs != defaultArgs):
                #~ self.overrideDict[lowername] = (newName, newArgs, newType)
                #~ extra += '*'
            #~ else:
                #~ if lowername in self.overrideDict:
                    #~ del self.overrideDict[lowername]
            lowername = newName.lower()
            self.overrideDict[lowername] = (newName, newArgs, newType)
            if newType == 2:
                self.pluginDict[lowername] = 0
                self.shortnamesDict[self.parent.GetPluginFunctionShortName(lowername)].append(lowername)
            extra += '*'
            # Update the preset dict
            if boolAutoPreset:
                if lowername in self.presetDict:
                    del self.presetDict[lowername]
            else:
                self.presetDict[lowername] = newPreset
                extra += '~'
            #~ listbox.SetString(listbox.GetSelection(), newName+extra)
            index = listbox.Append(newName+extra)
            listbox.Check(index)
            listbox.SetSelection(index)
            listbox.SetFirstItem(index)

    def EditFunctionInfo(self, name=None, arg=None, ftype=None, prompt=None):
        dlg = self.FilterInfoDialog
        if arg and ftype is not None:
            arg = arg.strip()
            name = unicode(name)
            for index in xrange(self.notebook.GetPageCount()):
                panel = self.notebook.GetPage(index)
                if panel.functiontype == ftype:
                    break
        else:
            panel = self.notebook.GetCurrentPage()
        listbox = panel.listbox
        functiontype = panel.functiontype
        if name is None:
            name = listbox.GetStringSelection().split()[0]
        if not name:
            return
        lowername = name.lower()
        if lowername not in self.filterDict and lowername not in self.overrideDict:
            if not ftype:
                self.AddNewFunction(name)
            else:
                self.AddNewFunction(name, ftype, arg)
            return
        # Fill out default values
        #~ defaultName = self.filterDict[lowername][0]
        #~ defaultArgs = self.filterDict[lowername][1]
        defaultName, defaultArgs, defaultType = self.filterDict.get(lowername, ('', '', None))
        #~ defaultPreset = self.CreateDefaultPreset(name, defaultArgs)
        enteredName = name
        enteredType = functiontype
        enteredArgs = self.overrideDict.get(lowername, (None, defaultArgs, None))[1] if not arg else arg
        #~ defaultPreset = self.CreateDefaultPreset(name, enteredArgs)
        enteredPreset = self.presetDict.get(lowername)#, defaultPreset)
        if enteredPreset is not None:
            dlg.SetAutopreset(False)
        else:
            dlg.SetAutopreset(True)
            enteredPreset = self.CreateDefaultPreset(name, enteredArgs)
        dlg.nameBox.SetValue(enteredName)
        dlg.typeBox.SetSelection(enteredType)
        dlg.argsBox.SetValue(enteredArgs)
        dlg.presetBox.SetValue(enteredPreset)
        if lowername in self.filterDict:
            dlg.typeBox.Disable()
            dlg.resetCtrl.Show()
        else:
            dlg.typeBox.Enable()
            dlg.resetCtrl.Hide()
        dlg.cancelButton.SetFocus()
        dlg.defaultArgs = defaultArgs
        #~ self.defaultPreset = defaultPreset
        dlg.defaultName = defaultName
        dlg.enteredName = enteredName
        if prompt is None:
            prompt = not bool(arg)
        if not prompt: ID = wx.ID_OK
        else: ID = dlg.ShowModal()
        if ID == wx.ID_OK:
            newName = dlg.nameBox.GetValue()
            newType = dlg.typeBox.GetSelection()
            newArgs = dlg.argsBox.GetValue()
            newPreset = dlg.presetBox.GetValue()
            boolAutoPreset = dlg.autopresetCheckbox.GetValue()
            extra = ' '
            # Update the override dict
            if (newName != defaultName) or (newArgs != defaultArgs):
                self.overrideDict[lowername] = (newName, newArgs, newType)
                extra += '*'
            else:
                if lowername in self.overrideDict:
                    del self.overrideDict[lowername]
            # Update the preset dict
            if boolAutoPreset:
                if lowername in self.presetDict:
                    del self.presetDict[lowername]
            else:
                self.presetDict[lowername] = newPreset
                extra += '~'
            if newType == enteredType:
                if arg and ftype is not None:
                    for i in xrange(listbox.GetCount()):
                        if newName == listbox.GetString(i).split()[0]:
                            listbox.SetSelection(i)
                            break
                listbox.SetString(listbox.GetSelection(), newName+extra)
            else:
                shortname = self.parent.GetPluginFunctionShortName(lowername)
                if newType == 2:
                    self.pluginDict[lowername] = 0
                    self.shortnamesDict[shortname].append(lowername)
                elif enteredType == 2:
                    del self.pluginDict[lowername]
                    if len(self.shortnamesDict[shortname]) == 1:
                        del self.shortnamesDict[shortname]
                    else:
                        self.shortnamesDict[shortname].remove(lowername)
                for index in xrange(self.notebook.GetPageCount()):
                    panel = self.notebook.GetPage(index)
                    if panel.functiontype == newType:
                        listindex = listbox.GetSelection()
                        ischecked = listbox.IsChecked(listindex)
                        listbox.Delete(listindex)
                        listindex = panel.listbox.Append(newName+extra)
                        panel.listbox.SetSelection(listindex)
                        panel.listbox.SetFirstItem(listindex)
                        panel.listbox.Check(listindex, ischecked)
                        self.notebook.SetSelection(index)
                        break
                else:
                    return

    def DeleteFunction(self):
        panel = self.notebook.GetCurrentPage()
        listbox = panel.listbox
        index = listbox.GetSelection()
        if index == wx.NOT_FOUND:
            return
        complete_string = listbox.GetString(index)
        name = complete_string.split()[0]
        lowername = name.lower()
        added_by_user = lowername not in self.filterDict
        modified = lowername != complete_string.rstrip().lower()
        if not added_by_user and not modified:
            return
        delete = not self.nag
        if self.nag:
            if added_by_user:
                message = _('Do you really want to delete this custom filter?')
            else:
                message = _('Do you really want to reset this filter?')
            dlg = wx.MessageDialog(self, message, _('Warning'), wx.YES_NO)
            ID = dlg.ShowModal()
            if ID == wx.ID_YES:
                delete = True
            dlg.Destroy()
        if delete:
            if lowername in self.overrideDict:
                del self.overrideDict[lowername]
            if lowername in self.presetDict:
                del self.presetDict[lowername]
            if added_by_user:
                if panel.functiontype == 2:
                    del self.pluginDict[lowername]
                    shortname = self.parent.GetPluginFunctionShortName(lowername)
                    if len(self.shortnamesDict[shortname]) == 1:
                        del self.shortnamesDict[shortname]
                    else:
                        self.shortnamesDict[shortname].remove(lowername)
                if lowername in self.removedSet:
                    self.removedSet.remove(lowername)
                listbox.Delete(index)
            else:
                listbox.SetString(index, name)

    def GetOverrideDict(self):
        return self.overrideDict

    def GetPresetDict(self):
        return self.presetDict

    def GetRemovedSet(self):
        return self.removedSet

    def GetAutocompletePluginNames(self):
        return self.pluginDict

    def GetPluginShortNames(self):
        return self.shortnamesDict
