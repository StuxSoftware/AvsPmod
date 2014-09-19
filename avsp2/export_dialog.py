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
import wx

from avsp2.i18nutils import _


class AvsFunctionExportImportDialog(wx.Dialog):
    def __init__(self, parent, infoDict, export=True):
        self.export = export
        if export:
            title = _('Export filter customizations')
        else:
            title = _('Import filter customizations')
        wx.Dialog.__init__(self, parent, wx.ID_ANY, title, size=(500, 300), style=wx.DEFAULT_DIALOG_STYLE|wx.RESIZE_BORDER)
        self.calltipDict = infoDict[0]
        self.presetDict = infoDict[1]
        self.docpathDict = infoDict[2]
        self.functiontypeDict = infoDict[3]

        # Create the list control using the dictionary
        decList = [(s.lower(), s) for s in self.calltipDict.keys()]
        decList.sort()
        self.names = [s[1] for s in decList]
        self.checkListBox = wx.CheckListBox(self, wx.ID_ANY, choices=self.names)

        # Create extra control buttons
        def OnButtonSelectAll(event):
            for index in xrange(len(self.names)):
                self.checkListBox.Check(index, True)
        def OnButtonClearAll(event):
            for index in xrange(len(self.names)):
                self.checkListBox.Check(index, False)
        buttonSelectAll = wx.Button(self, wx.ID_ANY, _('Select all'))
        self.Bind(wx.EVT_BUTTON, OnButtonSelectAll, buttonSelectAll)
        buttonClearAll = wx.Button(self, wx.ID_ANY, _('Clear all'))
        self.Bind(wx.EVT_BUTTON, OnButtonClearAll, buttonClearAll)

        if export:
            staticText = wx.StaticText(self, wx.ID_ANY, _('Select filters to export:'))
            extraItem = (-1, 20)
        else:
            staticText = wx.StaticText(self, wx.ID_ANY, _('Select filters to import from the file:'))
            # Import dialog, check all names by default
            for index in xrange(len(self.names)):
                self.checkListBox.Check(index)
            # Extra controls to provide options for import information
            #~ self.checkBoxCalltip = wx.CheckBox(self, wx.ID_ANY, _('Calltips'))
            #~ self.checkBoxPreset = wx.CheckBox(self, wx.ID_ANY, _('Presets'))
            #~ self.checkBoxDocpath = wx.CheckBox(self, wx.ID_ANY, _('Docpaths'))
            #~ self.checkBoxType = wx.CheckBox(self, wx.ID_ANY, _('Filter types'))
            #~ staticBox = wx.StaticBox(self, wx.ID_ANY, _('Import from filters:'))
            #~ staticBoxSizer = wx.StaticBoxSizer(staticBox, wx.HORIZONTAL)
            #~ for item in (self.checkBoxCalltip, self.checkBoxPreset, self.checkBoxDocpath, self.checkBoxType):
                #~ item.SetValue(True)
                #~ staticBoxSizer.Add(item, 0, wx.ALL, 5)
            self.checkBoxOverwriteAll = wx.CheckBox(self, wx.ID_ANY, _('Overwrite all data'))
            self.checkBoxOverwriteAll.SetValue(True)
            extraItem = wx.BoxSizer(wx.VERTICAL)
            #~ extraItem.Add(staticBoxSizer, 0, wx.BOTTOM, 10)
            extraItem.Add(self.checkBoxOverwriteAll, 0, wx.LEFT|wx.BOTTOM, 5)

        # Standard buttons
        okay  = wx.Button(self, wx.ID_OK, _('OK'))
        self.Bind(wx.EVT_BUTTON, self.OnButtonOK, okay)
        cancel = wx.Button(self, wx.ID_CANCEL, _('Cancel'))
        btns = wx.StdDialogButtonSizer()
        btns.AddButton(okay)
        btns.AddButton(cancel)
        btns.Realize()

        # Size the elements
        buttonSizer = wx.BoxSizer(wx.VERTICAL)
        buttonSizer.Add(buttonSelectAll, 0, wx.ALL, 5)
        buttonSizer.Add(buttonClearAll, 0, wx.ALL, 5)
        listSizer = wx.BoxSizer(wx.HORIZONTAL)
        listSizer.Add(self.checkListBox, 1, wx.EXPAND|wx.ALL, 5)
        listSizer.Add(buttonSizer, 0, wx.ALL, 5)
        dlgSizer = wx.BoxSizer(wx.VERTICAL)
        dlgSizer.Add((-1,5))
        dlgSizer.Add(staticText, 0, wx.ALL, 5)
        dlgSizer.Add(listSizer, 1, wx.EXPAND|wx.LEFT|wx.RIGHT, 5)
        dlgSizer.Add(extraItem, 0, wx.ALL, 5)
        dlgSizer.Add(btns, 0, wx.EXPAND|wx.ALL, 5)
        self.SetSizer(dlgSizer)
        dlgSizer.SetSizeHints(self)
        # Misc
        okay.SetDefault()

    def OnButtonOK(self, event):
        self.dlgDataDict = {}
        # Build the dictionnary from the checked filters
        for i, name in enumerate(self.names):
            if self.checkListBox.IsChecked(i):
                calltip = self.calltipDict.get(name, '')
                preset = self.presetDict.get(name, '')
                docpath = self.docpathDict.get(name, '')
                ftype = self.functiontypeDict.get(name, '')
                self.dlgDataDict[name] = (calltip, preset, docpath, ftype)
        if not self.dlgDataDict:
            wx.MessageBox(_('You must select at least one filter!'), _('Warning'))
            return
        event.Skip()

    def GetData(self):
        return self.dlgDataDict

    def GetOverwriteAll(self):
        return self.checkBoxOverwriteAll.GetValue()
