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
import wx.lib.buttons as wxButtons

import wxp
from avsp2.i18nutils import _

class AvsStyleDialog(wx.Dialog):
    """
    Dialog for choosing AviSynth specific fonts and colors.
    """

    # TODO: add export and import styles, macros to import...
    def __init__(self, parent, dlgInfo, options, defaults, colour_data=None, extra=None, title=_('AviSynth fonts and colors')):
        wx.Dialog.__init__(self, parent, wx.ID_ANY, title)
        self.dlgInfo = dlgInfo
        self.options = options.copy()
        self.defaults = defaults
        self.colour_data = colour_data
        # Create the font buttons
        self.controls = {}
        self.controls2 = {}
        self.notebook = wxp.Notebook(self, wx.ID_ANY, style=wx.NO_BORDER,
                                     invert_scroll=self.GetParent().options['invertscrolling'])
        def OnNotebookPageChanged(event):
            event.GetEventObject().GetCurrentPage().SetFocus()
            event.Skip()
        for tabLabel, tabInfo in dlgInfo:
            tabPanel = wx.Panel(self.notebook, wx.ID_ANY)
            self.notebook.AddPage(tabPanel, tabLabel)
            sizer = wx.FlexGridSizer(cols=4, hgap=20, vgap=5)
            sizer.Add((0,0), 0)
            for label in ( _('Font'), _('Text color'), _('Background')):
                staticText = wx.StaticText(tabPanel, wx.ID_ANY, label)
                font = staticText.GetFont()
                font.SetUnderlined(True)
                font.SetWeight(wx.FONTWEIGHT_BOLD)
                staticText.SetFont(font)
                sizer.Add(staticText, flag=wx.ALIGN_CENTER)
            for label, key in tabInfo:
                (fontSize, fontStyle, fontWeight, fontUnderline,
                fontFace, fontFore, fontBack) = self.ParseStyleInfo(options[key].split(','))
                if fontFace is not None:
                    font = wx.Font(fontSize, wx.FONTFAMILY_DEFAULT, fontStyle, fontWeight, fontUnderline, faceName=fontFace)
                else:
                    font = None
                # Create the controls
                if type(label) is tuple:
                    label, optKey, tip = label
                    staticText = checkbox = wx.CheckBox(tabPanel, wx.ID_ANY, label)
                    checkbox.SetValue(parent.options[optKey])
                    checkbox.SetToolTipString(tip)
                    self.controls2[optKey] = checkbox
                else:
                    staticText = wx.StaticText(tabPanel, wx.ID_ANY, label)
                if font is not None:
                    fontLabel = '%s, %d' % (fontFace, fontSize)
                    fontButton = wxButtons.GenButton(tabPanel, wx.ID_ANY, label=fontLabel)
                    fontButton.SetUseFocusIndicator(False)
                    fontButton.SetFont(font)
                    self.Bind(wx.EVT_BUTTON, self.OnButtonFont, fontButton)
                else:
                    fontButton = None
                if fontFore is not None:
                    #~ foreButton = wx.StaticText(tabPanel, wx.ID_ANY, size=(50, 20))
                    #~ foreButton.SetBackgroundColour(wx.Colour(*fontFore))
                    #~ foreButton.SetCursor(wx.StockCursor(wx.CURSOR_HAND))
                    #~ foreButton.Bind(wx.EVT_LEFT_UP, self.OnButtonColor)
                    foreButton = wxp.ColourSelect(tabPanel, wx.ID_ANY, colour=wx.Colour(*fontFore), size=(50,23), colour_data=self.colour_data)
                else:
                    foreButton = None
                if fontBack is not None:
                    #~ backButton = wx.StaticText(tabPanel, wx.ID_ANY, size=(50, 20))
                    #~ backButton.SetBackgroundColour(wx.Colour(*fontBack))
                    #~ backButton.SetCursor(wx.StockCursor(wx.CURSOR_HAND))
                    #~ backButton.Bind(wx.EVT_LEFT_UP, self.OnButtonColor)
                    backButton = wxp.ColourSelect(tabPanel, wx.ID_ANY, colour=wx.Colour(*fontBack), size=(50,23), colour_data=self.colour_data)
                else:
                    backButton = None
                sizer.Add(staticText, flag=wx.ALIGN_CENTER)
                if fontButton is not None:
                    sizer.Add(fontButton, flag=wx.ALIGN_CENTER)
                else:
                    sizer.Add((0,0), flag=wx.ALIGN_CENTER)
                if foreButton is not None:
                    sizer.Add(foreButton, flag=wx.ALIGN_CENTER)
                else:
                    sizer.Add((0,0), flag=wx.ALIGN_CENTER)
                if backButton is not None:
                    sizer.Add(backButton, flag=wx.ALIGN_CENTER)
                else:
                    sizer.Add((0,0), flag=wx.ALIGN_CENTER)
                self.controls[key] = (fontButton, foreButton, backButton)
            tabSizer = wx.BoxSizer(wx.VERTICAL)
            tabSizer.Add(sizer, 0, wx.ALL, 10)
            tabPanel.SetSizerAndFit(tabSizer)
        self.notebook.SetSelection(0)
        # Standard (and not standard) buttons
        themes = [_('Select a predefined theme')] + parent.defaulttextstylesDict.keys()
        theme_choice = wx.Choice(self, choices=themes)
        theme_choice.SetSelection(0)
        self.Bind(wx.EVT_CHOICE, self.OnSelectTheme, theme_choice)
        only_colors_checkbox = wx.CheckBox(self, wx.ID_ANY, _('Only change colours'))
        only_colors_checkbox.SetValue(parent.options['theme_set_only_colors'])
        only_colors_checkbox.SetToolTipString(_("When selecting a theme, don't change current fonts"))
        self.controls2['theme_set_only_colors'] = only_colors_checkbox
        okay  = wx.Button(self, wx.ID_OK, _('OK'))
        self.Bind(wx.EVT_BUTTON, self.OnButtonOK, okay)
        cancel = wx.Button(self, wx.ID_CANCEL, _('Cancel'))
        btns = wx.StdDialogButtonSizer()
        if extra: # single CheckBox
            label, optKey, tip = extra
            checkbox = wx.CheckBox(self, wx.ID_ANY, label)
            checkbox.SetValue(parent.options[optKey])
            checkbox.SetToolTipString(tip)
            self.controls2[optKey] = checkbox
            btns.Add(checkbox, 0, wx.LEFT | wx.RIGHT | wx.ALIGN_CENTER_VERTICAL, 3)
        btns.Add(theme_choice, 0, wx.LEFT | wx.RIGHT, 3)
        btns.Add(only_colors_checkbox, 0, wx.LEFT | wx.RIGHT | wx.ALIGN_CENTER_VERTICAL, 3)
        btns.AddButton(okay)
        btns.AddButton(cancel)
        btns.Realize()
        # Size the elements
        dlgSizer = wx.BoxSizer(wx.VERTICAL)
        #~ dlgSizer.Add(sizer, 0, wx.EXPAND|wx.ALL, 5)
        dlgSizer.Add(self.notebook, 0, wx.EXPAND|wx.ALL, 5)
        dlgSizer.Add(btns, 0, wx.EXPAND|wx.ALL, 10)
        self.SetSizer(dlgSizer)
        dlgSizer.Fit(self)
        self.sizer = dlgSizer
        # Misc
        okay.SetDefault()
        self.Centre(wx.CENTRE_ON_SCREEN)

    @staticmethod
    def ParseStyleInfo(styleInfo):
        # Get the style info (face, size, bold/italic/underline, color, background)
        (fontSize, fontStyle, fontWeight, fontUnderline,
        fontFace, fontFore, fontBack) = (10, wx.FONTSTYLE_NORMAL,
        wx.FONTWEIGHT_NORMAL, False, None, None, None)
        for info in styleInfo:
            infolower = info.lower().strip()
            if infolower.startswith('face:'):
                fontFace = info[5:]
            elif infolower.startswith('size:'):
                fontSize = int(info[5:])
            elif infolower.startswith('fore:'):
                color = info.split(':')[1].strip().lstrip('#')
                r = int(color[0:2], 16)
                g = int(color[2:4], 16)
                b = int(color[4:6], 16)
                fontFore = (r, g, b)
            elif infolower.startswith('back:'):
                color = info.split(':')[1].strip().lstrip('#')
                r = int(color[0:2], 16)
                g = int(color[2:4], 16)
                b = int(color[4:6], 16)
                fontBack = (r, g, b)
            elif infolower =='bold':
                fontWeight = wx.FONTWEIGHT_BOLD
            elif infolower =='italic':
                fontStyle = wx.FONTSTYLE_ITALIC
            elif infolower =='underline':
                fontUnderline = True
        return (fontSize, fontStyle, fontWeight, fontUnderline,
                fontFace, fontFore, fontBack)

    def OnSelectTheme(self, event):
        theme = event.GetEventObject().GetStringSelection()
        if theme != _('Select a predefined theme'):
            return self.SetTheme(theme, only_colors=
                            self.controls2['theme_set_only_colors'].GetValue())

    def SetTheme(self, theme, only_colors=False):
        for tabLabel, tabInfo in self.dlgInfo:
            for label, key in tabInfo:
                fontButton, foreButton, backButton = self.controls[key]
                (fontSize, fontStyle, fontWeight, fontUnderline,
                fontFace, fontFore, fontBack) = self.ParseStyleInfo(self.defaults[theme][key].split(','))
                if not only_colors and fontButton is not None and fontFace is not None:
                    font = wx.Font(fontSize, wx.FONTFAMILY_DEFAULT, fontStyle,
                                   fontWeight, fontUnderline, faceName=fontFace)
                    fontButton.SetLabel('%s, %d' % (fontFace, fontSize))
                    fontButton.SetFont(font)
                    fontButton.SetBestSize()
                    fontButton.Refresh()
                if foreButton is not None and fontFore is not None:
                    foreButton.SetColour(wx.Colour(*fontFore))
                if backButton is not None and fontBack is not None:
                    backButton.SetColour(wx.Colour(*fontBack))
            self.sizer.Fit(self)

    def OnButtonOK(self, event):
        if self.UpdateDict():
            event.Skip()

    def OnButtonFont(self, event):
        button = event.GetEventObject()
        font = button.GetFont()
        # Show the font dialog
        data = wx.FontData()
        data.EnableEffects(False)
        data.SetInitialFont(font)
        dlg = wx.FontDialog(self, data)
        if dlg.ShowModal() == wx.ID_OK:
            data = dlg.GetFontData()
            font = data.GetChosenFont()
            fontFace = font.GetFaceName()
            fontSize = font.GetPointSize()
            fontLabel = '%s, %d' % (fontFace, fontSize)
            button.SetLabel(fontLabel)
        button.SetFont(font)
        button.SetBestSize()
        button.Refresh()
        self.sizer.Fit(self)
        dlg.Destroy()

    def GetDict(self):
        return self.options

    def GetDict2(self):
        for key in self.controls2:
            self.controls2[key] = self.controls2[key].GetValue()
        return self.controls2

    def UpdateDict(self):
        for key, value in self.controls.items():
            styleList = []
            fontButton, foreButton, backButton = value
            if fontButton is not None:
                font = fontButton.GetFont()
                styleList.append('face:%s' % font.GetFaceName())
                styleList.append('size:%i' % font.GetPointSize())
            if foreButton is not None:
                #~ styleList.append('fore:#%02x%02x%02x' % foreButton.GetBackgroundColour().Get())
                styleList.append('fore:#%02x%02x%02x' % foreButton.GetColour().Get())
            if backButton is not None:
                #~ styleList.append('back:#%02x%02x%02x' % backButton.GetBackgroundColour().Get())
                styleList.append('back:#%02x%02x%02x' % backButton.GetColour().Get())
            if fontButton is not None:
                if font.GetWeight() == wx.FONTWEIGHT_BOLD:
                    styleList.append('bold')
                if font.GetStyle() == wx.FONTSTYLE_ITALIC:
                    styleList.append('italic')
                if font.GetUnderlined():
                    styleList.append('underlined')
            stylestring = ','.join(styleList)
            self.options[key] = stylestring
        return True