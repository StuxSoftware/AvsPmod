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
import sys

import wx
from wx import stc

from avsp2.i18nutils import _


class ScrapWindow(wx.Dialog):
    """
    Dialog for scrap window.
    """

    def __init__(self, parent, title=_('Scrap Window'), pos=wx.DefaultPosition, size=(250,250)):
        style = wx.DEFAULT_DIALOG_STYLE | wx.RESIZE_BORDER
        wx.Dialog.__init__(self, parent, wx.ID_ANY, title, pos, size, style=style)
        self.parent = parent
        # Create the stc control
        self.textCtrl = self.createTextCtrl()
        self.Style()
        self.textCtrl.nInserted = 0
        # Define keyboard shortcuts
        #~ self.BindShortcuts()
        # Add the text from the previous session
        txt, anchor, pos = self.parent.options['scraptext']
        self.textCtrl.SetText(txt)
        self.textCtrl.SetAnchor(anchor)
        self.textCtrl.SetCurrentPos(pos)
        self.textCtrl.EnsureCaretVisible()
        self.textCtrl.EmptyUndoBuffer()
        # Set the width for the horizontal scrollbar
        maxWidth = 50
        if wx.VERSION > (2, 9):
            self.textCtrl.SetScrollWidth(maxWidth)
            self.textCtrl.SetScrollWidthTracking(True)
        else:
            for line in txt.split('\n'):
                width = self.textCtrl.TextWidth(stc.STC_STYLE_DEFAULT, line)
                if width > maxWidth:
                    maxWidth = width
            self.textCtrl.SetScrollWidth(maxWidth)
        # Event binding
        self.Bind(wx.EVT_CLOSE, self.OnClose)
        # Misc
        sizer = wx.BoxSizer()
        sizer.Add(self.textCtrl, 1, wx.EXPAND)
        self.SetSizerAndFit(sizer)
        self.neverShown = True

    def createTextCtrl(self):
        textCtrl = stc.StyledTextCtrl(self, wx.ID_ANY, size=(250,250), style=wx.SIMPLE_BORDER)
        # Define the context menu
        textCtrl.UsePopUp(0)
        self.idInsertFrame = wx.NewId()
        self.idGetStatusText = wx.NewId()
        self.idToggleScrapWindow = wx.NewId()
        menuInfo = (
            (_('Undo')+'\tCtrl+Z', lambda event: textCtrl.Undo(), wx.ID_ANY),
            (_('Redo')+'\tCtrl+Y', lambda event: textCtrl.Redo(), wx.ID_ANY),
            (''),
            (_('Cut')+'\tCtrl+X', lambda event: textCtrl.Cut(), wx.ID_ANY),
            (_('Copy')+'\tCtrl+C', lambda event: textCtrl.Copy(), wx.ID_ANY),
            (_('Paste')+'\tCtrl+V', lambda event: textCtrl.Paste(), wx.ID_ANY),
            (''),
            (_('Select all')+'\tCtrl+A', lambda event: textCtrl.SelectAll(), wx.ID_ANY),
            (''),
            (_('Refresh'), self.OnRefresh, wx.ID_ANY),
            (_('Insert frame #'), self.OnInsertFrameNumber, self.idInsertFrame),
            (_('Save to file...'), self.OnSave, wx.ID_SAVE),
            (_('Clear all'), self.OnClearAll, wx.ID_ANY),
            (_('Toggle scrap window'), self.OnToggleScrapWindow, self.idToggleScrapWindow),
        )
        self.contextMenu = menu = wx.Menu()
        for eachMenuInfo in menuInfo:
            # Define optional arguments
            if not eachMenuInfo:
                menu.AppendSeparator()
            else:
                label = eachMenuInfo[0]
                handler = eachMenuInfo[1]
                status = ''
                id = eachMenuInfo[2]
                menuItem = menu.Append(id, label, status)
                textCtrl.Bind(wx.EVT_MENU, handler, menuItem)
        textCtrl.contextMenu = menu
        textCtrl.Bind(wx.EVT_CONTEXT_MENU, self.OnContextMenu)
        # Misc properties
        textCtrl.SetMarginWidth(1, 0)
        textCtrl.SetEOLMode(stc.STC_EOL_LF)
        return textCtrl

    def Style(self):
        textstyles = self.parent.options['textstyles']
        # Define the default style
        self.textCtrl.StyleSetSpec(stc.STC_STYLE_DEFAULT, textstyles['scrapwindow'])
        self.textCtrl.StyleClearAll()
        # Set a style to use for text flashing upon insertion
        self.textCtrl.StyleSetSpec(stc.STC_P_WORD, "fore:#FF0000,bold")
        # Set a style for selected text
        self.textCtrl.SetCaretForeground(textstyles['cursor'].split(':')[1])
        for elem in textstyles['highlight'].split(','):
            if elem.startswith('fore:'):
                if self.parent.options['highlight_fore']:
                    self.textCtrl.SetSelForeground(True, elem.split(':')[1].strip())
                else:
                    self.textCtrl.SetSelForeground(False, wx.WHITE)
            elif elem.startswith('back:'):
                self.textCtrl.SetSelBackground(True, elem.split(':')[1].strip())

    def BindShortcuts(self):
        menuInfo = (
            (_('Insert frame #'), self.idInsertFrame),
            (_('Save script'), wx.ID_SAVE),
            (_('Toggle scrap window'), self.idToggleScrapWindow),
        )
        menu = self.contextMenu
        counter = 0
        accList = []
        for itemName, shortcut, id in self.parent.options['shortcuts']:
            for label, id in menuInfo:
                if itemName.endswith(label):
                    counter += 1
                    accel = wx.GetAccelFromString('\t'+shortcut)
                    if accel and accel.IsOk():
                        accList.append((accel.GetFlags(), accel.GetKeyCode(), id))
                    menuItem = menu.FindItemById(id)
                    label = '%s\t%s' % (menuItem.GetItemLabelText(), shortcut)
                    menuItem.SetItemLabel(label)
                    break
            if counter == len(menuInfo):
                break
        accTable = wx.AcceleratorTable(accList)
        self.textCtrl.SetAcceleratorTable(accTable)

    def OnClose(self, event):
        self.Hide()

    def OnContextMenu(self, event):
        win = event.GetEventObject()
        pos = win.ScreenToClient(event.GetPosition())
        try:
            win.PopupMenu(win.contextMenu, pos)
        except AttributeError:
            print>>sys.stderr, _('Error: no contextMenu variable defined for window')

    def OnRefresh(self, event):
        scrap = self.textCtrl
        scrap.StartStyling(0, 31)
        scrap.SetStyling(scrap.GetTextLength(), stc.STC_STYLE_DEFAULT)
        self.Refresh()

    def OnInsertFrameNumber(self, event):
        frame = self.parent.GetFrameNumber()
        self.textCtrl.ReplaceSelection(str(frame))

    def OnSave(self, event):
        filefilter = (_('Text document') + ' (*.txt)|*.txt|' +
                      _('All files') + ' (*.*)|*.*')
        initialdir = self.parent.GetProposedPath(only='dir')
        dlg = wx.FileDialog(self,_('Save scrap text'),
            initialdir, '', filefilter, wx.SAVE | wx.OVERWRITE_PROMPT)
        ID = dlg.ShowModal()
        if ID == wx.ID_OK:
            filename = dlg.GetPath()
            self.textCtrl.SaveFile(filename)
            self.parent.options['recentdir'] = os.path.dirname(filename)
        dlg.Destroy()

    def OnClearAll(self, event):
        self.textCtrl.ClearAll()

    def OnToggleScrapWindow(self, event):
        self.Hide()

    def GetText(self):
        return self.textCtrl.GetText()

    def SetText(self, txt):
        return self.textCtrl.SetText(txt)

    def Show(self):
        if self.neverShown:
            xp, yp = self.parent.GetPositionTuple()
            wp, hp = self.parent.GetSizeTuple()
            wd, hd = wx.ScreenDC().GetSizeTuple()
            ws, hs = self.GetSizeTuple()
            self.SetPosition((min(xp+wp-50, wd-ws),-1))
        super(ScrapWindow, self).Show()
        if self.neverShown:
            self.Refresh()
            self.neverShown = False

    def write(self, msg):
        self.parent.MacroWriteToScrap(msg)
