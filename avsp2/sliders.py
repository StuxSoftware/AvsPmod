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
import sys

import wx

from avsp2.i18nutils import _


class UserSliderValidator(wx.PyValidator):
    """
    Dialog and validator for defining user slider
    """
    def __init__(self, ctrlDict, labels):
        wx.PyValidator.__init__(self)
        self.ctrlDict = ctrlDict
        self.labels = labels

    def Clone(self):
        return UserSliderValidator(self.ctrlDict, self.labels)

    def Validate(self, parent):
        textCtrl = self.GetWindow()
        text = textCtrl.GetValue()
        if len(text) == 0:
            self.ShowWarning(textCtrl, _('This field must contain a value!'))
            return False
        elif textCtrl == self.ctrlDict['label']:
            try:
                temp  = str(text)
            except UnicodeEncodeError:
                temp = text
            if temp in self.labels:
                self.ShowWarning(textCtrl, _('This slider label already exists!'))
                return False
            if self.getModFromLabel(text) == -1:
                self.ShowWarning(textCtrl, _('Invalid slider label modulo syntax!'))
                return False
            return True
        else:
            try:
                float(text)
            except ValueError:
                self.ShowWarning(textCtrl, _('This field must contain a number!'))
                return False
            try:
                minValue = float(self.ctrlDict['min'].GetValue())
                maxValue = float(self.ctrlDict['max'].GetValue())
                value = float(self.ctrlDict['val'].GetValue())
                # Validate ranges
                if minValue >= maxValue and textCtrl == self.ctrlDict['min']:
                    self.ShowWarning(textCtrl, _('The min value must be less than the max!'))
                    return False
                if value < minValue or value > maxValue and textCtrl == self.ctrlDict['val']:
                    self.ShowWarning(textCtrl, _('The initial value must be between the min and the max!'))
                    return False
                # Validate modulo divisibility
                mod = self.getModFromLabel(self.ctrlDict['label'].GetValue())
                if mod == -1:
                    self.ShowWarning(textCtrl, _('Invalid slider label modulo syntax!'))
                    return False
                if mod is not None:
                    if int(minValue) % mod != 0 and textCtrl == self.ctrlDict['min']:
                        self.ShowWarning(textCtrl, _('The min value must be a multiple of %(mod)s!') % locals())
                        return False
                    if int(maxValue) % mod != 0 and textCtrl == self.ctrlDict['max']:
                        self.ShowWarning(textCtrl, _('The max value must be a multiple of %(mod)s!') % locals())
                        return False
                    if int(value) % mod != 0 and textCtrl == self.ctrlDict['val']:
                        self.ShowWarning(textCtrl, _('The initial value must be a multiple of %(mod)s!') % locals())
                        return False
                    if mod > (maxValue - minValue):
                        self.ShowWarning(self.ctrlDict['min'], _('The difference between the min and max must be greater than %(mod)s!') % locals())
                        return False
            except ValueError:
                pass
            return True

    def getModFromLabel(self, label):
        mod = None
        label = self.ctrlDict['label'].GetValue()
        splitlabel = label.split('%', 1)
        if len(splitlabel) == 2:
            try:
                mod = int(splitlabel[1])
                if mod <= 0:
                    mod = -1
            except ValueError:
                mod = -1
        return mod

    def ShowWarning(self, textCtrl, message):
        color = textCtrl.GetBackgroundColour()
        textCtrl.SetBackgroundColour('pink')
        textCtrl.Refresh()
        wx.MessageBox(message, _('Error'), style=wx.OK|wx.ICON_ERROR)
        textCtrl.SetBackgroundColour(color)
        textCtrl.SetSelection(-1,-1)
        textCtrl.SetFocus()
        textCtrl.Refresh()

    def TransferToWindow(self):
        return True

    def TransferFromWindow(self):
        return True

class UserSliderDialog(wx.Dialog):
    def __init__(self, parent, labels, initialValueText=''):
        wx.Dialog.__init__(self, None, wx.ID_ANY, _('Define user slider'))
        self.parent = parent
        # Entry fields
        gridSizer = wx.FlexGridSizer(cols=2, hgap=10, vgap=5)
        gridSizer.AddGrowableCol(1)
        self.ctrlDict = {}
        for eachKey, eachLabel in self.fieldInfo():
            textCtrl = wx.TextCtrl(self, validator=UserSliderValidator(self.ctrlDict, labels))
            staticText = wx.StaticText(self, wx.ID_ANY, eachLabel)
            gridSizer.Add(staticText, 0, wx.ALIGN_RIGHT|wx.ALIGN_CENTER_VERTICAL)
            gridSizer.Add(textCtrl, 0, wx.EXPAND)
            self.ctrlDict[eachKey] = textCtrl
        if initialValueText:
            self.ctrlDict['val'].SetValue(initialValueText)
        # Standard buttons
        okay  = wx.Button(self, wx.ID_OK, _('OK'))
        okay.SetDefault()
        cancel = wx.Button(self, wx.ID_CANCEL, _('Cancel'))
        btns = wx.StdDialogButtonSizer()
        btns.AddButton(okay)
        btns.AddButton(cancel)
        btns.Realize()
        # Set the sizer
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add(gridSizer, 0, wx.EXPAND|wx.ALL, 20)
        sizer.Add(btns, 0, wx.EXPAND|wx.ALL, 5)
        self.SetSizer(sizer)
        sizer.Fit(self)

    def fieldInfo(self):
        return (
            ('label', _('Slider label:')),
            ('min', _('Min value:')),
            ('max', _('Max value:')),
            ('val', _('Initial value:')),
        )

    def GetSliderText(self):
        textDict = dict([(k, v.GetValue()) for k,v in self.ctrlDict.items()])
        textDict['open'] = self.parent.sliderOpenString
        textDict['close'] = self.parent.sliderCloseString
        return '%(open)s"%(label)s", %(min)s, %(max)s, %(val)s%(close)s' % textDict


class SliderPlus(wx.Panel):
    """
    Custom slider
    """
    def __init__(self, parent, app, id, value=0, minValue=0, maxValue=100, size=(-1, 28), big=False, bookmarkDict={}):
        self.big = big
        if self.big:
            size = size[0], size[1] + 16
        wx.Panel.__init__(self, parent, id, size=size, style=wx.WANTS_CHARS)
        self.bookmarkDict = bookmarkDict
        self.parent = parent
        self.app = app
        self.minValue = minValue
        self.maxValue = maxValue
        self.value = max(min(value, self.maxValue), self.minValue)
        self.bookmarks = {}
        self.mouse_wheel_rotation = 0
        # Internal display variables
        self.isclicked = False
        self.xdelta = None
        self.xo = 15
        self.yo = 5
        self.yo2 = 10
        self.wT = 22
        self.wH = 10
        if self.big:
            self.xo += 8
            self.yo += 4
            self.yo2 += 4
            self.wT += 8
            self.wH += 4
        self.selections = None
        self.selmode = 0
        self._DefineBrushes()
        # Event binding
        self.Bind(wx.EVT_PAINT, self._OnPaint)
        self.Bind(wx.EVT_SIZE, self._OnSize)
        self.Bind(wx.EVT_LEFT_DOWN, self._OnLeftDown)
        self.Bind(wx.EVT_MOTION, self._OnMouseMotion)
        self.Bind(wx.EVT_LEFT_UP, self._OnLeftUp)
        self.Bind(wx.EVT_MOUSEWHEEL, self._OnMouseWheel)
        self.Bind(wx.EVT_KEY_DOWN, self._OnKeyDown)
        def OnSetFocus(event):
            if not self.HasCapture():
                try:
                    event.GetWindow().SetFocus()
                except AttributeError:
                    event.Skip()
        self.Bind(wx.EVT_SET_FOCUS, OnSetFocus)

    def _DefineBrushes(self):
        #~ colorBackground = self.parent.GetBackgroundColour()
        colorBackground = self.GetBackgroundColour()
        colorHighlight = wx.SystemSettings.GetColour(wx.SYS_COLOUR_3DLIGHT)
        colorHighlight2 = wx.SystemSettings.GetColour(wx.SYS_COLOUR_3DHILIGHT)
        colorShadow = wx.SystemSettings.GetColour(wx.SYS_COLOUR_3DSHADOW)
        colorDarkShadow = wx.SystemSettings.GetColour(wx.SYS_COLOUR_3DDKSHADOW)
        colorWindow = colorHighlight2#wx.SystemSettings.GetColour(wx.SYS_COLOUR_WINDOW)
        #~ colorHandle = wx.SystemSettings.GetColour(wx.SYS_COLOUR_MENU)
        colorHandle = wx.SystemSettings.GetColour(wx.SYS_COLOUR_BTNFACE)
        r,g,b = colorHandle.Red(), colorHandle.Green(), colorHandle.Blue()
        #~ colorHandle2 = wx.Colour(min(r+30, 255),min(g+30, 255),min(b+30, 255))#wx.SystemSettings.GetColour(wx.SYS_COLOUR_SCROLLBAR)
        colorHandle2 = wx.SystemSettings.GetColour(wx.SYS_COLOUR_BTNHIGHLIGHT)
        colorGrayText = wx.SystemSettings.GetColour(wx.SYS_COLOUR_GRAYTEXT)
        self.penWindowBackground = wx.Pen(colorBackground)
        self.brushWindowBackground = wx.Brush(colorBackground)
        self.penBackground = wx.Pen(colorWindow)
        self.brushBackground = wx.Brush(colorWindow)
        self.penShadow = wx.Pen(colorShadow)
        self.penDarkShadow = wx.Pen(colorDarkShadow)
        self.penHighlight = wx.Pen(colorHighlight)
        self.penHighlight2 = wx.Pen(colorHighlight2)
        self.penHandle = wx.Pen(colorHandle)
        self.brushHandle = wx.Brush(colorHandle)
        self.penHandle2 = wx.Pen(colorHandle2)
        self.brushHandle2 = wx.Brush(colorHandle2)
        self.penGrayText = wx.Pen(colorGrayText)
        self.brushGrayText = wx.Brush(colorGrayText)

    def _OnLeftDown(self, event):
        self.app.lastshownframe = self.app.paintedframe
        mousepos = event.GetPosition()
        x, y, w, h = self.GetRect()
        #~ pixelpos = int(self.value * (w-2*self.xo) / float(self.maxValue - self.minValue))
        #~ rectHandle = wx.Rect(pixelpos-self.wH/2+self.xo, self.yo-3, self.wH, h-self.yo-self.yo2+6)
        rectHandle = self._getRectHandle()
        rectBox = wx.Rect(0, 0+self.yo, w, h-self.yo-self.yo2)
        if rectHandle.Inside(mousepos):
            self.isclicked = True
            self.xdelta = mousepos.x - rectHandle.x
            self.CaptureMouse()
            if self.IsDoubleBuffered():
                dc = wx.ClientDC(self)
            else:
                dc = wx.BufferedDC(wx.ClientDC(self))
            dc.Clear()
            self._PaintSlider(dc)
        elif self.selmode == 1 and self._HitTestHandleDeadZone(mousepos):
            pass
        elif rectBox.Inside(mousepos):
            self.isclicked = True
            self.CaptureMouse()
            oldvalue = self.value
            #~ self.SetValue(int(round((mousepos.x-self.xo+self.wH/2) * (self.maxValue - self.minValue) / float(w-2*self.xo))))
            self.SetValue(int(round((mousepos.x-self.xo) * (self.maxValue - self.minValue) / float(w-2*self.xo))))
            if self.value != oldvalue:
                self._SendScrollEvent()
            rectHandle = self._getRectHandle()
            self.xdelta = mousepos.x - rectHandle.x
        event.Skip()

    def _OnMouseMotion(self, event):
        if event.Dragging() and event.LeftIsDown() and self.HasCapture():
            x, y, w, h = self.GetRect()
            xmouse, ymouse = event.GetPosition()
            oldvalue = self.value
            #~ self.value = int(round((xmouse-self.xdelta-self.xo+self.wH/2) * (self.maxValue - self.minValue) / float(w-2*self.xo)))
            #~ self.value = max(min(self.value, self.maxValue), self.minValue)
            self.SetValue(int(round((xmouse-self.xdelta-self.xo+self.wH/2) * (self.maxValue - self.minValue) / float(w-2*self.xo))))
            if self.value != oldvalue:
                self._SendScrollEvent()
            #~ dc = wx.BufferedDC(wx.ClientDC(self))
            #~ dc.Clear()
            #~ self._PaintSlider(dc)

    def _OnLeftUp(self, event):
        self.isclicked = False
        self.xdelta = None
        if self.HasCapture():
            self.ReleaseMouse()
            self.adjust_handle = True
            self._SendScrollEndEvent()
            # Done in ShowVideoFrame by calling SetValue
            #~if self.IsDoubleBuffered():
            #~    dc = wx.ClientDC(self)
            #~else:
            #~    dc = wx.BufferedDC(wx.ClientDC(self))
            #~dc.Clear()
            #~self._PaintSlider(dc)
        else:
            # If clicked on a bookmark, go to that frame
            mousepos = event.GetPosition()
            index = self.HitTestBookmark(mousepos)
            if index is not None:
                self.SetValue(index)
                self.adjust_handle = False
                self._SendScrollEndEvent()
            #~ # If clicked on a selection button, create the selection bookmark
            #~ bmtype = self.HitTestSelectionButton(mousepos)
            #~ if bmtype is not None:
                #~ if self.bookmarks.count((self.value, bmtype)) == 0:
                    #~ self.SetBookmark(self.value, bmtype)
                #~ else:
                    #~ self.RemoveBookmark(self.value, bmtype)
        event.Skip()

    def _OnMouseWheel(self, event):
        #~ if event.LeftIsDown():
        if not self.HasCapture():
            rotation = event.GetWheelRotation()
            if self.mouse_wheel_rotation * rotation < 0:
                self.mouse_wheel_rotation = rotation
            else:
                self.mouse_wheel_rotation += rotation
            if abs(self.mouse_wheel_rotation) >= event.GetWheelDelta():
                delta = -1 if self.mouse_wheel_rotation > 0 else 1
                if self.app.options['invertscrolling']: delta = -delta
                self.mouse_wheel_rotation = 0
                oldvalue = self.value
                self.SetValue(self.value + delta)
                if self.value != oldvalue:
                    self._SendScrollEvent()

    def _OnKeyDown(self, event):
        if self.HasCapture():
            key = event.GetKeyCode()
            oldvalue = self.value
            if key in (wx.WXK_LEFT, wx.WXK_UP):
                self.SetValue(self.value-1)
            elif key in (wx.WXK_RIGHT, wx.WXK_DOWN):
                self.SetValue(self.value+1)
            if self.value != oldvalue:
                self._SendScrollEvent()

    def _SendScrollEvent(self):
        event = wx.CommandEvent(wx.wxEVT_SCROLL_THUMBTRACK, self.GetId())
        event.SetEventObject(self)
        self.GetEventHandler().ProcessEvent(event)

    def _SendScrollEndEvent(self):
        event = wx.CommandEvent(wx.wxEVT_SCROLL_ENDSCROLL, self.GetId())
        event.SetEventObject(self)
        self.GetEventHandler().ProcessEvent(event)

    def _OnSize(self, event):
        if self.IsDoubleBuffered():
            dc = wx.ClientDC(self)
        else:
            dc = wx.BufferedDC(wx.ClientDC(self))
        dc.Clear()
        self._PaintSlider(dc)

    def _OnPaint(self, event):
        # Color info
        self._DefineBrushes()
        dc = wx.PaintDC(self)
        #~ dc = wx.BufferedPaintDC(self)
        self._PaintSlider(dc)

    def _PaintSlider(self, dc):
        boolEnabled = self.IsEnabled()
        # Paint the bar
        x, y = (0, 0)
        w, h = self.GetSize()
        xB, yB, wB, hB = self.xo, self.yo, w-2*self.xo, h-self.yo-self.yo2
        xH, yH, wH, hH = -1, self.yo-3, self.wH, hB+6
        # First paint background
        dc.SetPen(self.penWindowBackground)
        dc.SetBrush(self.brushWindowBackground)
        dc.DrawRectangle(0, 0, w, h)
        dc.SetPen(self.penBackground)
        dc.SetBrush(self.brushBackground)
        dc.DrawRectangle(xB, yB, wB, hB)
        # Then paint the bookmark selections
        if self.selections is not None:
            if boolEnabled:
                dc.SetPen(wx.Pen(wx.BLUE))
                dc.SetBrush(wx.BLUE_BRUSH)
            else:
                color = wx.Colour(200,200,230)
                dc.SetPen(wx.Pen(color))
                dc.SetBrush(wx.Brush(color))
            for start, stop in self.selections:
                start = min(max(start, self.minValue), self.maxValue)
                stop = min(max(stop, self.minValue), self.maxValue)
                pixelstart = int(start * wB / float(self.maxValue - self.minValue)) + self.xo
                pixelstop = int(stop * wB / float(self.maxValue - self.minValue)) + self.xo
                dc.DrawRectangle(pixelstart, yB, pixelstop - pixelstart, hB)
        # Then draw the bookmark triangles
        dc.SetPen(self.penWindowBackground)
        if boolEnabled:
            dc.SetBrush(wx.BLACK_BRUSH)
        else:
            dc.SetBrush(self.brushGrayText)
        wT = self.wT
        drawnBookmarks = dict()
        for value, bmtype in self.bookmarks.items():
            if value > self.maxValue or value < self.minValue:
                continue
            pixelpos = int(value * wB / float(self.maxValue - self.minValue)) + self.xo
            try:
                if drawnBookmarks[pixelpos] == bmtype:
                    continue
            except KeyError:
                pass
            drawnBookmarks[pixelpos] = bmtype

            p1 = wx.Point(pixelpos, h-wT/2)
            if bmtype == 0:
                if value in self.bookmarkDict:
                    dc.SetBrush(wx.BLUE_BRUSH)
                else:
                    dc.SetBrush(wx.BLACK_BRUSH)
                p2 = wx.Point(pixelpos-wT/4, h)
                p3 = wx.Point(pixelpos+wT/4, h)
                dc.DrawPolygon((p1, p2, p3))
            elif bmtype == 1:
                p2 = wx.Point(pixelpos-wT/2, h)
                p3 = wx.Point(pixelpos, h)
                dc.DrawPolygon((p1, p2, p3))
                dc.SetPen(wx.BLACK_PEN)
                dc.DrawLine(pixelpos, h-1, pixelpos+wT/4, h-1)
                dc.SetPen(self.penWindowBackground)
            elif bmtype == 2:
                p2 = wx.Point(pixelpos, h)
                p3 = wx.Point(pixelpos+wT/2, h)
                dc.DrawPolygon((p1, p2, p3))
                dc.SetPen(wx.BLACK_PEN)
                dc.DrawLine(pixelpos, h-1, pixelpos-wT/4, h-1)
                dc.SetPen(self.penWindowBackground)
        # Then paint the border
        dc.SetPen(self.penShadow)
        dc.DrawLine(xB, yB, xB+wB, yB)
        dc.DrawLine(xB, yB, xB, yB+hB)
        dc.SetPen(self.penDarkShadow)
        dc.DrawLine(xB+1, yB+1, xB+wB, yB+1)
        dc.DrawLine(xB+1, yB+1, xB+1, yB+hB)
        dc.SetPen(self.penHighlight2)
        dc.DrawLine(xB+wB, yB, xB+wB, yB+hB)
        dc.DrawLine(xB, yB+hB, xB+wB+1, yB+hB)
        dc.SetPen(self.penHighlight)
        dc.DrawLine(xB+wB-1, yB+1, xB+wB-1, yB+hB)
        dc.DrawLine(xB+1, yB+hB-1, xB+wB, yB+hB-1)
        # Then paint the handle
        pixelpos = int(self.value * wB / float(self.maxValue - self.minValue)) + self.xo
        pixelpos0 = pixelpos - self.wH/2
        if self.isclicked or not boolEnabled:
            dc.SetPen(self.penHandle2)
            dc.SetBrush(self.brushHandle2)
        else:
            dc.SetPen(self.penHandle)
            dc.SetBrush(self.brushHandle)
        dc.DrawRectangle(pixelpos0, yH, wH, hH)
        dc.SetPen(self.penHighlight2)
        dc.DrawLine(pixelpos0, yH, pixelpos0+wH, yH)
        dc.DrawLine(pixelpos0, yH, pixelpos0, yH+hH)
        dc.SetPen(self.penDarkShadow)
        dc.DrawLine(pixelpos0+wH, yH, pixelpos0+wH, yH+hH)
        dc.DrawLine(pixelpos0, yH+hH, pixelpos0+wH+1, yH+hH)
        dc.SetPen(self.penShadow)
        dc.DrawLine(pixelpos0+wH-1, yH+1, pixelpos0+wH-1, yH+hH)
        dc.DrawLine(pixelpos0+1, yH+hH-1, pixelpos0+wH, yH+hH-1)
        if self.selmode == 1:
            hH2 = hH/2
            border = 3
            yH2 = yB #yH + hH/4
            for bmtype in (1,2):
                if bmtype == 1:
                    xpos = pixelpos0 - self.wH
                    p1 = wx.Point(xpos+border, yH2+hH2-border)
                    p2 = wx.Point(xpos+self.wH-border, yH2+hH2-border)
                    p3 = wx.Point(xpos+self.wH-border, yH2+border)
                else:
                    xpos = pixelpos0 + self.wH #+ 1
                    p1 = wx.Point(xpos+border, yH2+border)
                    p2 = wx.Point(xpos+border, yH2+hH2-border)
                    p3 = wx.Point(xpos+self.wH-border, yH2+hH2-border)
                # Draw the button
                dc.SetPen(self.penHandle)
                dc.SetBrush(self.brushHandle)
                dc.DrawRectangle(xpos, yH2, self.wH, hH2)
                dc.SetPen(self.penHighlight2)
                dc.DrawLine(xpos, yH2, xpos+wH, yH2)
                dc.DrawLine(xpos, yH2, xpos, yH2+hH2)
                dc.SetPen(self.penDarkShadow)
                if bmtype == 2:
                    dc.DrawLine(xpos+wH, yH2, xpos+wH, yH2+hH2)
                    dc.DrawLine(xpos, yH2+hH2, xpos+wH+1, yH2+hH2)
                else:
                    dc.DrawLine(xpos, yH2+hH2, xpos+wH, yH2+hH2)
                dc.SetPen(self.penShadow)
                dc.DrawLine(xpos+wH-1, yH2+1, xpos+wH-1, yH2+hH2)
                dc.DrawLine(xpos+1, yH2+hH2-1, xpos+wH, yH2+hH2-1)
                # Draw the button image
                if boolEnabled:
                    dc.SetPen(wx.BLACK_PEN)
                    dc.SetBrush(wx.BLACK_BRUSH)
                else:
                    dc.SetPen(self.penGrayText)
                    dc.SetBrush(self.brushGrayText)
                dc.DrawPolygon((p1, p2, p3))


    def _createSelections(self):
        selectionList = []
        start = stop = None
        #~ selectionmarks = self.bookmarks
        selectionmarks = [item for item in self.bookmarks.items() if item[1] != 0]
        selectionmarks.sort()
        if len(selectionmarks) == 0:
            return None
        if selectionmarks[0][1] == 2:
            start =self.minValue
        for value, bmtype in selectionmarks:
            if start is None:
                if bmtype == 1:
                    start = value
            else:
                if bmtype == 2:
                    stop = value
                    selectionList.append((start, stop))
                    start = stop =None
        if start is not None:
            stop = self.maxValue
            selectionList.append((start, stop))
        return selectionList

    def _getRectHandle(self):
        x, y, w, h = self.GetRect()
        pixelpos = int(self.value * (w-2*self.xo) / float(self.maxValue - self.minValue))
        rectHandle = wx.Rect(pixelpos-self.wH/2+self.xo, self.yo-3, self.wH, h-self.yo-self.yo2+6)
        return rectHandle

    def GetValue(self):
        return self.value

    def GetMin(self):
        return self.minValue

    def GetMax(self):
        return self.maxValue

    def SetValue(self, value):
        self.value = max(min(value, self.maxValue), self.minValue)
        if self.IsDoubleBuffered():
            dc = wx.ClientDC(self)
        else:
            dc = wx.BufferedDC(wx.ClientDC(self))
        dc.Clear()
        self._PaintSlider(dc)
        return True

    def SetRange(self, minValue, maxValue, refresh=True):
        if minValue >= maxValue:
            if minValue == 0 and (maxValue == -1 or maxValue ==0):
                maxValue = 1
            else:
                print>>sys.stderr, _('Error: minValue must be less than maxValue')
                return
        self.minValue = minValue
        self.maxValue = maxValue
        self.selections = self._createSelections()
        if refresh:
            if self.IsDoubleBuffered():
                dc = wx.ClientDC(self)
            else:
                dc = wx.BufferedDC(wx.ClientDC(self))
            dc.Clear()
            self._PaintSlider(dc)
        return True

    def SetBookmark(self, value, bmtype=0, refresh=True):
        # Type=0: bookmark, Type=1: selection start, Type=2: selection end
        if bmtype not in (0,1,2):
            return False
        try:
            if self.bookmarks[value] == bmtype:
                return False
        except:
            pass
        self.bookmarks[value] = bmtype

        if refresh:
            if self.bookmarks:
                self.selections = self._createSelections()
            else:
                self.selections = None
            if self.IsDoubleBuffered():
                dc = wx.ClientDC(self)
            else:
                dc = wx.BufferedDC(wx.ClientDC(self))
            dc.Clear()
            self._PaintSlider(dc)
        return True

    def RemoveBookmark(self, value, bmtype=0, refresh=True):
        try:
            del self.bookmarks[value]
            if refresh:
                if self.bookmarks:
                    self.selections = self._createSelections()
                else:
                    self.selections = None
                if self.IsDoubleBuffered():
                    dc = wx.ClientDC(self)
                else:
                    dc = wx.BufferedDC(wx.ClientDC(self))
                dc.Clear()
                self._PaintSlider(dc)
            return True
        except KeyError:
            return False

    def RemoveAllBookmarks(self):
        if self.bookmarks:
            self.bookmarks.clear()
            self.selections = None
            if self.IsDoubleBuffered():
                dc = wx.ClientDC(self)
            else:
                dc = wx.BufferedDC(wx.ClientDC(self))
            dc.Clear()
            self._PaintSlider(dc)
        return True

    def GetBookmarks(self, copy=False):
        if not copy:
            return self.bookmarks
        else:
            return dict(self.bookmarks)

    def GetSelections(self):
        if self.selections:
            return self.selections[:]
        else:
            return self.selections

    def ToggleSelectionMode(self, mode=0):
        if self.selmode == 0 or mode == 1:
            self.selmode = 1
        else:
            self.selmode = 0
        if self.IsDoubleBuffered():
            dc = wx.ClientDC(self)
        else:
            dc = wx.BufferedDC(wx.ClientDC(self))
        dc.Clear()
        self._PaintSlider(dc)

    def HitTestHandle(self, mousepos):
        #~ x, y, w, h = self.GetRect()
        #~ pixelpos = int(self.value * (w-2*self.xo) / float(self.maxValue - self.minValue))
        #~ rectHandle = wx.Rect(pixelpos-self.wH/2+self.xo, self.yo-3, self.wH, h-self.yo-self.yo2+6)
        #~ return rectHandle.Inside(mousepos)
        rectHandle = self._getRectHandle()
        return rectHandle.Inside(mousepos)

    def HitTestBookmark(self, mousepos):
        x, y, w, h = self.GetRect()
        hitlist = []
        wT = self.wT
        for value, bmtype in self.bookmarks.items():
            pixelpos = int(value * (w-2*self.xo) / float(self.maxValue - self.minValue)) + self.xo
            if bmtype == 0:
                rect = wx.Rect(pixelpos-wT/4, h-self.yo2, wT/2, wT/2)
            elif bmtype == 1:
                rect = wx.Rect(pixelpos-wT/2, h-self.yo2, wT/2+wT/4, wT/2)
            elif bmtype == 2:
                rect = wx.Rect(pixelpos-wT/4, h-self.yo2, wT/2+wT/4, wT/2)
            if rect.Inside(mousepos):
                hitlist.append((value, pixelpos))
        if hitlist:
            if len(hitlist) == 1:
                return hitlist[0][0]
            else:
                return min([(abs(pixelpos-mousepos.x), value) for value, pixelpos in hitlist])[1]
        else:
            return None

    def HitTestSelectionButton(self, mousepos):
        if self.selmode == 1:
            x, y, w, h = self.GetRect()
            pixelpos = int(self.value * (w-2*self.xo) / float(self.maxValue - self.minValue))
            rectLeftButton = wx.Rect(pixelpos-self.wH/2+self.xo-self.wH, self.yo-3, self.wH, (h-self.yo-self.yo2+6)/1)
            rectRightButton = wx.Rect(pixelpos-self.wH/2+self.xo+self.wH, self.yo-3, self.wH, (h-self.yo-self.yo2+6)/1)
            bmtype = None
            if rectLeftButton.Inside(mousepos):
                bmtype = 1
            if rectRightButton.Inside(mousepos):
                bmtype = 2
            return bmtype

    def _HitTestHandleDeadZone(self, mousepos):
        rectHandle = self._getRectHandle()
        rectHandle.Inflate(3*self.wH, 0)
        return rectHandle.Inside(mousepos)


class AvsFilterAutoSliderInfo(wx.Dialog):
    """
    Dialog specifically for AviSynth filter auto-slider information.
    """
    def __init__(self, parent, mainFrame, filterName, filterInfo, title=_('Edit filter database')):
        wx.Dialog.__init__(self, parent, wx.ID_ANY, title, style=wx.DEFAULT_DIALOG_STYLE|wx.RESIZE_BORDER)
        self.mainFrame = mainFrame
        self.newFilterInfo = None
        # Filter name label
        filterLabel = wx.StaticText(self, wx.ID_ANY, filterName)
        font = filterLabel.GetFont()
        font.SetPointSize(10)
        font.SetWeight(wx.FONTWEIGHT_BOLD)
        filterLabel.SetFont(font)
        # Arguments
        argWindow = wx.ScrolledWindow(self, wx.ID_ANY, style=wx.TAB_TRAVERSAL)
        argWindow.SetScrollRate(10, 10)
        argSizer = wx.GridBagSizer(hgap=0, vgap=10)
        row = 0
        growable = False
        self.argctrls = []
        for argInfo in self.mainFrame.currentScript.GetFilterCalltipArgInfo(calltip=filterInfo):
            totalInfo, cArgType, cArgName, boolRepeatArg, boolOptionalArg, cArgInfo = argInfo
            argtype, argname, guitype, defaultValue, other = self.mainFrame.ParseCalltipArgInfo(totalInfo)
            #~ if guitype is None or argname is None or argtype not in ('int', 'float', 'bool', 'string'):
            if argname is None or argtype not in ('int', 'float', 'bool', 'string'):
                self.argctrls.append((argtype, argname, None, boolRepeatArg, boolOptionalArg))
            else:
                argLabel = wx.StaticText(argWindow, wx.ID_ANY, '%(argtype)s %(argname)s' % locals())
                argLabel.controls = []
                argSizer.Add(argLabel, (row,0), wx.DefaultSpan, wx.ALIGN_RIGHT|wx.ALIGN_BOTTOM|wx.BOTTOM|wx.RIGHT, 5)
                if argtype in ('int', 'float') and guitype != 'intlist':
                    strDefaultValue = strMinValue = strMaxValue = strMod = ''
                    if other is not None:
                        minValue, maxValue, nDecimal, mod = other
                        if nDecimal is None:
                            nDecimal = 0
                        strTemplate = '%.'+str(nDecimal)+'f'
                        if defaultValue is not None:
                            try:
                                strDefaultValue = strTemplate % defaultValue
                            except TypeError:
                                strDefaultValue = defaultValue
                        if minValue is not None:
                            try:
                                strMinValue = strTemplate % minValue
                            except TypeError:
                                strMinValue = minValue
                        if maxValue is not None:
                            try:
                                strMaxValue = strTemplate % maxValue
                            except TypeError:
                                strMaxValue = maxValue
                        if mod is not None:
                            try:
                                strMod = '%i' % mod
                            except TypeError:
                                strMod = mod
                    elif guitype == 'color':
                        strDefaultValue = '$%s' % defaultValue
                    itemData = (
                        (strDefaultValue, _('Default')),
                        (strMinValue, _('Min value')),
                        (strMaxValue, _('Max value')),
                        (strMod, _('Step size')),
                    )
                    hsizer = wx.BoxSizer(wx.HORIZONTAL)
                    for itemValue, itemName in itemData:
                        itemLabel = wx.StaticText(argWindow, wx.ID_ANY, itemName)
                        itemTextCtrl = wx.TextCtrl(argWindow, wx.ID_ANY, itemValue,size=(75,-1))
                        vsizer = wx.BoxSizer(wx.VERTICAL)
                        vsizer.Add(itemLabel, 0, wx.LEFT, 2)
                        vsizer.Add(itemTextCtrl, 0, wx.ALL, 0)
                        hsizer.Add(vsizer, 0, wx.EXPAND|wx.RIGHT,5)
                        argLabel.controls.append(itemTextCtrl)
                    argSizer.Add(hsizer, (row,1), wx.DefaultSpan, wx.ALIGN_CENTER_VERTICAL|wx.RIGHT, 0)
                elif argtype == 'bool':
                    strDefaultValue = ''
                    if defaultValue is not None:
                        if defaultValue.lower() == 'true':
                            strDefaultValue = 'True'
                        if defaultValue.lower() == 'false':
                            strDefaultValue = 'False'
                    itemLabel = wx.StaticText(argWindow, wx.ID_ANY, _('Default'))
                    itemTextCtrl = wx.ComboBox(argWindow, wx.ID_ANY, strDefaultValue, choices=['True', 'False'], style=wx.CB_DROPDOWN, size=(75,-1))
                    vsizer = wx.BoxSizer(wx.VERTICAL)
                    vsizer.Add(itemLabel, 0, wx.LEFT, 2)
                    vsizer.Add(itemTextCtrl, 0, wx.ALL, 0)
                    argLabel.controls.append(itemTextCtrl)
                    argSizer.Add(vsizer, (row,1), wx.DefaultSpan, wx.ALIGN_CENTER_VERTICAL|wx.RIGHT, 0)
                elif argtype == 'string' or argtype == 'int' and guitype == 'intlist':
                    strDefaultValue = strValuesList = ''
                    if defaultValue is not None:
                        if defaultValue:
                            if argtype == 'string':
                                strDefaultValue = '"%s"' % defaultValue.strip('"')
                            else:
                                strDefaultValue = str(defaultValue)
                    if other is not None:
                        strValuesList = ', '.join(other)
                    hsizer = wx.BoxSizer(wx.HORIZONTAL)
                    # Default control
                    itemLabel = wx.StaticText(argWindow, wx.ID_ANY, _('Default'))
                    itemTextCtrl = wx.TextCtrl(argWindow, wx.ID_ANY, strDefaultValue, size=(75,-1))
                    vsizer = wx.BoxSizer(wx.VERTICAL)
                    vsizer.Add(itemLabel, 0, wx.LEFT, 2)
                    vsizer.Add(itemTextCtrl, 0, wx.ALL, 0)
                    argLabel.controls.append(itemTextCtrl)
                    hsizer.Add(vsizer, 0, wx.EXPAND|wx.RIGHT,5)
                    # Values control
                    itemLabel = wx.StaticText(argWindow, wx.ID_ANY, _('Value list (comma separated)'))
                    itemTextCtrl = wx.TextCtrl(argWindow, wx.ID_ANY, strValuesList, size=(200,-1))
                    vsizer = wx.BoxSizer(wx.VERTICAL)
                    vsizer.Add(itemLabel, 0, wx.LEFT, 2)
                    vsizer.Add(itemTextCtrl, 1, wx.EXPAND|wx.ALL, 0)
                    argLabel.controls.append(itemTextCtrl)
                    hsizer.Add(vsizer, 1, wx.EXPAND|wx.RIGHT,5)

                    argSizer.Add(hsizer, (row,1), wx.DefaultSpan, wx.EXPAND|wx.ALIGN_CENTER_VERTICAL|wx.RIGHT, 0)
                    if wx.VERSION > (2, 9):
                        if not argSizer.IsColGrowable(1):
                            argSizer.AddGrowableCol(1)
                    else:
                        if not growable:
                            argSizer.AddGrowableCol(1)
                            growable = True
                row += 1
                self.argctrls.append((argtype, argname, argLabel, boolRepeatArg, boolOptionalArg))
        argWindow.SetSizer(argSizer)
        # Standard buttons
        okay  = wx.Button(self, wx.ID_OK, _('OK'))
        self.Bind(wx.EVT_BUTTON, self.OnButtonOK, okay)
        okay.SetDefault()
        cancel = wx.Button(self, wx.ID_CANCEL, _('Cancel'))
        btns = wx.StdDialogButtonSizer()
        btns.AddButton(okay)
        btns.AddButton(cancel)
        btns.Realize()
        # Set the sizer
        sizer = wx.BoxSizer(wx.VERTICAL)
        sizer.Add((-1,-1), 0, wx.TOP, 10)
        sizer.Add(filterLabel, 0, wx.EXPAND|wx.ALL, 5)
        sizer.Add(wx.StaticLine(self, wx.ID_ANY), 0, wx.EXPAND|wx.LEFT|wx.RIGHT, 5)
        sizer.Add(argWindow, 1, wx.EXPAND|wx.ALL, 5)
        sizer.Add(wx.StaticLine(self, wx.ID_ANY), 0, wx.EXPAND|wx.LEFT|wx.RIGHT, 5)
        #~ sizer.Add(wx.StaticText(self,wx.ID_ANY, _('* optional value')), 0, wx.EXPAND|wx.ALL, 10)
        sizer.Add(btns, 0, wx.EXPAND|wx.ALL, 5)
        self.SetSizer(sizer)
        sizer.Layout()
        argWindow.FitInside()
        w, h = argSizer.GetMinSize()
        w = max(w + 10, 400)
        h = min(h + 100, 700)
        self.SetSize(self.ClientToWindowSize((w, h)))
        if argWindow.HasScrollbar(wx.HORIZONTAL):
            scrollbar_w = wx.SystemSettings_GetMetric(wx.SYS_VSCROLL_X)
            self.SetSize(self.ClientToWindowSize((w + scrollbar_w, -1)))

    def OnButtonOK(self, event):
        strList = []
        for argtype, argname, argLabel, boolRepeatArg, boolOptionalArg in self.argctrls:
            if argtype is None and argname is None:
                continue
            strBase = '%(argtype)s %(argname)s' % locals()
            strInfoNew = strBase
            if argLabel is None:
                if argname is None:
                    strInfoNew = argtype
            else:

                strDef = argLabel.controls[0].GetValue().strip()
                is_list = argtype == 'int' and argLabel.controls[1].GetValue().count(',')
                #~ strList.append('%(strBase)s=%(strDefaultValue)s' % locals())
                if argtype in ('int', 'float') and not is_list:
                    strMin = argLabel.controls[1].GetValue().strip()
                    strMax = argLabel.controls[2].GetValue().strip()
                    strMod = argLabel.controls[3].GetValue().strip()
                    # Validate if any field has input
                    sliderValues = None
                    if strDef or strMin or strMax or strMod:
                        errorType, errorMessage, sliderValues = self.mainFrame.ValidateAvsSliderInputs(strDef, strMin, strMax, strMod)
                        if errorType is not None and errorType != -1:
                            self.ShowWarning(argLabel.controls[errorType], '%(argtype)s %(argname)s: %(errorMessage)s' % locals())
                            return
                    # Create the new string info
                    #~ if sliderValues is not None and len(sliderValues) == 1:
                    if strDef and not strMin and not strMax:
                        strInfoNew = '%(strBase)s=%(strDef)s' % locals()
                    elif not strMin and not strMax:
                        strInfoNew = strBase
                    elif strMod:
                        strInfoNew = '%(strBase)s=%(strDef)s (%(strMin)s to %(strMax)s by %(strMod)s)' % locals()
                    else:
                        strInfoNew = '%(strBase)s=%(strDef)s (%(strMin)s to %(strMax)s)' % locals()
                elif argtype == 'bool':
                    if strDef:
                        if strDef.lower() not in ('true', 'false'):
                            self.ShowWarning(argLabel.controls[0], '%s %s: %s' % (argtype, argname, _('Value must be True or False!')), comboBox=True)
                            return
                        strInfoNew = '%(strBase)s=%(strDef)s' % locals()
                elif argtype == 'string' or argtype == 'int' and is_list:
                    strValues = argLabel.controls[1].GetValue().strip()
                    if strDef or strValues:
                        if not strValues:
                            strValuesNew = ''
                            #~ msg =  _('Must enter a value list!')
                            #~ self.ShowWarning(argLabel.controls[1], '%s %s: %s' % (argtype, argname,msg))
                            #~ return
                            pass
                        else:
                            if argtype == 'int':
                                strValuesNew = ' (%s)' % ' / '.join([s.strip() for s in strValues.split(',')])
                            else:
                                strValuesNew = ' (%s)' % '/ '.join(['"%s"' % s.strip(' "') for s in strValues.split(',')])
                        if strDef and argtype == 'string':
                            strDef = '"%s"' % strDef.strip('"')
                        strInfoNew = '%(strBase)s=%(strDef)s%(strValuesNew)s' % locals()
            strRepeatArg = ''
            if boolRepeatArg:
                strRepeatArg = ' [, ...]'
            if boolOptionalArg:
                strInfoNew = '[{0}]'.format(strInfoNew)
            strList.append(strInfoNew+strRepeatArg)
        self.newFilterInfo = '(\n%s\n)' % ',\n'.join(strList)
        event.Skip()

    def GetNewFilterInfo(self):
        return self.newFilterInfo

    def ShowWarning(self, textCtrl, message, comboBox=False):
        color = textCtrl.GetBackgroundColour()
        textCtrl.SetBackgroundColour('pink')
        textCtrl.Refresh()
        wx.MessageBox(message, _('Error'), style=wx.OK|wx.ICON_ERROR)
        textCtrl.SetBackgroundColour(color)
        textCtrl.Refresh()
        textCtrl.GetParent().Refresh()
        if comboBox:
            textCtrl.SetMark(-1,-1)
        else:
            textCtrl.SetSelection(-1,-1)
        textCtrl.SetFocus()
        textCtrl.Refresh()