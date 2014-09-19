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

class STCPrintout(wx.Printout):
    """Specific printing support of the wx.StyledTextCtrl for the wxPython
    framework

    This class can be used for both printing to a printer and for print
    preview functions.

    """
    debuglevel = 0

    def __init__(self, stc, page_setup_data, print_mode=None, header=True,
                 title='', job_title='', border=False, zoom=False,
                 wrap=None):
        """Constructor.

        stc: wx.StyledTextCtrl to print

        page_setup_data: wx.PageSetupDialogData instance that
        is used to determine the margins of the page.

        print_mode: optional; of the wx.stc.STC_PRINT_* flags indicating
        how to render color text.  Defaults to
        wx.stc.STC_PRINT_COLOURONWHITEDEFAULTBG

        header: optional flag indicating whether or not to include a header
        on every page with the title and page number

        title: optional text string to use as the title, if header is True

        job_title: optional text string used to identify the job in the
        printing list

        border: optional flag indicating whether or not to draw a black
        border around the text on each page

        zoom: optional flag indicating whether or not to apply stc's
        current magnification to the output

        wrap: optional flag indicating whether or not to word-wrap long lines

        """
        if not job_title:
            job_title = wx.PrintoutTitleStr
        wx.Printout.__init__(self, job_title)
        self.stc = stc
        self.page_setup_data = page_setup_data
        if print_mode:
            self.print_mode = print_mode
        else:
            self.print_mode = wx.stc.STC_PRINT_COLOURONWHITEDEFAULTBG
        self.header = header
        if self.header:
            self.setHeaderFont()
            self.title = title
        self.stc.SetPrintMagnification(self.stc.GetZoom() if zoom else 0)
        if wrap is not None:
            self.stc.SetPrintWrapMode(wx.stc.STC_WRAP_WORD if wrap else
                                      wx.stc.STC_WRAP_NONE)
        self.border_around_text = border

    def OnPreparePrinting(self):
        """Called once before a print job is started to set up any defaults.

        """
        self.MapScreenSizeToPageMargins(self.page_setup_data)
        dc = self.GetDC()
        self._calculatePageStarts(dc)

    def _calculatePageStarts(self, dc):
        """Calculates offsets into the STC for each page

        This pre-calculates the page offsets for each page to support print
        preview being able to seek backwards and forwards.

        """
        if self.header:
            # Set font for title/page number rendering
            dc.SetFont(self.getHeaderFont())
            # Title
            self.header_height = dc.GetTextExtent(self.title)[1]
            # Page Number
            page_lbl = _("Page:")
            self.header_height = 1.5 * max(self.header_height,
                                           dc.GetTextExtent(page_lbl)[1])
        else:
            self.header_height = 0

        self.stc.SetPrintColourMode(self.print_mode)
        edge_mode = self.stc.GetEdgeMode()
        self.stc.SetEdgeMode(wx.stc.STC_EDGE_NONE)
        stc_len = self.stc.GetLength()
        self.start_points = [0]
        rect = self.GetLogicalPageMarginsRect(self.page_setup_data)
        rect[2] -= self.stc.GetMarginWidth(0)
        rect[1] += self.header_height
        rect[3] -= self.header_height
        if self.debuglevel > 0:
            print  "prepare rect: ", rect
        while self.start_points[-1] < stc_len:
            self.start_points.append(self.stc.FormatRange(False,
                                    self.start_points[-1], stc_len,
                                    dc, dc, rect, rect))
            if self.debuglevel > 0:
                if self.start_points[-1] == stc_len:
                    print "prepare printing - reached end of document: %d" % stc_len
                else:
                    print ("prepare printing - page %d first line: %d" % (
                           len(self.start_points), self.start_points[-1]))
        self.stc.SetEdgeMode(edge_mode)

    def GetPageInfo(self):
        """Return the valid page ranges.

        Note that pages are numbered starting from one.

        """
        return (1, len(self.start_points) - 1, 1, len(self.start_points) - 1)

    def HasPage(self, page):
        """Returns True if the specified page is within the page range

        """
        return page < len(self.start_points)

    def OnPrintPage(self, page):
        """Draws the specified page to the DC

        page: page number to render

        """
        self.MapScreenSizeToPageMargins(self.page_setup_data)
        dc = self.GetDC()
        self._drawPageContents(dc, page)
        if self.header:
            self._drawPageHeader(dc, page)
        if self.border_around_text:
            self._drawPageBorder(dc)
        return True

    def _drawPageContents(self, dc, page):
        """Render the STC window into a DC for printing.

        dc: the device context representing the page

        page: page number

        """
        self.stc.SetPrintColourMode(self.print_mode)
        edge_mode = self.stc.GetEdgeMode()
        self.stc.SetEdgeMode(wx.stc.STC_EDGE_NONE)
        stc_len = self.stc.GetLength()
        rect = self.GetLogicalPageMarginsRect(self.page_setup_data)
        rect[2] -= self.stc.GetMarginWidth(0)
        rect[1] += self.header_height
        rect[3] -= self.header_height
        next = self.stc.FormatRange(True, self.start_points[page-1], stc_len,
                                    dc, dc, rect, rect)
        self.stc.SetEdgeMode(edge_mode)
        if self.debuglevel > 0:
            print  "print rect: ", rect
            if next == stc_len:
                print "printing - reached end of document: %d" % stc_len
            else:
                print "printing - page %d first line: %d" % (page + 1, next)

    def _drawPageHeader(self, dc, page):
        """Draw the page header into the DC for printing

        dc: the device context representing the page

        page: page number

        """
        rect = self.GetLogicalPageMarginsRect(self.page_setup_data)
        # Set font for title/page number rendering
        dc.SetFont(self.getHeaderFont())
        dc.SetTextForeground ("black")
        # Title
        if self.title:
            dc.DrawText(self.title, rect[0], rect[1])
        # Page Number
        page_lbl = _("Page: %d") % page
        pg_lbl_w, pg_lbl_h = dc.GetTextExtent(page_lbl)
        dc.DrawText(page_lbl, rect[2] - pg_lbl_w, rect[1])

    def setHeaderFont(self, point_size=10, family=wx.FONTFAMILY_SWISS,
                      style=wx.FONTSTYLE_NORMAL, weight=wx.FONTWEIGHT_NORMAL):
        """Set the font to be used as the header font

        point_size: point size of the font

        family: one of the wx.FONTFAMILY_* values, e.g.
        wx.FONTFAMILY_SWISS, wx.FONTFAMILY_ROMAN, etc.

        style: one of the wx.FONTSTYLE_* values, e.g.
        wxFONTSTYLE_NORMAL, wxFONTSTYLE_ITALIC, etc.

        weight: one of the wx.FONTWEIGHT_* values, e.g.
        wx.FONTWEIGHT_NORMAL, wx.FONTWEIGHT_LIGHT, etc.

        """
        self.header_font_point_size = point_size
        self.header_font_family = family
        self.header_font_style = style
        self.header_font_weight = weight

    def getHeaderFont(self):
        """Returns the font to be used to draw the page header text

        returns: wx.Font instance

        """
        point_size = self.header_font_point_size
        font = wx.Font(point_size, self.header_font_family,
                       self.header_font_style, self.header_font_weight)
        return font

    def _drawPageBorder(self, dc):
        """Draw the page border into the DC for printing

        dc: the device context representing the page

        """
        dc.SetPen(wx.BLACK_PEN)
        dc.SetBrush(wx.TRANSPARENT_BRUSH)
        dc.DrawRectangleRect(self.GetLogicalPageMarginsRect(self.page_setup_data))
