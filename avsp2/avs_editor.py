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
import cgi                       # What is this module doing here anyways?
import string
import textwrap
import collections

import wx
from wx import stc

import global_vars
from icons import ok_icon, smile_icon, question_icon, rectangle_icon

from avsp2.oshelpers import startfile
from avsp2.filters import AvsFilterDict
from avsp2.i18nutils import _

class AvsStyledTextCtrl(stc.StyledTextCtrl):
    """
    Custom styled text control for avisynth language.
    """
    (
        STC_AVS_DEFAULT, STC_AVS_COMMENT, STC_AVS_ENDCOMMENT,
        STC_AVS_BLOCKCOMMENT, STC_AVS_NUMBER, STC_AVS_NUMBERBAD,
        STC_AVS_OPERATOR, STC_AVS_STRING, STC_AVS_STRINGEOL,
        STC_AVS_TRIPLE, STC_AVS_COREFILTER, STC_AVS_PLUGIN,
        STC_AVS_CLIPPROPERTY, STC_AVS_USERFUNCTION, STC_AVS_UNKNOWNFUNCTION,
        STC_AVS_USERSLIDER, STC_AVS_SCRIPTFUNCTION, STC_AVS_PARAMETER,
        STC_AVS_ASSIGN, STC_AVS_KEYWORD, STC_AVS_MISCWORD,
        STC_AVS_DATATYPE, STC_AVS_IDENTIFIER
    ) = range(23)

    def __init__(
            self,
            parent,
            app,
            id=wx.ID_ANY,
            pos=wx.DefaultPosition,
            size=wx.DefaultSize,
            style=wx.SIMPLE_BORDER,
            ):
        stc.StyledTextCtrl.__init__(self, parent, id, pos, size, style)
        self.app = app
        self.styleInfo = {
            self.STC_AVS_DEFAULT: ('default', ''),
            self.STC_AVS_COMMENT: ('comment', ',eol'),
            self.STC_AVS_ENDCOMMENT: ('endcomment', ''),
            self.STC_AVS_BLOCKCOMMENT: ('blockcomment', ''),
            self.STC_AVS_NUMBER: ('number', ''),
            self.STC_AVS_STRING: ('string', ''),
            self.STC_AVS_TRIPLE: ('stringtriple', ''),
            self.STC_AVS_COREFILTER: ('internalfilter', ''),
            self.STC_AVS_PLUGIN: ('externalfilter', ''),
            self.STC_AVS_CLIPPROPERTY: ('clipproperty', ''),
            self.STC_AVS_USERFUNCTION: ('userdefined', ''),
            self.STC_AVS_UNKNOWNFUNCTION: ('unknownfunction', ''),
            self.STC_AVS_PARAMETER: ('parameter', ''),
            self.STC_AVS_ASSIGN: ('assignment', ''),
            self.STC_AVS_OPERATOR: ('operator', ''),
            self.STC_AVS_STRINGEOL: ('stringeol', ',eol'),
            self.STC_AVS_USERSLIDER: ('userslider', ''),

            self.STC_AVS_SCRIPTFUNCTION: ('internalfunction', ''),
            self.STC_AVS_KEYWORD: ('keyword', ''),
            self.STC_AVS_MISCWORD: ('miscword', ''),

            stc.STC_STYLE_LINENUMBER: ('linenumber', ''),
            stc.STC_STYLE_BRACELIGHT: ('bracelight', ''),
            stc.STC_STYLE_BRACEBAD: ('badbrace', ''),
            self.STC_AVS_NUMBERBAD: ('badnumber', ''),

            self.STC_AVS_DATATYPE: ('datatype', ''),
        }
        self.avsfilterdict = AvsFilterDict(self.app.avsfilterdict)
        self.avsazdict = collections.defaultdict(list)
        self.styling_refresh_needed = False
        self.SetUserOptions()
        if wx.VERSION > (2, 9):
            self.SetScrollWidth(1)
            self.SetScrollWidthTracking(True)
        self.SetEOLMode(stc.STC_EOL_LF)
        #~ self.CmdKeyClear(stc.STC_KEY_TAB,0)
        self.UsePopUp(0)
        self.showLinenumbers = 1
        #~ self.enableFolding = 1
        self.calltipFilter = None
        self.calltiptext = None
        self.calltipOpenpos = None
        self.flagTextChanged = self.flagCodeFolding = False
        self.keywordStyleList = (
            self.STC_AVS_COREFILTER,
            #~ self.STC_AVS_CLIPPROPERTY,
            self.STC_AVS_PLUGIN,
            self.STC_AVS_USERFUNCTION,
            #~ self.STC_AVS_SCRIPTFUNCTION,
        )
        self.highlightwordStyleList = (
            self.STC_AVS_COREFILTER,
            self.STC_AVS_CLIPPROPERTY,
            self.STC_AVS_PLUGIN,
            self.STC_AVS_USERFUNCTION,
            self.STC_AVS_SCRIPTFUNCTION,
        )
        self.commentStyle = [self.STC_AVS_COMMENT, self.STC_AVS_BLOCKCOMMENT, self.STC_AVS_ENDCOMMENT]
        self.nonBraceStyles = [
            self.STC_AVS_COMMENT,
            self.STC_AVS_ENDCOMMENT,
            self.STC_AVS_BLOCKCOMMENT,
            self.STC_AVS_STRING,
            self.STC_AVS_TRIPLE,
            self.STC_AVS_STRINGEOL,
            self.STC_AVS_USERSLIDER,
        ]
        self.stc_attr = ( # 'eol' not supported in html export
            ('bold', 'italic', 'underline'),
            ('fore', 'back', 'face', 'size'))
        self.css_properties = {
            'bold':      'font-weight',
            'italic':    'font-style',
            'fore':      'color',
            'back':      'background-color',
            'face':      'font-family',
            'size':      'font-size',
            'underline': 'text-decoration',
        }
        # Auto-completion options
        self.AutoCompSetIgnoreCase(1)
        self.AutoCompSetDropRestOfWord(1)
        self.AutoCompSetAutoHide(1)
        self.AutoCompSetChooseSingle(0)
        self.AutoCompSetCancelAtStart(1)
        self.AutoCompSetSeparator(ord('\n'))
        self.AutoCompStops_chars = ''' `~!@#$%^&*()+=[]{};:'",<.>/?\|'''
        # Margin options
        #~ self.SetMarginType(0, stc.STC_MARGIN_NUMBER)
        self.SetMarginWidth(0, self.initialMarginWidth)
        self.SetMarginWidth(1, 0)
        self.SetMarginType(2, stc.STC_MARGIN_SYMBOL)
        self.SetMarginMask(2, stc.STC_MASK_FOLDERS)
        self.SetMarginSensitive(2, True)
        self.SetMarginWidth(2, 13)
        self.MarkerDefine(stc.STC_MARKNUM_FOLDEROPEN,    stc.STC_MARK_MINUS)
        self.MarkerDefine(stc.STC_MARKNUM_FOLDER,        stc.STC_MARK_PLUS)
        self.MarkerDefine(stc.STC_MARKNUM_FOLDERSUB,     stc.STC_MARK_EMPTY)
        self.MarkerDefine(stc.STC_MARKNUM_FOLDERTAIL,    stc.STC_MARK_EMPTY)
        self.MarkerDefine(stc.STC_MARKNUM_FOLDEREND,     stc.STC_MARK_EMPTY)
        self.MarkerDefine(stc.STC_MARKNUM_FOLDEROPENMID, stc.STC_MARK_EMPTY)
        self.MarkerDefine(stc.STC_MARKNUM_FOLDERMIDTAIL, stc.STC_MARK_EMPTY)
        self.SetSavePoint()
        # Event handling
        self.Bind(stc.EVT_STC_UPDATEUI, self.OnUpdateUI)
        self.Bind(stc.EVT_STC_CHANGE, self.OnTextChange)
        self.Bind(stc.EVT_STC_CHARADDED, self.OnTextCharAdded)
        self.Bind(stc.EVT_STC_NEEDSHOWN, self.OnNeedShown)
        self.Bind(wx.EVT_KEY_UP, self.OnKeyUp)
        self.Bind(wx.EVT_KEY_DOWN, self.OnKeyDown)
        self.Bind(wx.EVT_LEFT_DOWN, self.OnLeftMouseDown)
        self.Bind(stc.EVT_STC_AUTOCOMP_SELECTION, self.OnAutocompleteSelection)
        self.Bind(stc.EVT_STC_USERLISTSELECTION, self.OnUserListSelection)
        self.Bind(stc.EVT_STC_CALLTIP_CLICK, self.OnCalltipClick)
        self.Bind(wx.EVT_KILL_FOCUS, self.OnKillFocus)
        self.Bind(wx.EVT_SET_FOCUS, self.OnSetFocus)
        self.Bind(stc.EVT_STC_MARGINCLICK, self.OnMarginClick)
        self.Bind(stc.EVT_STC_ZOOM, lambda event: self.fitNumberMarginWidth())
        try:
            self.Bind(wx.EVT_MOUSE_CAPTURE_LOST, lambda event: self.ReleaseMouse())
        except AttributeError:
            pass
        if self.GetLexer() == stc.STC_LEX_CONTAINER:
            self.Bind(stc.EVT_STC_STYLENEEDED, self.OnStyleNeeded)

    def SetUserOptions(self):
        # AviSynth filter information
        #~ if not filterDict:
            #~ filterDict = self.defineFilterDict()
            #~ filterDict = dict([(name.lower(), (name,args,ftype)) for name, (args,ftype) in filterDict.items()])
        #~ if not keywordLists:
            #~ keywords = ['default', 'end', 'return', 'global', 'function', 'last', 'true', 'false', 'try', 'catch',]
            #~ datatypes = ['clip', 'int', 'float', 'string', 'bool', 'val']
            #~ operators = ('-', '*', ',', '.', '/', ':', '?', '\\', '+', '<', '>', '=', '(', ')', '[', ']', '{', '}', '!', '%', '&', '|')
            #~ miscwords = []
            #~ keywordLists = (keywords, datatypes, operators, miscwords)
        self.SetTextStyles(self.app.options['textstyles'], self.app.options['usemonospacedfont'])
        if self.styling_refresh_needed:
            self.styling_refresh_needed = False
            self.Colourise(0, 0) # set self.GetEndStyled() to 0
        if self.app.options['autocompleteicons']:
            self.RegisterImage(1, ok_icon.GetBitmap())
            self.RegisterImage(2, smile_icon.GetBitmap())
            self.RegisterImage(3, question_icon.GetBitmap())
            self.RegisterImage(4, rectangle_icon.GetBitmap())
            self.RegisterImage(5, wx.ArtProvider.GetBitmap(wx.ART_FOLDER))
            self.RegisterImage(6, wx.ArtProvider.GetBitmap(wx.ART_NORMAL_FILE))
        else:
            self.ClearRegisteredImages()
        # General options
        self.SetUseTabs(self.app.options['usetabs'])
        self.SetTabWidth(self.app.options['tabwidth'])
        self.SetCaretLineBack(self.app.options['textstyles']['highlightline'].split(':')[1])
        self.SetCaretLineVisible(self.app.options['highlightline'])
        if self.app.options['wrap']:
            self.SetWrapMode(stc.STC_WRAP_WORD)
        else:
            self.SetWrapMode(stc.STC_WRAP_NONE)
        self.SetFoldFlags(self.app.options['foldflag']<<4)
        if self.app.options['numlinechars']:
            self.initialMarginWidth = self.numlinechars2pixels(self.app.options['numlinechars'])
            self.fitNumberMarginWidth()
        else:
            self.initialMarginWidth = 0
            self.SetMarginWidth(0, 0)

    def defineFilterDict(self): # not used anymore, filter info is stored in MainFrame.filterdbfilename
        return {
            'AddBorders': ('(clip, int left, int top, int right, int bottom, int color)', 0),
            'Amplify': ('(clip, float amount1 [, ...])', 0),
            'AmplifydB': ('(clip, float amount1 [, ...])', 0),
            'Animate': ('(clip, int start_frame, int end_frame, string filtername, start_args, end_args)', 0),
            'ApplyRange': ('(clip, int start_frame, int end_frame, string filtername, args)', 0),
            'AssumeFrameBased': ('(clip)', 0),
            'AssumeFieldBased': ('(clip)', 0),
            'AssumeBFF': ('(clip)', 0),
            'AssumeTFF': ('(clip)', 0),
            'AssumeSampleRate': ('(clip, int samplerate)', 0),
            'AudioDub': ('(video_clip, audio_clip)', 0),
            'AVISource': ('(string filename [, ...], bool "audio", string "pixel_type")', 0),
            'OpenDMLSource': ('(string filename [, ...], bool "audio", string "pixel_type")', 0),
            'AVIFileSource': ('(string filename [, ...], bool "audio", string "pixel_type")', 0),
            'WAVSource': ('(string filename [, ...])', 0),
            'BlankClip': ('(clip clip, int "length", int "width", int "height", string "pixel_type",\nfloat "fps", int "fps_denominator", int "audio_rate", bool "stereo",\nbool "sixteen_bit", int "color")', 0),
            'Blackness': ('(clip clip, int "length", int "width", int "height", string "pixel_type",\nfloat "fps", int "fps_denominator", int "audio_rate", bool "stereo",\nbool "sixteen_bit", int "color")', 0),
            'Blur': ('(clip, float amount)', 0),
            'Sharpen': ('(clip, float amount)', 0),
            'Bob': ('(clip, float "b", float "c", float "height")', 0),
            'ColorBars': ('(int width, int height)', 0),
            'ColorYUV': ('(clip, float "gain_y", float "off_y", float "gamma_y", float "cont_y",\nfloat "gain_u", float "off_u", float "gamma_u", float "cont_u", float "gain_v",\nfloat "off_v", float "gamma_v", float "cont_v", string "levels", string "opt",\nbool "showyuv", bool "analyze", bool "autowhite", bool "autogain")', 0),
            'ComplementParity': ('(clip)', 0),
            'Compare': ('(clip_filtered, clip_original, string "channels", string "logfile", bool "show_graph")', 0),
            'ConditionalFilter': ('(clip testclip, clip source1, clip source2, string filter,\nstring operator, string value, bool ''show'')', 0),
            'FrameEvaluate': ('(clip clip, script function, bool "after_frame")', 0),
            'ScriptClip': ('(clip clip, string function, bool ''show'')', 0),
            'ConditionalReader': ('(clip clip, string filename, string variablename, bool "show")', 0),
            'ConvertBackToYUY2': ('(clip, bool "interlaced")', 0),
            'ConvertToRGB': ('(clip, bool "interlaced")', 0),
            'ConvertToRGB24': ('(clip, bool "interlaced")', 0),
            'ConvertToRGB32': ('(clip, bool "interlaced")', 0),
            'ConvertToYUY2': ('(clip, bool "interlaced")', 0),
            'ConvertToYV12': ('(clip, bool "interlaced")', 0),
            'ConvertAudioTo8bit': ('(clip)', 0),
            'ConvertAudioTo16bit': ('(clip)', 0),
            'ConvertAudioTo24bit': ('(clip)', 0),
            'ConvertAudioTo32bit': ('(clip)', 0),
            'ConvertAudioToFloat': ('(clip)', 0),
            'ConvertToMono': ('(clip)', 0),
            'Crop': ('(clip, int left, int top, int -right, int -bottom, bool "align")', 0),
            'CropBottom': ('(clip, int count, bool "align")', 0),
            'DelayAudio': ('(clip, float seconds)', 0),
            'DeleteFrame': ('(clip, int frame)', 0),
            'DirectShowSource': ('(string filename, int "fps", bool "seek", bool "audio", bool "video")', 0),
            'Dissolve': ('(clip1, clip2 [, ...], int overlap)', 0),
            'DoubleWeave': ('(clip)', 0),
            'DuplicateFrame': ('(clip, int frame)', 0),
            'EnsureVBRMP3Sync': ('(clip)', 0),
            'FadeOut': ('(clip, int frames, int "color")', 0),
            'FadeOut2': ('(clip, int frames, int "color")', 0),
            'FadeIn': ('(clip, int frames, int "color")', 0),
            'FadeIn2': ('(clip, int frames, int "color")', 0),
            'FadeIO': ('(clip, int frames, int "color")', 0),
            'FadeIO2': ('(clip, int frames, int "color")', 0),
            'FixBrokenChromaUpsampling': ('(clip)', 0),
            'FixLuminance': ('(clip, int intercept, int slope)', 0),
            'FlipHorizontal': ('(clip)', 0),
            'FlipVertical': ('(clip)', 0),
            'AssumeFPS': ('(clip, float fps, bool "sync_audio")', 0),
            'ChangeFPS': ('(clip, float fps, bool "linear")', 0),
            'ConvertFPS': ('(clip, int new_rate, int "zone", int "vbi")', 0),
            'FreezeFrame': ('(clip, int first_frame, int last_frame, int source_frame)', 0),
            'GeneralConvolution': ('(clip, int "bias", string matrix)', 0),
            'GetChannel': ('(clip, int ch1 [, int ch2, ...])', 0),
            'Greyscale': ('(clip)', 0),
            'Histogram': ('(clip, string ''mode'')', 0),
            'ImageReader': ('(string path, int begin, int end, int fps, bool "use_DevIL")', 0),
            'ImageWriter': ('(clip, string "path", int "begin", int "end", string format)', 0),
            'Info': ('(clip)', 0),
            'Interleave': ('(clip1, clip2 [, ...])', 0),
            'Invert': ('(clip, string "channels")', 0),
            'KillAudio': ('(clip)', 0),
            'Layer': ('(clip, layer_clip, string "op", int "level", int "x", int "y", int "threshold",\nbool "use_chroma")', 0),
            'Mask': ('(clip, mask_clip)', 0),
            'ResetMask': ('(clip)', 0),
            'ColorKeyMask': ('(clip, int color, int tolerance)', 0),
            'Letterbox': ('(clip, int top, int bottom, [int left, int right])', 0),
            'Levels': ('(clip, int input_low, float gamma, int input_high, int output_low, int\noutput_high, bool "coring")', 0),
            'Limiter': ('(clip, int ''min_luma'', int ''max_luma'', int ''min_chroma'', int ''max_chroma'')', 0),
            'LoadPlugin': ('(string filename)', 0),
            'Loop': ('(clip, int "times", int "start", int "end")', 0),
            'MergeChannels': ('(clip1, clip2 [, ...])', 0),
            'MergeChroma': ('(clip1, clip2, float weight)', 0),
            'MergeLuma': ('(clip1, clip2, float weight)', 0),
            'MessageClip': ('(string message, int "width", int "height", bool "shrink", int "text_color",\nint "halo_color", int "bg_color")', 0),
            'MixAudio': ('(clip1, clip 2, clip1_factor, "clip2_factor")', 0),
            'Normalize': ('(clip, float "volume", bool "show")', 0),
            'Overlay': ('(clip, clip overlay, int ''x'', int ''y'', clip ''mask'', float ''opacity'',\nstring ''mode'', bool ''greymask'', string ''output'', bool ''ignore_conditional'',\nbool ''pc_range'')', 0),
            'PeculiarBlend': ('(clip, int cutoff)', 0),
            'Pulldown': ('(clip, int a , int b)', 0),
            'RGBAdjust': ('(clip, float red, float green, float blue, float alpha)', 0),
            'HorizontalReduceBy2': ('(clip)', 0),
            'VerticalReduceBy2': ('(clip)', 0),
            'ReduceBy2': ('(clip)', 0),
            'ResampleAudio': ('(clip, int new_sample_rate)', 0),
            'BilinearResize': ('(clip, int target_width, int target_height)', 0),
            'BicubicResize': ('(clip, int target_width, int target_height, float "b", float "c")', 0),
            'LanczosResize': ('(clip, int target_width, int target_height)', 0),
            'PointResize': ('(clip, int target_width, int target_height)', 0),
            'Reverse': ('(clip)', 0),
            'SegmentedAVISource': ('(string base_filename [, ...], bool "audio")', 0),
            'SegmentedDirectShowSource': ('(string base_filename [, ...] [, fps])', 0),
            'SelectEven': ('(clip)', 0),
            'SelectOdd': ('(clip)', 0),
            'SelectEvery': ('(clip, int step_size, int offset1 [, int offset2 [, ...]])', 0),
            'SelectRangeEvery': ('(clip, int period, int range)', 0),
            'SeparateFields': ('(clip)', 0),
            'ShowAlpha': ('(clip, string pixel_type)', 0),
            'ShowFiveVersions': ('(clip1, clip2, clip3, clip4, clip5)', 0),
            'ShowFrameNumber': ('(clip, bool "scroll")', 0),
            'ShowSMPTE': ('(clip, float fps)', 0),
            'SpatialSoften': ('(clip, int radius, int luma_threshold, int chroma_threshold)', 0),
            'TemporalSoften': ('(clip, int radius, int luma_threshold, int chroma_threshold, int "scenechange",\nint "mode")', 0),
            'AlignedSplice': ('(clip1, clip2 [, ...])', 0),
            'UnAlignedSplice': ('(clip1, clip2 [, ...])', 0),
            'SSRC': ('(int samplerate, bool "fast")', 0),
            'StackHorizontal': ('(clip1, clip2 [, ...])', 0),
            'StackVertical': ('(clip1, clip2 [, ...])', 0),
            'Subtitle': ('(clip, string text, int "x", int "y", int "first_frame", int "last_frame",\nstring "font", int "size", int "text_color", int "halo_color")', 0),
            'Subtract': ('(clip1, clip2)', 0),
            'SuperEQ': ('(string filename)', 0),
            'SwapUV': ('(clip)', 0),
            'UToY': ('(clip)', 0),
            'VToY': ('(clip)', 0),
            'YToUV': ('(clip)', 0),
            'SwapFields': ('(clip)', 0),
            'Tone': ('(float "length", float "frequency", int "samplerate", int "channels", string "type")', 0),
            'Trim': ('(clip, int first_frame, int last_frame)', 0),
            'TurnLeft': ('(clip)', 0),
            'TurnRight': ('(clip)', 0),
            'Tweak': ('(clip, float "hue", float "sat", float "bright", float "cont", bool "coring")', 0),
            'Version': ('()', 0),
            'Weave': ('(clip)', 0),
        }

        #~ # Currently FunctionNames, ClipProperties, and KeyWords are unused
        #~ self.FunctionNames = ['floor', 'ceil', 'round', 'int', 'float', 'frac', 'abs', 'sign',
                                       #~ 'hexvalue', 'sin', 'cos', 'pi', 'log', 'exp', 'pow', 'sqrt', 'rand', 'spline',
                                       #~ 'ucase', 'lcase', 'revstr', 'strlen', 'findstr', 'leftstr', 'midstr',
                                       #~ 'versionnumber', 'versionstring', 'chr', 'time', 'value', 'string',
                                       #~ 'isbool', 'isint', 'isfloat', 'isstring', 'isclip',
                                       #~ 'select', 'defined', 'default', 'exist', 'eval', 'apply', 'import', 'try', 'catch',
                                       #~ 'setmemorymax', 'setworkingdir']
        #~ self.ClipProperties = ['width', 'height', 'framecount', 'framerate',
                                     #~ 'audiorate', 'audiolength', 'audiochannels', 'audiobits',
                                     #~ 'isrgb', 'isrgb24', 'isrgb32', 'isyuy2', 'isyuv',
                                     #~ 'isplanar', 'isinterleaved', 'isfieldbased', 'isframebased', 'getparity']
        #~ self.KeyWords = tuple(' '.join(self.FilterNames).lower().split(' '))

    def ParseFunctions(self, text=None, refresh_highlighting=False):
        if text is None:
            text = self.GetText()
        filterInfo = self.app.ParseAvisynthScript(script_text=text, quiet=True) or []
        self.avsfilterdict.clear()
        self.avsfilterdict.update(dict(
            [
            (filtername.lower(), (filterargs, self.STC_AVS_USERFUNCTION, filtername, None))
            for filename, filtername, filterargs, ftype in filterInfo
            ]
        ))
        self.avsazdict = self.app.GetAutocompleteDict(self.avsfilterdict.own_dict)
        if refresh_highlighting:
            self.Colourise(0, 0)

    def SetTextStyles(self, textstyles, monospaced=False):
        self.SetLexer(stc.STC_LEX_CONTAINER)
        #~ self.commentStyle = [self.STC_AVS_COMMENT, self.STC_AVS_BLOCKCOMMENT, self.STC_AVS_ENDCOMMENT]
        #~ self.nonBraceStyles = [
            #~ self.STC_AVS_COMMENT,
            #~ self.STC_AVS_ENDCOMMENT,
            #~ self.STC_AVS_BLOCKCOMMENT,
            #~ self.STC_AVS_STRING,
            #~ self.STC_AVS_TRIPLE,
            #~ self.STC_AVS_STRINGEOL,
            #~ self.STC_AVS_USERSLIDER,
        #~ ]
        default = 'font:Arial, size:10, fore:#000000, back:#FFFFFF'

        # Global default styles for all languages
        self.StyleSetSpec(stc.STC_STYLE_DEFAULT, textstyles.get('default', default))
        #~ if textstyles.get('default', default).endswith('bold'):
            #~ self.StyleSetBold(stc.STC_STYLE_DEFAULT, 1)
        #~ else:
            #~ self.StyleSetBold(stc.STC_STYLE_DEFAULT, 0)
        if monospaced:
            face = ''
            size = ''
            for item in textstyles['monospaced'].split(','):
                if item.lower().startswith('face:'):
                    face = item.split(':')[1]
                if item.lower().startswith('size:'):
                    size = int(item.split(':')[1])
            self.StyleSetFaceName(stc.STC_STYLE_DEFAULT, face)
            self.StyleSetSize(stc.STC_STYLE_DEFAULT, size)
        self.StyleClearAll()  # Reset all to be like the default

        for style, (key, extra) in self.styleInfo.iteritems():
            self.StyleSetSpec(style, textstyles.get(key, default) + extra)
            if monospaced:
                self.StyleSetFaceName(style, face)
                self.StyleSetSize(style, size)
        # Set miscellaneous non-style colors
        for key in ('calltip', 'calltiphighlight'):
            value = textstyles[key]
            for elem in value.split(','):
                if elem.startswith('fore:'):
                    if key == 'calltip':
                        self.CallTipSetForeground(elem.split(':')[1].strip())
                    else:
                        self.CallTipSetForegroundHighlight(elem.split(':')[1].strip())
                if elem.startswith('back:'):
                    self.CallTipSetBackground(elem.split(':')[1].strip())
        self.SetCaretForeground(textstyles['cursor'].split(':')[1])
        for elem in textstyles['highlight'].split(','):
            if elem.startswith('fore:'):
                if self.app.options['highlight_fore']:
                    self.SetSelForeground(True, elem.split(':')[1].strip())
                else:
                    self.SetSelForeground(False, wx.WHITE)
            elif elem.startswith('back:'):
                self.SetSelBackground(True, elem.split(':')[1].strip())
        fore = back = None
        for elem in textstyles['foldmargin'].split(','):
            if elem.startswith('fore:'):
                fore = elem.split(':')[1].strip()
            elif elem.startswith('back:'):
                back = elem.split(':')[1].strip()
                self.SetFoldMarginColour(True, back)
                self.SetFoldMarginHiColour(True, back)
        fore = fore or 'white'
        back = back or 'black'
        self.MarkerSetForeground(stc.STC_MARKNUM_FOLDEROPEN, fore)
        self.MarkerSetBackground(stc.STC_MARKNUM_FOLDEROPEN, back)
        self.MarkerSetForeground(stc.STC_MARKNUM_FOLDER, fore)
        self.MarkerSetBackground(stc.STC_MARKNUM_FOLDER, back)
        self.MarkerSetForeground(stc.STC_MARKNUM_FOLDERSUB, fore)
        self.MarkerSetBackground(stc.STC_MARKNUM_FOLDERSUB, back)
        self.MarkerSetForeground(stc.STC_MARKNUM_FOLDERTAIL, fore)
        self.MarkerSetBackground(stc.STC_MARKNUM_FOLDERTAIL, back)
        self.MarkerSetForeground(stc.STC_MARKNUM_FOLDEREND, fore)
        self.MarkerSetBackground(stc.STC_MARKNUM_FOLDEREND, back)
        self.MarkerSetForeground(stc.STC_MARKNUM_FOLDEROPENMID, fore)
        self.MarkerSetBackground(stc.STC_MARKNUM_FOLDEROPENMID, back)
        self.MarkerSetForeground(stc.STC_MARKNUM_FOLDERMIDTAIL, fore)
        self.MarkerSetBackground(stc.STC_MARKNUM_FOLDERMIDTAIL, back)

    def numlinechars2pixels(self, numlinechars):
        return self.TextWidth(stc.STC_STYLE_LINENUMBER, '%s' % ('0'*numlinechars)) + 12

    def fitNumberMarginWidth(self):
        # Update line number margin width
        w = self.TextWidth(stc.STC_STYLE_LINENUMBER, '%s' % str(self.GetLineCount())) + 12
        w = max(w, self.initialMarginWidth)
        if w != self.GetMarginWidth(0):
            self.SetMarginWidth(0, w)

    # New utility functions
    def ShowQuickFindDialog(self):
        if self.app.findDialog.IsShown():
            self.app.findDialog.SetFocus()
        else:
            x0, y0 = self.app.currentScript.GetScreenPosition()
            w0, h0 = self.app.currentScript.GetSize()
            w, h = self.app.findDialog.GetSize()
            self.app.findDialog.SetPosition((x0 + w0 - w - 5, y0 + 5))
            self.app.findDialog.Show()
            self.app.findDialog.SetFocus()
        text = self.GetSelectedText()
        if text:
            self.app.findDialog.UpdateText(text)

    def ShowFindReplaceDialog(self, find=False):
        self.app.findDialog.Hide()
        text = self.GetSelectedText()
        if self.app.replaceDialog.IsShown():
            self.app.replaceDialog.SetFocus()
            if text:
                if '\n' in text.strip():
                    self.app.replaceDialog.only_selection.SetValue(True)
                else:
                    ctrl = 'find' if find else 'replace'
                    self.app.replaceDialog.UpdateText(text, ctrl)
        else:
            self.app.replaceDialog.Show()
            if text:
                if '\n' in text.strip():
                    self.app.replaceDialog.only_selection.SetValue(True)
                else:
                    self.app.replaceDialog.UpdateText(text, 'find')

    def FindNext(self):
        if self.AutoCompActive():
            self.AutoCompCancel()
        if self.app.replaceDialog.GetFindText():
            self.app.replaceDialog.OnFindNext()
        elif self.app.replaceDialog.IsShown():
            self.ShowFindReplaceDialog()
        else:
            text = self.GetSelectedText()
            if text:
                self.app.findDialog.UpdateText(text)
                self.app.replaceDialog.OnFindNext()
            else:
                self.ShowQuickFindDialog()

    def FindPrevious(self):
        if self.AutoCompActive():
            self.AutoCompCancel()
        if self.app.replaceDialog.GetFindText():
            self.app.replaceDialog.OnFindPrevious()
        elif self.app.replaceDialog.IsShown():
            self.ShowFindReplaceDialog()
        else:
            text = self.GetSelectedText()
            if text:
                self.app.findDialog.UpdateText(text)
                self.app.replaceDialog.OnFindPrevious()
            else:
                self.ShowQuickFindDialog()

    def ReplaceNext(self):
        if self.AutoCompActive():
            self.AutoCompCancel()
        if self.app.replaceDialog.GetReplaceText():
            if self.app.replaceDialog.GetFindText():
                self.app.replaceDialog.OnReplace()
            else:
                text = self.GetSelectedText()
                if text:
                    self.app.replaceDialog.UpdateText(text, 'find')
                    self.app.replaceDialog.OnReplace()
                else:
                    self.ShowFindReplaceDialog()
        else:
            self.ShowFindReplaceDialog()

    def IndentSelection(self):
        self.CmdKeyExecute(stc.STC_CMD_TAB)

    def UnIndentSelection(self):
        self.CmdKeyExecute(stc.STC_CMD_BACKTAB)

    def BlockComment(self):
        line1 = self.LineFromPosition(self.GetSelectionStart())
        line2 = self.LineFromPosition(self.GetSelectionEnd())
        self.BeginUndoAction()
        for line in xrange(line1, line2+1):
            txt = self.GetLine(line)
            if txt.strip():
                pos = self.PositionFromLine(line) + len(txt) - len(txt.lstrip())
                if txt.strip().startswith('#~ '):
                    self.SetTargetStart(pos)
                    self.SetTargetEnd(pos+3)
                    self.ReplaceTarget('')
                else:
                    self.SetTargetStart(pos)
                    self.SetTargetEnd(pos)
                    self.ReplaceTarget('#~ ')
        self.EndUndoAction()

    def StyleComment(self):
        pos = self.GetCurrentPos()
        start = self.PositionFromLine(self.LineFromPosition(pos))
        style = self.GetStyleAt(pos)
        if style == self.STC_AVS_COMMENT:
            while pos > start and self.GetStyleAt(pos-1) == self.STC_AVS_COMMENT:
                pos -= 1
            self.SetTargetStart(pos)
            if self.GetTextRange(pos, pos+3) == '#~ ':
                self.SetTargetEnd(pos+3)
            else:
                self.SetTargetEnd(pos+1)
            self.ReplaceTarget('')
        else:
            if pos > start and unichr(self.GetCharAt(pos)) == '.' and self.GetStyleAt(pos-1) == self.STC_AVS_NUMBER:
                pos -= 1
                style = self.STC_AVS_NUMBER
            while pos > start and self.GetStyleAt(pos-1) == style:
                pos -= 1
            if pos > start and unichr(self.GetCharAt(pos-1)) == '.':
                pos -= 1
            if style == self.STC_AVS_NUMBER:
                while pos > start and self.GetStyleAt(pos-1) == style:
                    pos -= 1
                if pos > start and unichr(self.GetCharAt(pos-1)) in '+-':
                    pos -= 1
            self.InsertText(pos, '#~ ')

    def MoveSelectionByOneLine(self, up=True):
        selA = self.GetSelectionStart()
        selB = self.GetSelectionEnd()
        line1 = self.LineFromPosition(selA)
        line2 = self.LineFromPosition(selB)
        numlines = self.GetLineCount()
        if line2 == numlines - 1:
            if selB != self.GetLength() or selB != self.PositionFromLine(line2):
                self.InsertText(self.GetLineEndPosition(line2), '\n')
        posA = self.PositionFromLine(line1)
        if self.GetSelectionEnd() == self.PositionFromLine(line2) and selA != selB:
            posB = self.PositionFromLine(line2)
        else:
            posB = self.PositionFromLine(line2 + 1)
        if up:
            newline = max(line1 - 1, 0)
        else:
            newline = min(line1 + 1, numlines-1 - (line2 - line1))
        if newline == line1:
            return
        if newline == self.GetLineCount() - 1 and self.GetLine(newline) != '':
                self.InsertText(self.GetLineEndPosition(newline), '\n')
        self.BeginUndoAction()
        self.SetSelection(posA, posB)
        txt = self.GetSelectedText()
        self.ReplaceSelection('')
        newpos = self.PositionFromLine(newline)
        self.GotoPos(newpos)
        self.ReplaceSelection(txt)
        self.SetSelection(newpos, newpos+len(txt))
        self.EndUndoAction()

    def ShowAutocomplete(self, all=False, auto=0):
        pos = self.GetCurrentPos()
        startwordpos = self.WordStartPosition(pos,1)
        if pos == startwordpos:
            return
        word = self.GetTextRange(startwordpos,pos)
        #~ if len(word) == 0:
            #~ return
        keywords = []
        wordlower = word.lower()
        avsazdict = self.app.avsazdict_all if all else self.app.avsazdict
        first_chr = word[0].lower()
        for keyword in set(avsazdict[first_chr] + self.avsazdict[first_chr]):
            if keyword.lower().startswith(wordlower):
                keywords.append(keyword)
        if self.app.options['autocompletevariables']:
            lineCount = self.LineFromPosition(pos)
            line = 0
            while line <= lineCount:
                if line == lineCount:
                    line += 1
                    lineCount = self.GetLineCount()
                    continue
                start = self.PositionFromLine(line)
                eol = self.GetLineEndPosition(line)
                #~ while unichr(self.GetCharAt(eol-1)) == '\\' or unichr(self.GetCharAt(eol+1)) == '\\':
                    #~ line += 1
                    #~ if line >= lineCount:
                        #~ break
                    #~ eol = self.GetLineEndPosition(line)
                while line < lineCount - 1 and (self.FindText(self.PositionFromLine(line), eol, r'\\[ ]*$', stc.STC_FIND_REGEXP) != -1 or \
                                                self.FindText(eol+1, self.GetLineEndPosition(line+1), r'^[ ]*\\', stc.STC_FIND_REGEXP) != -1):
                    line += 1
                    eol = self.GetLineEndPosition(line)
                start = self.FindText(start, eol, r'\<', stc.STC_FIND_REGEXP)
                while start != -1 and self.GetStyleAt(start) == self.STC_AVS_BLOCKCOMMENT:
                    end = self.WordEndPosition(start, 1)
                    start = self.FindText(end, eol, r'\<', stc.STC_FIND_REGEXP)
                if start == -1:
                    line += 1
                    continue
                end = self.WordEndPosition(start, 1)
                keyword = self.GetTextRange(start, end)
                #~ print keyword
                if self.GetStyleAt(start) == self.STC_AVS_ASSIGN and keyword.lower().startswith(wordlower) and keyword not in keywords:
                    keywords.append(keyword)
                elif keyword == 'global' or keyword == 'function':
                    start = self.FindText(end, self.GetLineEndPosition(line), r'\<', stc.STC_FIND_REGEXP)
                    if start == -1:
                        line += 1
                        continue
                    end = self.WordEndPosition(start, 1)
                    keyword = self.GetTextRange(start, end)
                    if keyword.lower().startswith(wordlower) and keyword not in keywords:
                        keywords.append(keyword)
                line += 1
            keywords.sort(key=lambda s: s.lower())
        if keywords:
            if auto != 2 or (len(keywords) == 1 and len(keywords[0]) != len(word)):
                if self.app.options['autocompleteicons']:
                    for i in range(len(keywords)):
                        keyword = keywords[i].lower()
                        if keyword not in self.avsfilterdict:
                            keywords[i] += '?4'
                            continue
                        keyword = self.avsfilterdict[keyword][3] or keyword
                        preset = self.app.options['filterpresets'].get(keyword)
                        if preset is None:
                            preset = self.CreateDefaultPreset(keywords[i])
                        question = preset.count('?')
                        comma = preset.count(',')
                        if question == 0:
                            keywords[i] += '?1'
                        elif question == 1 or question*10 <= (comma+1)*3:
                            keywords[i] += '?2'
                        elif comma <= 1:
                            pass
                        elif question*10 >= (comma+1)*7:
                            keywords[i] += '?3'
                self.autocomplete_case = 'function'
                self.AutoCompStops(self.AutoCompStops_chars)
                self.AutoCompShow(len(word), '\n'.join(keywords))
                if self.CallTipActive():
                    self.CallTipCancelCustom()
            #~ if len(keywords) == 1:
                #~ self.FinishAutocomplete()
        elif auto == 0 and pos - startwordpos > 0:
            self.CmdKeyExecute(stc.STC_CMD_CHARLEFT)
            wx.CallAfter(self.ShowAutocomplete)

    def FinishAutocomplete(self, key=None):
        self.AutoCompComplete()
        pos = self.GetCurrentPos()
        startwordpos = self.WordStartPosition(pos,1)
        filtername = self.GetTextRange(startwordpos,pos)
        if filtername.lower() not in self.avsfilterdict:
            return
        boolActivatePreset = (
            self.app.options['presetactivatekey'] == 'tab' and key == wx.WXK_TAB or
            self.app.options['presetactivatekey'] == 'return' and key in (wx.WXK_RETURN, wx.WXK_NUMPAD_ENTER) or
            self.app.options['presetactivatekey'] == 'both')
        if boolActivatePreset:
            keyword = filtername.lower()
            keyword = self.avsfilterdict[keyword][3] or keyword
            preset = self.app.options['filterpresets'].get(keyword)
            boolHighlightQuestionMarks = True
            if preset is not None:
                self.SetSelection(startwordpos, pos)
                self.ReplaceSelection(preset)
                cursorTag = '[|]'
                nCursorTags = preset.count(cursorTag)
                if nCursorTags > 0:
                    minPos = startwordpos
                    maxPos = self.GetCurrentPos()
                    startSelectionPos = endSelectionPos = None
                    for i in xrange(nCursorTags):
                        findpos = self.FindText(minPos, maxPos, cursorTag, stc.STC_FIND_MATCHCASE)
                        if findpos != -1:
                            self.SetSelection(findpos, findpos + len(cursorTag))
                            self.ReplaceSelection('')
                            endSelectionPos = findpos
                            if startSelectionPos is None:
                                startSelectionPos = findpos
                            minPos = findpos
                            maxPos -= len(cursorTag)
                        else:
                            break
                    if startSelectionPos is not None and endSelectionPos is not None:
                        self.SetSelection(startSelectionPos, endSelectionPos)
                        boolHighlightQuestionMarks = False
            else:
                preset = self.CreateDefaultPreset(filtername)
                self.SetSelection(startwordpos, pos)
                self.ReplaceSelection(preset)
            if boolHighlightQuestionMarks:
                minPos = self.WordEndPosition(pos,1)
                maxPos = self.GetCurrentPos()
                findpos = self.FindText(minPos, maxPos, '?')#, stc.STC_FIND_MATCHCASE)
                if findpos != -1:
                    self.SetSelection(findpos, findpos+1)
            return
        args = self.avsfilterdict[filtername.lower()][0]
        if not args:
            return
        if args == '()':
            self.InsertText(pos,'()')
            self.GotoPos(pos+2)
            return
        level = self.app.options['autoparentheses']
        if unichr(self.GetCharAt(pos)) == '(':
            level = 0
        if level==0:
            pass
        elif level==1:
            self.InsertText(pos,'(')
            self.GotoPos(pos+1)
        elif level==2:
            self.InsertText(pos,'()')
            self.GotoPos(pos+1)

    def AutocompleteFilename(self):
        """Autocomplete a filename string, showing choices if necessary"""
        pos = self.GetCurrentPos()
        str_range = self.GetStringRange(pos)
        if not str_range:
            return
        start, end = str_range
        if self.GetStyleAt(start) == self.STC_AVS_TRIPLE: # only current line
            line = self.LineFromPosition(pos)
            start = max(start, self.PositionFromLine(line))
            end = min(end, self.GetLineEndPosition(line))
        ac_str = self.GetTextRange(start, pos)
        prefix = '' if os.path.isabs(ac_str) else self.workdir
        if os.path.isdir(os.path.join(prefix, ac_str)):
            dir = ac_str
            base = ''
        else:
            dir, base = os.path.split(ac_str)
        try:
            filenames = sorted([path for path in os.listdir(os.path.join(prefix, dir) or unicode(os.curdir))
                                if not base or os.path.normcase(path).startswith(os.path.normcase(base))],
                               key=lambda s: s.upper())
        except OSError:
            return
        if filenames:
            if len(filenames) == 1:
                self.AutocompleteReplaceText(start, end, prefix, os.path.join(dir, filenames[0]))
            else:
                self.autocomplete_params = pos, start, end, prefix, dir
                if self.app.options['autocompleteicons']:
                    filenames = [u'{0}?{1}'.format(file, 5 if os.path.isdir(os.path.join(prefix, dir, file))
                                 else 6) for file in filenames]
                self.autocomplete_case = 'filename'
                self.AutoCompStops('')
                self.AutoCompShow(len(base), '\n'.join(filenames))
                if self.CallTipActive():
                    self.CallTipCancelCustom()

    def AutocompleteReplaceText(self, start, end, prefix, new_text):
        """Used on filename autocomplete, instead of the default handler"""
        if new_text != self.GetTextRange(start, end):
            self.SetTargetStart(start)
            self.SetTargetEnd(end)
            new_end = start + self.ReplaceTarget(new_text)
            self.GotoPos(new_end)
        else:
            self.GotoPos(end)
        if os.path.isdir(os.path.join(prefix, new_text)):
            def autocomplete_again():
                wx.GetApp().Yield(True)
                self.AutocompleteFilename()
            wx.CallAfter(autocomplete_again)

    def AutocompleteParameterName(self):
        """Autocomplete parameter name in a function call"""
        pos = self.GetCurrentPos()
        openpos = self.GetOpenParenthesesPos(pos - 1)
        if openpos is None:
            return
        wordstartpos = self.WordStartPosition(openpos, 1)
        if openpos == wordstartpos:
            wordstartpos = self.WordStartPosition(self.WordStartPosition(openpos, 0), 1)
        if wordstartpos != -1:
            matched_args = {}
            arg_start_pos = self.WordStartPosition(pos, 1)
            chrs = self.GetTextRange(arg_start_pos, pos).lower()
            function_name = self.GetTextRange(wordstartpos, openpos).strip()
            args_script = [arg[0].lower() for arg in self.GetFilterScriptArgInfo(openpos) or []]
            for arg_type, arg_name, arg_info in ((arg[1], arg[2].strip('"'), arg[5]) for arg in
                             self.GetFilterCalltipArgInfo(function_name) or []
                             if arg[2].startswith('"') and arg[2].endswith('"')):
                arg_name_lower = arg_name.lower()
                if arg_name_lower.startswith(chrs) and arg_name_lower not in args_script:
                    matched_args[arg_name] = arg_type, arg_info
            if matched_args:
                if len(matched_args) == 1:
                    arg_name, (arg_type, arg_info) = matched_args.items()[0]
                    if unichr(self.GetCharAt(pos)) == '=':
                        new_text = arg_name
                    else:
                        new_text = arg_name + '='
                    self.SetTargetStart(arg_start_pos)
                    self.SetTargetEnd(self.WordEndPosition(pos, 1))
                    self.GotoPos(arg_start_pos + self.ReplaceTarget(new_text))
                    self.AutocompleteParameterValue(arg_type, arg_info)
                else:
                    args = matched_args.keys()
                    args.sort(key=lambda s: s.upper())
                    self.autocomplete_case = 'parameter name'
                    self.autocomplete_params = matched_args
                    self.AutoCompStops(self.AutoCompStops_chars)
                    self.AutoCompShow(len(chrs), '\n'.join(args))
                    if self.CallTipActive():
                        self.CallTipCancelCustom()

    def AutocompleteParameterValue(self, arg_type=None, arg_info=None):
        """Autocomplete parameter name in a function call"""
        if arg_type is None or arg_info is None:
            pos = self.GetCurrentPos()
            openpos = self.GetOpenParenthesesPos(pos - 1)
            if openpos is None:
                return
            wordstartpos = self.WordStartPosition(openpos, 1)
            if openpos == wordstartpos:
                wordstartpos = self.WordStartPosition(self.WordStartPosition(openpos, 0), 1)
            if wordstartpos != -1:
                matched_args = self.GetFilterMatchedArgs(wordstartpos)[self.cursorFilterScriptArgIndex][1]
                arg_info = self.GetFilterCalltipArgInfo(calltip=matched_args)[0]
                arg_type, arg_info = arg_info[1], arg_info[-1]
        if arg_type is not None and arg_info is not None:
            value_list = self.GetParameterValues(arg_type, arg_info)
            if value_list:
                self.autocomplete_case = 'parameter value'
                self.AutoCompStops('')
                self.AutoCompShow(0, '\n'.join(value_list))
                if self.CallTipActive():
                    self.CallTipCancelCustom()

    @staticmethod
    def GetParameterValues(arg_type, arg_info):
        if arg_type == 'bool':
            return ['true', 'false']
        elif arg_type in ('int', 'string'):
            if arg_type == 'string' and arg_info.startswith('"'):
                arg_info = arg_info[arg_info[1:].index('"') + 2:]
            start = arg_info.find('(')
            if start == -1:
                return
            arg_info = arg_info[start + 1:]
            value_list = [value.strip() for value in
                          arg_info.strip(' )').split('/')]
            if len(value_list) > 1:
                return value_list

    def InsertSnippet(self):
        pos = self.GetCurrentPos()
        start = self.WordStartPosition(pos, 1)
        end = self.WordEndPosition(pos, 1)
        word = self.GetTextRange(start, end)
        if word in self.app.options['snippets']:
            text = self.app.options['snippets'][word]
            if text:
                self.SetTargetStart(start)
                self.SetTargetEnd(end)
                self.GotoPos(start + self.ReplaceTarget(text))
        else:
            if self.AutoCompActive():
                self.CmdKeyExecute(wx.stc.STC_CMD_CANCEL)
                if self.autocomplete_case == 'snippet':
                        return
            tag_list = [tag for tag, text in self.app.options['snippets'].iteritems() if text]
            if tag_list:
                self.autocomplete_case = 'snippet'
                self.autocomplete_params = pos
                self.UserListShow(1, '\n'.join(sorted(tag_list)))

    def UpdateCalltip(self, force=False):
        caretPos = self.GetCurrentPos()
        # Cancel under certain conditions
        boolHasFocus = (self.app.FindFocus() == self)
        boolIsComment = (self.GetStyleAt(caretPos - 1) in self.commentStyle)
        if not self.app.options['calltips'] or not boolHasFocus or self.AutoCompActive() or boolIsComment:
            self.CallTipCancelCustom()
            return
        # Determine the positions of the filter within the script
        openpos = self.GetOpenParenthesesPos(caretPos-1)
        if openpos is None:
            if force:
                openpos = self.WordEndPosition(caretPos,1) #+ 1
            else:
                self.CallTipCancelCustom()
                return
        closepos = self.BraceMatch(openpos)
        if closepos == -1:
            closepos = self.GetLength()
        # Set the force flag to true if there's an appropriate highlight
        selA, selB = self.GetSelection()
        if selA != selB:
            if selA >= openpos and selB <= closepos+1:
                force = True
            else:
                self.CallTipCancelCustom()
                return
        startwordpos = self.WordStartPosition(self.WordStartPosition(openpos, 0), 1)
        endwordpos = self.WordEndPosition(startwordpos, 1)
        # Show the calltip
        self.calltipFilter = None
        word = self.GetTextRange(startwordpos, endwordpos)
        iArgPos = None
        #~ if word.lower() in self.filterDict:
        if self.GetStyleAt(startwordpos) in self.highlightwordStyleList:
            # Show the calltip
            wordWidth = self.TextWidth(stc.STC_STYLE_DEFAULT, '%s(' % word)
            spaceWidth = self.TextWidth(stc.STC_STYLE_DEFAULT, ' ')
            spaces = ' ' * int(round(wordWidth / float(spaceWidth)))
            #~ args = self.FilterNameArgs[word.lower()]
            args = self.avsfilterdict[word.lower()][0]
            if args  in ('', '()'):
                self.CallTipCancelCustom()
                self.calltipFilter = word
                return
            # Get the argument index based on the cursor position
            self.cursorFilterScriptArgIndex = None
            filterMatchedArgs = self.GetFilterMatchedArgs(startwordpos, args)
            try:
                iArgPos = filterMatchedArgs[self.cursorFilterScriptArgIndex][0]
            except IndexError:
                iArgPos = None
            boolOutOfOrder = False
            if iArgPos is not None:
                currentArgName = filterMatchedArgs[self.cursorFilterScriptArgIndex][2]
                if not currentArgName:
                    for item in filterMatchedArgs[:self.cursorFilterScriptArgIndex]:
                        if item[2]:
                            boolOutOfOrder = True
                            break
            # TODO: fix iArgPos to not be None if unfinished arg...?
            # Format the calltip
            splitargs = args.split('\n\n', 1)
            tempList = []
            for iTemp, tempInfo in enumerate(self.GetFilterCalltipArgInfo(calltip=splitargs[0])):
                cArgTotal, cArgType, cArgName, boolMulti, boolOptional, cArgInfo = tempInfo
                s = '%s %s' % (cArgType, cArgName)
                if iTemp == iArgPos and cArgInfo and not boolOutOfOrder:
                    s += '=%s' % cArgInfo
                if boolMulti:
                    s += ' [, ...]'
                tempList.append(s)
            args0 = '(%s)' % (','.join(tempList))
            args0 = self.app.wrapFilterCalltip(args0)
            args0 = args0.replace('\n', '\n'+spaces)
            if len(splitargs) == 2:
                args = '%s\n\n%s' % (args0, splitargs[1])
            else:
                args = args0
            text = '%s%s' % (word, args)
            if self.LineFromPosition(startwordpos) == self.GetCurrentLine():
                showpos = startwordpos
            else:
                showpos = self.PositionFromLine(self.LineFromPosition(caretPos))
            xpoint, ypoint = self.PointFromPosition(showpos)
            #~ if text != self.calltiptext:
                #~ self.CallTipCancelCustom()
                #~ return
            if openpos == self.calltipOpenpos or self.flagTextChanged:
                force = True
            if self.app.options['frequentcalltips'] or force:# or (charBefore and unichr(charBefore) == '('):
                if xpoint >= 0:
                    self.CallTipShow(showpos, text)
                else:
                    xpoint = self.GetMarginWidth(0) + self.GetMarginWidth(1) + self.GetMarginWidth(2)
                    newpos = self.PositionFromPoint(wx.Point(xpoint, ypoint))
                    self.CallTipShow(newpos, text)
            self.calltiptext = text
            self.calltipFilter = word
        if self.CallTipActive():
            self.calltipOpenpos = openpos
            # BOLD THE CURRENT ARGUMENT
            a, b = 1,1
            if iArgPos is not None and not boolOutOfOrder:
                # Get the calltip arguments text positions
                try:
                    calltiptext = text
                except UnboundLocalError:
                    return
                openpos = calltiptext.find('(')
                if openpos == -1:
                    return
                argPosList = []
                startpos = openpos+1
                stoppos = startpos
                nopenSquare = 0
                argString = calltiptext[stoppos:]
                imax = len(argString)-1
                for i, c in enumerate(argString):
                    if c == '[':
                        nopenSquare += 1
                    if c == ']':
                        nopenSquare -= 1
                    if nopenSquare > 0:
                        c = 'x'
                    if c == ',' or i == imax:
                        argPosList.append((startpos, stoppos))
                        startpos = stoppos + 1
                    stoppos += 1
                if len(argPosList) == 1 and iArgPos == 1:
                    pass
                else:
                    try:
                        a, b = argPosList[iArgPos]
                    except IndexError:
                        if __debug__:
                            print>>sys.stderr, 'Error in UpdateCalltip: invalid iArgPos'
            self.CallTipSetHighlight(a,b)
        else:
            self.calltipOpenpos = None

    def CallTipCancelCustom(self):
        self.CallTipCancel()
        self.calltipFilter = None
        self.calltiptext = None
        self.calltipOpenpos = None

    def GetOpenParenthesesPos(self, pos):
        boolInside = False
        nclose = 1
        stylesToSkip = (self.STC_AVS_STRING, self.STC_AVS_TRIPLE, self.STC_AVS_USERSLIDER)
        while pos >= 0:
            c = unichr(self.GetCharAt(pos))
            if self.GetStyleAt(pos) not in stylesToSkip:
                if c == ')':
                    nclose += 1
                if c == '(':
                    nclose -= 1
                if c == '\n':
                    current = self.GetLine(self.LineFromPosition(pos)).strip()
                    next = self.GetLine(self.LineFromPosition(pos+1)).strip()
                    if not current.endswith('\\') and not next.startswith('\\'):
                        # this is a not a multiline statement
                        # either an error or we weren't inside a function call to begin with
                        return None
            if nclose == 0:
                if self.GetStyleAt(pos) in self.commentStyle:
                    return None
                else:
                    return pos
            pos -= 1
        return None

    def GetFilterMatchedArgs(self, startwordpos, calltip=None):
        if calltip is None:
            filterName = self.GetTextRange(startwordpos, self.WordEndPosition(startwordpos, 1))
            calltip = self.avsfilterdict[filterName.lower()][0].split('\n\n')[0]
        # Get both argument lists
        filterCalltipArgInfo = self.GetFilterCalltipArgInfo(calltip=calltip)
        filterScriptArgInfo = self.GetFilterScriptArgInfo(startwordpos, calltip=calltip)
        # Determine if clip passed via "dot" operator
        isClipPrePassed = False
        try:
            firstType = filterCalltipArgInfo[0][1]
        except IndexError:
            return []
        if firstType == 'clip':
            preText = self.GetAviSynthLine(startwordpos, preSectionOnly=True)
            if preText.strip().endswith('.'):
                isClipPrePassed = True
            elif filterScriptArgInfo is not None and filterScriptArgInfo[0][1] == '?':
                isClipPrePassed = True
            else:
                lastClipIndex = 0
                for i, argInfo in enumerate(filterCalltipArgInfo):
                    if argInfo[1] != 'clip':
                        break
                    lastClipIndex = i
                try:
                    if filterScriptArgInfo is not None:
                        if filterScriptArgInfo[lastClipIndex][2] not in ('clip', 'var'):
                            isClipPrePassed = True
                    else:
                        isClipPrePassed = True
                except IndexError:
                    pass
        clipOffset = int(isClipPrePassed)
        if filterScriptArgInfo is None:
            return [(clipOffset, '', '', '')]
        # Match arguments
        calltipArgNames = [info[2].strip('"').lower() for info in filterCalltipArgInfo]
        maxCalltipIndex = len(filterCalltipArgInfo) - 1
        multiType = None
        multiIndex = None
        for index, calltipInfo in enumerate(filterCalltipArgInfo):
            cArgTotal, cArgType, cArgName, cBoolMulti, boolOptional, cArgInfo = calltipInfo
            if cBoolMulti:
                multiType = cArgType
                multiIndex = index
                postMultiIndex = index
                # TODO: handle multiple multiTypes...
                break
        filterArgInfo = []
        for scriptArgIndex, argInfo in enumerate(filterScriptArgInfo):
            argname, argvalue, argtype = argInfo
            if argname:
                # Check named arguments
                try:
                    calltipIndex = calltipArgNames.index(argname.lower())
                except ValueError:
                    calltipIndex = None
            else:
                calltipIndex = scriptArgIndex + clipOffset
                # Check for multi-arg possibility
                if multiIndex is not None and calltipIndex > multiIndex:
                    if argtype in (multiType, 'var'):
                        calltipIndex = multiIndex
                    else:
                        multiType = None
                        postMultiIndex += 1
                        calltipIndex = postMultiIndex
                if calltipIndex > maxCalltipIndex:
                    calltipIndex = None
                    continue
            if calltipIndex is not None:
                calltipFilterInfo = filterCalltipArgInfo[calltipIndex][0]
            else:
                calltipFilterInfo = ''
            filterArgInfo.append((calltipIndex, calltipFilterInfo, argname, argvalue))
        return filterArgInfo

    def GetFilterScriptArgInfo(self, startwordpos, calltip=None):
        openpos = self.FindText(startwordpos, self.GetTextLength(), '(')
        if openpos == -1:
            self.cursorFilterScriptArgIndex = 0
            return None
        # Grab the text line from the script
        line = self.LineFromPosition(openpos)
        posStart = openpos - self.PositionFromLine(line)
        iArg = 0
        pos1 = openpos
        posEnd = None
        while pos1 < self.GetLength():
            if unichr(self.GetCharAt(pos1)) == '(':
                posEnd = self.BraceMatch(pos1)
                if posEnd == -1:
                    posEnd = self.GetLineEndPosition(line) #self.GetLength()
                pos1 += 1
                break
            pos1 += 1
        if posEnd is None:
            self.cursorFilterScriptArgIndex = 0
            return None
        if pos1 == posEnd:
            self.cursorFilterScriptArgIndex = 0
            return None #[('','','')]
        currentPos = self.GetCurrentPos()
        currentIndex = None
        argsList = []
        counter = 0
        pos2 = self.GetNextValidCommaPos(pos1, allowparentheses=False)
        while pos2 is not None and pos2 <= posEnd:
            txt = self.GetTextRange(pos1,pos2).strip()
            argsList.append(txt)
            if pos2 >= currentPos and currentIndex is None:
                currentIndex = counter
            counter += 1
            pos1 = pos2 + 1
            pos2 = self.GetNextValidCommaPos(pos1, allowparentheses=False)
        if currentIndex is None:
            currentIndex = counter
        txt = self.GetTextRange(pos1,posEnd).strip()
        argsList.append(txt)
        argInfo = []
        for txt in argsList:
            try:
                argname, argvalue = [s.strip() for s in txt.split('=', 1)]
                argname = argname.strip(string.whitespace+'\\')
                argvalue = argvalue.strip(string.whitespace+'\\')
                argtype = 'named'
            except ValueError:
                argname = u''
                argvalue = txt
                argname = argname.strip(string.whitespace+'\\')
                argvalue = argvalue.strip(string.whitespace+'\\')
                argtype = self.GetAviSynthVarType(argvalue)
            #~ argname = argname.strip(string.whitespace+'\\')
            #~ argvalue = argvalue.strip(string.whitespace+'\\')
            argInfo.append((argname, argvalue, argtype))
        self.cursorFilterScriptArgIndex = currentIndex
        return argInfo

    def GetFilterCalltipArgInfo(self, word=None, calltip=None, ignore_opt_args=False):
        if calltip is None:
            # Get the user slider info from the filter's calltip
            try:
                calltip = self.avsfilterdict[word.lower()][0].split('\n\n')[0]
            except KeyError:
                return
        # Delete open and close parentheses
        if calltip.startswith('(') and calltip.endswith(')'):
            calltip = calltip[1:-1]
        elif calltip.startswith('('):
            calltip = calltip[1:]
        elif calltip.endswith(')'):
            calltip = calltip[:-1]

        # Delete/mark optional arguments
        new_calltip = []
        for arg in calltip.split(','):
            arg = arg.strip()
            if arg.startswith('[') and arg.endswith(']'):
                if not ignore_opt_args:
                    new_calltip.append(arg[1:-1] + 'OPT')
            else:
                new_calltip.append(arg)
        calltip = ', '.join(new_calltip)

        # Get rid of any commas in square brackets
        calltip = re.sub(r'\[.*\]', '[...]', calltip)

        # Split the arguments by commas
        argInfo = []
        for item in calltip.split(','):
            item = item.strip()
            if not item.strip():
                continue
            if item.count('[...]') > 0:
                boolMulti = True
                item = item.replace('[...]', '')
            else:
                boolMulti = False
            if item.endswith('OPT'):
                boolOptional = True
                item = item[:-3]
            else:
                boolOptional = False
            try:
                argtype, nameAndInfo = [s.strip() for s in item.split(' ', 1)]
                try:
                    name, info = [s.strip() for s in nameAndInfo.split('=', 1)]
                except ValueError:
                    name = nameAndInfo
                    info = u''
                argInfo.append((item, argtype.lower(), name, boolMulti, boolOptional, info))
            except ValueError:
                if item.lower() in ('clip', 'int', 'float', 'bool', 'string'):
                    argInfo.append((item, item.lower(), u'', boolMulti, boolOptional, u''))
                else:
                    # Assume it's a clip
                    argInfo.append((item, u'clip', item, boolMulti, boolOptional, u''))
        return argInfo

    def CreateDefaultPreset(self, filtername, calltip=None):
        if calltip is None:
            calltip = self.avsfilterdict[filtername.lower()][0].split('\n\n')[0]
        if calltip == '':
            return filtername
        argList = []
        for i, info in enumerate(self.GetFilterCalltipArgInfo(filtername, calltip, ignore_opt_args=True)):
            totalInfo, cArgType, cArgName, boolRepeatArg, boolOptionalArg, cArgInfo = info
            argtype, argname, guitype, defaultValue, other = self.app.ParseCalltipArgInfo(totalInfo)
            namedarg = ''
            if cArgName.startswith('"') and cArgName.endswith('"'):
                namedarg = cArgName.strip('"')+'='
            #~ if defaultValue is not None:
            if defaultValue or defaultValue == 0:
                if guitype == 'color':
                    argList.append('%s$%s' % (namedarg, defaultValue))
                elif argtype in ('float', 'int') and guitype == 'slider' and other is not None:
                    nDecimal = other[2]
                    strTemplate = '%.'+str(nDecimal)+'f'
                    try:
                        argList.append(namedarg+strTemplate % defaultValue)
                    except (TypeError, ValueError):
                        re_clip = re.compile(r'\bclip\b', re.I)
                        defaultValue = re_clip.sub('last', str(defaultValue))
                        argList.append(namedarg+defaultValue)
                else:
                    argList.append(namedarg+str(defaultValue))#.lower())
            elif argtype == 'clip' and i == 0:
                pass   # argList.append('last')
            else:
                argList.append(namedarg+'?')
        return '%s(%s)' % (filtername, ', '.join(argList))

    def GetAviSynthLine(self, pos, preSectionOnly=False, postSectionOnly=False):
        '''Returns the line of text at pos, accommodating for AviSynth line continuations'''
        linenumber = self.LineFromPosition(pos)
        if preSectionOnly:
            lines = [self.GetLine(linenumber)[:pos-self.PositionFromLine(linenumber)]]
        elif postSectionOnly:
            lines = [self.GetLine(linenumber)[pos-self.PositionFromLine(linenumber):]]
        else:
            lines = [self.GetLine(linenumber)]
        if not postSectionOnly:
            iLine = linenumber - 1
            while iLine >= 0:
                linetxt = self.GetLine(iLine)
                if lines[0].strip().startswith('\\') or linetxt.strip().endswith('\\'):
                    lines.insert(0, linetxt)
                else:
                    break
                iLine -= 1
        if not preSectionOnly:
            maxlinenumber = self.GetLineCount() - 1
            iLine = linenumber + 1
            while iLine <= maxlinenumber:
                linetxt = self.GetLine(iLine)
                if lines[-1].strip().endswith('\\') or linetxt.strip().startswith('\\'):
                    lines.append(linetxt)
                else:
                    break
                iLine += 1
        return ' '.join([s.strip().strip('\\') for s in lines])

    def GetAviSynthVarType(self, strVar):
        strVar = strVar.strip()
        if not strVar:
            return 'empty'
        # Check int
        if strVar.isdigit():
            return 'int'
        # Check float
        try:
            float(strVar)
            return 'float'
        except ValueError:
            pass
        # Check hex number
        if strVar.startswith('$'):
            return 'hex'
        # Check boolean
        if strVar.lower() in ('true', 'false'):
            return 'bool'
        # Check string
        if strVar.startswith('"') and strVar.endswith('"'):
            return 'string'
        if strVar.startswith('"'):
            # Incomplete string...
            return 'string'
        # Check if it's a named argument
        if strVar.count('=') > 0:
            return 'named'
        # Check if it's the Avisynth variable last
        if strVar.lower() == 'last':
            return 'clip'
        # Heuristic...
        if strVar.count('.') > 0:
            name = strVar.split('.')[-1].split('(')[0].lower()
            if name in ('width', 'height', 'framecount'):
                return 'int'
            elif name in ('framerate',):
                return 'float'
            elif name.startswith('is'):
                return 'bool'
        # If none of the above, it's a variable name
        if self.AVI is not None:
            vartype = self.AVI.GetVarType(strVar)
            if vartype in ('int', 'float', 'string', 'bool'):
                return vartype
        return 'var'

    def GetNextValidCommaPos(self, pos, checkChar=',', allowparentheses=False):
        #~ txt = self.GetTextRange(pos, self.GetLength())
        #~ newPos = pos
        #~ for c in txt:
            #~ if c == ',':
                #~ if self.GetStyleAt(newPos) not in (self.STC_AVS_STRING, self.STC_AVS_TRIPLE, self.STC_AVS_USERSLIDER):
                    #~ return newPos
            #~ newPos += 1
        nOpen = 0
        while pos <= self.GetLength():
            c = unichr(self.GetCharAt(pos))
            if c == '(' and not allowparentheses:
                pos = self.BraceMatch(pos)
                if pos == wx.NOT_FOUND:
                    return None
                continue
            if c == checkChar:
                if self.GetStyleAt(pos) not in (self.STC_AVS_STRING, self.STC_AVS_TRIPLE, self.STC_AVS_USERSLIDER, self.STC_AVS_COMMENT):
                    return pos
            pos += 1
        return None

    def ShowFilterDocumentation(self, name=None):
        if name is None:
            name = self.calltipFilter
        if not name:
            return
        docsearchpaths = []
        avisynthdir = self.app.ExpandVars(self.app.avisynthdir)
        docsearchpathstring = self.app.ExpandVars(self.app.options['docsearchpaths'])
        for path in docsearchpathstring.split(';'):
            path = path.strip()
            if os.path.isdir(path):
                docsearchpaths.append(path)
        extensions = ['.htm', '.html', '.txt', '.lnk', '']

        def get_names(name):
            name = name.lower()
            if name in self.avsfilterdict:
                display_name = self.avsfilterdict[name][2]
                if self.avsfilterdict[name][1] == AvsStyledTextCtrl.STC_AVS_PLUGIN:
                    is_short = self.avsfilterdict[name][3]
                    if is_short:
                        long_name = self.avsfilterdict[is_short][2]
                        short_name = display_name
                    else:
                        long_name = display_name
                        short_name = self.app.GetPluginFunctionShortName(long_name)
                    yield long_name[:-len(short_name) - 1]
                    yield short_name
                    yield long_name
                else:
                    yield display_name

        for find_name in get_names(name):
            for dir in docsearchpaths:
                filenames = []
                for filename in os.listdir(dir):
                    base, ext = os.path.splitext(filename)
                    if ext in extensions:
                        if re.findall(r'(\b|[_\W]|readme)%s(\b|[_\W]|readme)' % find_name, base, re.IGNORECASE):
                            filenames.append((extensions.index(ext), filename))
                if filenames:
                    filenames.sort()
                    filename = os.path.join(dir, filenames[0][1])
                    startfile(filename)
                    return True
        url = self.app.options['docsearchurl'].replace('%filtername%', name.replace('_', '+'))
        startfile(url)
        return False

    def GetFilterNameAtCursor(self, pos=None):
        if self.calltipFilter is not None:
            word = self.calltipFilter
        else:
            if pos is None:
                pos = self.GetCurrentPos()
            posA = self.WordStartPosition(pos, 1)
            posB = self.WordEndPosition(pos, 1)
            word = self.GetTextRange(posA, posB)
        return word

    def IsString(self, pos):
        if pos == self.GetTextLength():
            return self.IsString(pos - 1)
        return self.GetStyleAt(pos) in (self.STC_AVS_STRING, self.STC_AVS_TRIPLE, self.STC_AVS_STRINGEOL)

    def GetStringRange(self, pos):
        if not self.IsString(pos):
            return
        start = end = pos
        last_pos = self.GetTextLength()
        if pos == last_pos:
            start -= 1
        else:
            while end + 1 <= last_pos and self.IsString(end + 1):
                end += 1
        while start - 1 >= 0 and self.IsString(start - 1):
            start -= 1
        if self.GetStyleAt(start) == self.STC_AVS_TRIPLE:
            start += 3
            if self.GetStyleAt(end) != self.STC_AVS_STRINGEOL and end != last_pos:
                end -= 2
        else:
            start += 1
        return start, end

    def GenerateHTML(self, title=None, ext_css=None):
        """Return a HTML version of the text in the stc

        'ext_css' can be a filename for linking to an external style sheet.
        In that case a tuple (html, css) is returned
        """

        # Override face and size with the monospace font if used
        if self.app.options['usemonospacedfont']:
            monospaced = self.GenerateCSSBlock('monospaced', join=False)
            face = monospaced[self.css_properties['face']]
            size = monospaced[self.css_properties['size']]
            monospaced = face, size
        else:
            monospaced = None

        # Generate the body of the html and the style sheet
        # a complete sheet if external, otherwise only the needed styles
        # without inheritable declarations
        body = list()
        if not ext_css:
            default_css = self.GenerateCSSBlock('default', join=False,
                                                monospaced=monospaced)
            css = {'default': self.JoinCSSBlock('default', default_css)}
            default_css = default_css.items()
        last_style = self.GetStyleAt(0)
        style_start = 0
        length = self.GetLength()
        if not length:
            return
        for pos in xrange(0, length + 1):
            if pos != length:
                style = self.GetStyleAt(pos)
                if style == last_style:
                    continue
            style_name = self.styleInfo[last_style][0]
            if not ext_css and style_name not in css:
                css[style_name] = self.GenerateCSSBlock(style_name, default_css,
                                                        monospaced=monospaced)
            text = cgi.escape(self.GetTextRange(style_start, pos), True)
            if style_name != 'default':
                text = u'<span class="{0}">{1}</span>'.format(style_name, text)
            body.append(text)
            last_style = style
            style_start = pos
        body = u'<body>\n<pre class="default">\n{0}\n</pre>\n</body>'.format(
                                                                  ''.join(body))
        css =  self.GenerateCSS(monospaced=monospaced) if ext_css else \
               '\n'.join(css.values())

        # Generate the head, inserting the css if required
        title = cgi.escape(title or _('AviSynth script'), True)
        generator = cgi.escape(u'{0} v{1}'.format(global_vars.name,
                               global_vars.version), True)
        if ext_css:
            head_css = u'<link rel="stylesheet" type="text/css" '\
                        'href="{0}">'.format(ext_css)
        else:
            head_css = u'<style type="text/css">\n{0}\n</style>'.format(css)
        head = textwrap.dedent(u'''\
            <!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01//EN"
            "http://www.w3.org/TR/html4/strict.dtd">
            <html>
            <head>
            <meta http-equiv="content-type" content="text/html; charset=utf-8">
            <meta name="generator" content="{0}">
            <title>{1}</title>
            {2}
            </head>''').format(generator, title, head_css)

        # Return the html file, and optionally the style sheet
        html = u'{0}\n{1}\n</html>'.format(head, body)
        if ext_css:
            return html, css
        return html

    def GenerateCSS(self, monospaced=None):
        """Generate a style sheet from the styled text in the STC

        Override face and size with 'monospaced', if given
        """
        css = []
        for style, (key, extra) in self.styleInfo.iteritems():
            css.append(self.GenerateCSSBlock(key, monospaced=monospaced))
        return '\n'.join(css)

    def GenerateCSSBlock(self, style_name, default=None, monospaced=None, join=True):
        """Return a CSS block from a STC style

        Don't include in the block declarations in 'default', if given
        Override face and size with 'monospaced', if given
        """
        if not style_name in self.app.options['textstyles']:
            return ''
        if style_name == 'default' and default:
            default = None
        declarations = {}
        for attr in self.app.options['textstyles'][style_name].split(','):
            values = None
            splitted_attr = attr.split(':')
            if len(splitted_attr) == 1:
                if attr in self.stc_attr[0]:
                    values = self.css_properties[attr], attr
            elif len(splitted_attr) == 2:
                attr, value = splitted_attr
                if attr in self.stc_attr[1]:
                    if attr == 'face':
                        if monospaced:
                            value = monospaced[0]
                        else: # add fallback
                            if 'monospace' in style_name or 'string' in style_name:
                                fallback = 'monospace'
                            elif 'comment' in style_name:
                                fallback = 'serif'
                            else:
                                fallback = 'sans-serif'
                            value = u'"{0}", {1}'.format(value, fallback)
                    elif attr == 'size':
                        if monospaced:
                            value = monospaced[1]
                        else: # specify unit
                            value += 'pt'
                    values = self.css_properties[attr], value
            if values and (not default or values not in default):
                declarations[values[0]] = values[1]
        if join:
            return self.JoinCSSBlock(style_name, declarations)
        return declarations

    @staticmethod
    def JoinCSSBlock(css_class, css):
        """Generate a CSS block from a property: value dict"""
        declarations = []
        for property, value in css.iteritems():
            declarations.append(u"\n\t{0}: {1};".format(property, value))
        return u".{0} {{{1}\n}}".format(css_class, ''.join(declarations))

    # Event functions

    def OnUpdateUI(self, event):
        # Get the character before the caret
        charBefore = None
        caretPos = self.GetCurrentPos()
        if caretPos > 0:
            charBefore = self.GetCharAt(caretPos - 1)
        # Highlight braces
        braceAtCaret = -1
        braceOpposite = -1
        # check before
        if charBefore and unichr(charBefore) in "[]{}()":# and styleBefore == stc.STC_P_OPERATOR:
            braceAtCaret = caretPos - 1
        # check after
        if braceAtCaret < 0:
            charAfter = self.GetCharAt(caretPos)
            #~ styleAfter = self.GetStyleAt(caretPos)
            if charAfter and unichr(charAfter) in "[]{}()":# and styleAfter == stc.STC_P_OPERATOR:
                braceAtCaret = caretPos
        if braceAtCaret >= 0:
            braceOpposite = self.BraceMatch(braceAtCaret)
        #~ if braceAtCaret != -1:
        if braceOpposite == -1:
            self.BraceBadLight(braceAtCaret)
        else:
            self.BraceHighlight(braceAtCaret, braceOpposite)
        #~ if self.commentStyle in (self.GetStyleAt(braceAtCaret), self.GetStyleAt(braceAtCaret)):
        if self.GetStyleAt(braceAtCaret) in self.nonBraceStyles or self.GetStyleAt(braceOpposite) in self.nonBraceStyles:
            self.BraceHighlight(-1, -1)
        # Display call tips
        self.UpdateCalltip()
        self.flagTextChanged = False

    def x_CodeFolding(self):    # update folding level
        lineCount = self.GetLineCount()
        line = 0
        while line < lineCount:
            if self.GetFoldLevel(line) & stc.STC_FOLDLEVELHEADERFLAG:
                hasBrace = False
                hasBlock = False
                for pos in range(self.PositionFromLine(line), self.GetLineEndPosition(line)+1):
                    if unichr(self.GetCharAt(pos)) == '{' and self.GetStyleAt(pos) == self.STC_AVS_OPERATOR:
                        hasBrace = True
                        break
                if not hasBrace:
                    for pos in range(self.GetLineEndPosition(line), self.PositionFromLine(line)-1, -1):
                        if self.GetStyleAt(pos) == self.STC_AVS_BLOCKCOMMENT and self.GetStyleAt(pos-1) != self.STC_AVS_BLOCKCOMMENT:
                            hasBlock = True
                            break
                if hasBrace:
                    posMatch = self.BraceMatch(pos)
                    if posMatch != stc.STC_INVALID_POSITION:
                        lineEnd = self.LineFromPosition(posMatch) + 1
                        lastChild = self.GetLastChild(line, -1) + 1
                        if line+1 == lineEnd:
                            if not self.GetFoldExpanded(line):
                                self.SetFoldExpanded(line, True)
                                self.Expand(line, True)
                            self.SetFoldLevel(line, self.GetFoldLevel(line) & stc.STC_FOLDLEVELNUMBERMASK)
                    else:
                        lineEnd = lastChild = lineCount
                    level = (self.GetFoldLevel(line) & stc.STC_FOLDLEVELNUMBERMASK) + 1
                    for lineNum in range(line+1, lineEnd):
                        self.SetFoldLevel(lineNum, self.GetFoldLevel(lineNum) & 0xF000 | level)
                    for lineNum in range(lineEnd, lastChild):
                        self.SetFoldLevel(lineNum, self.GetFoldLevel(lineNum)-1)
                elif hasBlock:
                    end = pos
                    while self.GetStyleAt(end+1) == self.STC_AVS_BLOCKCOMMENT:
                        end += 1
                    lineEnd = self.LineFromPosition(end) + 1
                    lastChild = self.GetLastChild(line, -1) + 1
                    if line+1 == lineEnd:
                        if not self.GetFoldExpanded(line):
                            self.SetFoldExpanded(line, True)
                            self.Expand(line, True)
                        self.SetFoldLevel(line, self.GetFoldLevel(line) & stc.STC_FOLDLEVELNUMBERMASK)
                    else:
                        for lineNum in range(line+1, self.LineFromPosition(end)+1):
                            if self.GetFoldLevel(lineNum) & stc.STC_FOLDLEVELHEADERFLAG and not self.GetFoldExpanded(lineNum):
                                self.SetFoldExpanded(lineNum, True)
                                self.Expand(lineNum, True)
                        level = (self.GetFoldLevel(line) & stc.STC_FOLDLEVELNUMBERMASK) + 1
                        for lineNum in range(line+1, lineEnd):
                            self.SetFoldLevel(lineNum, self.GetFoldLevel(lineNum) & 0xF000 | level)
                        for lineNum in range(lineEnd, lastChild):
                            self.SetFoldLevel(lineNum, self.GetFoldLevel(lineNum)-1)
                elif self.GetStyleAt(self.PositionFromLine(line)) != self.STC_AVS_ENDCOMMENT and self.GetStyleAt(self.PositionFromLine(line+1)) == self.STC_AVS_ENDCOMMENT:
                    for lineNum in range(line+1, lineCount):
                        if self.GetFoldLevel(lineNum) & stc.STC_FOLDLEVELHEADERFLAG and not self.GetFoldExpanded(lineNum):
                            self.SetFoldExpanded(lineNum, True)
                            self.Expand(lineNum, True)
                        level = (self.GetFoldLevel(line) & stc.STC_FOLDLEVELNUMBERMASK) + 1
                    for lineNum in range(line+1, lineCount):
                        self.SetFoldLevel(lineNum, self.GetFoldLevel(lineNum) & 0xF000 | level)
                else:
                    if not self.GetFoldExpanded(line):
                        self.SetFoldExpanded(line, True)
                        self.Expand(line, True)
                    #~ else:
                        #~ lineNext = line + 1
                    for lineNum in range(line+1, self.GetLastChild(line, -1)+1):
                        self.SetFoldLevel(lineNum, self.GetFoldLevel(lineNum)-1)
                    self.SetFoldLevel(line, self.GetFoldLevel(line)&stc.STC_FOLDLEVELNUMBERMASK)
                    #~ line = lineNext - 1
            line += 1

    def OnTextChange(self, event):
        if self.app.options['numlinechars']:
            self.fitNumberMarginWidth()
        #~ self.UpdateCalltip(force=True)
        self.flagTextChanged = True

    def OnTextCharAdded(self, event):
        if unichr(event.GetKey()) == '\n':
            line = self.GetCurrentLine() - 1
            indentText = self.GetTextRange(self.PositionFromLine(line), self.GetLineIndentPosition(line))
            self.AddText(indentText)
            level = self.GetFoldLevel(line)
            if level & stc.STC_FOLDLEVELHEADERFLAG:
                self.SetFoldLevel(line + 1, level & stc.STC_FOLDLEVELNUMBERMASK)

    def OnNeedShown(self, event):
        line = self.LineFromPosition(event.GetPosition())
        lineEnd = self.LineFromPosition(event.GetPosition()+event.GetLength())
        while line < lineEnd:
            level = self.GetFoldLevel(line)
            if level & stc.STC_FOLDLEVELHEADERFLAG and not self.GetFoldExpanded(line):
                self.SetFoldExpanded(line, True)
                self.Expand(line, True)
            line += 1

    def OnKeyUp(self, event):
        pos = self.GetCurrentPos()
        #~ charCurrent = self.GetCharAt(pos-1)
        #~ charBefore = self.GetCharAt(pos-2)
        #~ charAfter= self.GetCharAt(pos)
        #~ isCurrentCap = unichr(charCurrent).isalpha() and unichr(charCurrent).isupper()#unichr(charCurrent).isalpha() and event.ShiftDown() #
        #~ isBeforeBlank = unichr(charBefore).isspace() or unichr(charBefore)=='.' or charBefore==0
        #~ isBeforeBlank = unichr(charBefore).isspace() or unichr(charBefore) in self.app.avsoperators or charBefore==0
        #~ isAfterBlank = unichr(charAfter).isspace() or unichr(charAfter)=='.' or charAfter==0
        #~ validChar = isCurrentCap and isBeforeBlank and isAfterBlank
        #~ isCommentStyle = self.commentStyle == self.GetStyleAt(pos - 1)
        #~ if self.app.options['autocomplete'] and validChar and not(self.AutoCompActive()) and not isCommentStyle:
            #~ keywords = self.app.avsazdict.get(unichr(charCurrent).lower(), [])[:]
            #~ for i in range(len(keywords)-1, -1, -1):
                #~ if keywords[i] in self.app.options['autocompleteexclusions']:
                    #~ del keywords[i]
            #~ if keywords:
                #~ self.AutoCompShow(1, '\n'.join(keywords))
        keys = (wx.WXK_ESCAPE, wx.WXK_RETURN, wx.WXK_NUMPAD_ENTER, wx.WXK_TAB)
        if event.GetKeyCode() not in keys\
        and not self.AutoCompActive()\
        and not (self.CallTipActive() and self.app.options['calltipsoverautocomplete'])\
        and self.GetStyleAt(pos-1) not in self.nonBraceStyles:
            start = self.WordStartPosition(pos,1)
            end = self.WordEndPosition(pos,1)
            char = unichr(self.GetCharAt(start))
            if pos == end:
                if self.app.options['autocomplete']\
                and (char.isalpha() and char.isupper() or char == '_')\
                and pos - start == self.app.options['autocompletelength']:
                    wx.CallAfter(self.ShowAutocomplete, auto=1)
                elif self.app.options['autocompletesingle'] and char.isalpha():
                    wx.CallAfter(self.ShowAutocomplete, auto=2)
        event.Skip()

    def OnKeyDown(self,event):
        key = event.GetKeyCode()
        #~ flags = event.GetModifiers()
        if (self.AutoCompActive() and self.autocomplete_case == 'function' and
            key in (wx.WXK_RETURN, wx.WXK_NUMPAD_ENTER, wx.WXK_TAB) and
            not (event.ControlDown() or event.AltDown() or event.ShiftDown())):
                self.FinishAutocomplete(key=key)
                #~ if key == wx.WXK_TAB:
                    #~ self.app.tab_processed = True
            #~ elif key == wx.WXK_TAB and mod == wx.MOD_NONE:
                #~ self.app.OnMenuEditIndentSelection()
            #~ elif key in (wx.WXK_RETURN, wx.WXK_NUMPAD_ENTER) and not event.ControlDown():
                #~ pos = self.GetCurrentPos()
                #~ line = self.LineFromPosition(pos)
                #~ indentText = self.GetTextRange(self.PositionFromLine(line), self.GetLineIndentPosition(line))
                #~ self.ReplaceSelection('\n'+indentText)
                #~ level = self.GetFoldLevel(line)
                #~ if level & stc.STC_FOLDLEVELHEADERFLAG:
                    #~ self.SetFoldLevel(line+1, level & stc.STC_FOLDLEVELNUMBERMASK)
        else:
            event.Skip()

    def OnMiddleDown(self,event):
        xypos = event.GetPosition()
        self.GotoPos(self.PositionFromPoint(xypos))

    def OnMouseMotion(self,event):
        if event.MiddleIsDown():
            self.OnMiddleDown(event)
        elif event.LeftIsDown():
            xypos = event.GetPosition()
            self.SetCurrentPos(self.PositionFromPoint(xypos))
        #~ else:
            #~ pass

    def OnLeftMouseDown(self, event):
        #~ self.CallTipCancelCustom()
        event.Skip()

    def OnAutocompleteSelection(self, event):
        if self.autocomplete_case == 'function':
            event.Skip() # processing on EVT_KEY_DOWN, because we need event.GetKeyCode()
        elif self.autocomplete_case == 'parameter name':
            self.BeginUndoAction()
            event.Skip()
            def post_autocomplete(arg_name):
                # add an equals sign
                pos = self.GetCurrentPos()
                if unichr(self.GetCharAt(pos)) == '=':
                    self.GotoPos(pos + 1)
                else:
                    self.AddText('=')
                self.EndUndoAction()
                # autocomplete parameter value
                matched_args = self.autocomplete_params
                self.AutocompleteParameterValue(*matched_args[arg_name])
            wx.CallAfter(post_autocomplete, event.GetText())
        elif self.autocomplete_case == 'parameter value':
            # AutoCompSetDropRestOfWord doesn't include quotes
            pos = self.GetCurrentPos()
            self.SetTargetStart(pos)
            while unichr(self.GetCharAt(pos)) in (' ', '?') or self.IsString(pos):
                pos += 1
            self.SetTargetEnd(pos)
            self.BeginUndoAction()
            self.ReplaceTarget('')
            event.Skip()
            wx.CallAfter(self.EndUndoAction)
        elif self.autocomplete_case == 'filename':
            self.AutoCompCancel()
            pos0, start, end0, prefix, dir = self.autocomplete_params
            self.AutocompleteReplaceText(start, end0 + self.GetCurrentPos() - pos0,
                                         prefix, os.path.join(dir, event.GetText()))

    def OnUserListSelection(self, event):
        if self.autocomplete_case == 'snippet':
            start, end = self.autocomplete_params, self.GetCurrentPos()
            self.SetTargetStart(start)
            self.SetTargetEnd(end)
            self.GotoPos(start + self.ReplaceTarget(self.app.options['snippets'][event.GetText()]))

    def OnCalltipClick(self, event):
        if wx.GetKeyState(wx.WXK_ALT) or wx.GetKeyState(wx.WXK_CONTROL) or wx.GetKeyState(wx.WXK_SHIFT):
            self.ShowFilterDocumentation()
        else:
            self.CallTipCancelCustom()

    def OnKillFocus(self, event):
        self.CallTipCancelCustom()
        self.AutoCompCancel()
        event.Skip()

    def OnSetFocus(self, event):
        self.UpdateCalltip()
        event.Skip()

    def OnStyleNeeded(self, event, forceAll=False):
        if forceAll:
            start = -1
            line = 0
            isCommentNest = 0
            end = self.GetLength()
        else:
            pos = self.GetEndStyled()
            line = self.LineFromPosition(pos)
            start = self.PositionFromLine(line) - 1
            if self.GetStyleAt(start) == self.STC_AVS_BLOCKCOMMENT:
                isCommentNest = self.GetLineState(line - 1)
            else:
                isCommentNest = 0
            if self.app.options['wrap']: # workaround
                end = self.GetLineEndPosition(line + self.LinesOnScreen()) + 1
            else:
                end = event.GetPosition()
        if start < 1:
            start = 0
            state = self.STC_AVS_DEFAULT
        else:
            state = self.GetStyleAt(start)
            if state == self.STC_AVS_STRINGEOL:
                start += 1
                state = self.STC_AVS_DEFAULT
        isLoadPlugin = False
        flag = None # True -> start, False -> end
        if line and self.GetFoldLevel(line - 1) & stc.STC_FOLDLEVELHEADERFLAG:
            prev_flag = True
        else:
            prev_flag = None
        self.endstyled = pos = start
        fragment = []
        hexfragment = []
        # vpy hack, remove when VapourSynth is supported (with a custom Python lexer)
        string_delimiters = ['"', "'"] if self.filename.endswith('.vpy') else '"'
        self.StartStyling(pos, 31)
        while pos <= end:
            ch = unichr(self.GetCharAt(pos))
            isEOD = (ch == unichr(0))
            isEOL = (ch == '\n' or ch == '\r' or isEOD)
            if state == self.STC_AVS_DEFAULT:
                if ch == '#':
                    state = self.STC_AVS_COMMENT
                elif ch == '/' and unichr(self.GetCharAt(pos+1)) == '*':
                    pos += 1
                    flag = True
                    state = self.STC_AVS_BLOCKCOMMENT
                elif ch in string_delimiters:
                    self.ColourTo(pos-1, state)
                    if unichr(self.GetCharAt(pos+1)) in string_delimiters and unichr(self.GetCharAt(pos+2)) in string_delimiters:
                        pos += 2
                        if self.app.options['syntaxhighlight_styleinsidetriplequotes']:
                            self.ColourTo(pos, self.STC_AVS_TRIPLE)
                        else:
                            triple_start = pos
                            state = self.STC_AVS_TRIPLE
                    else:
                        state = self.STC_AVS_STRING
                    if isLoadPlugin:
                        isLoadPlugin = pos
                elif ch == '$':
                    hexfragment = []
                    state = self.STC_AVS_NUMBERBAD
                elif ch == '[' and unichr(self.GetCharAt(pos+1)) == '*':
                    pos += 1
                    isCommentNest += 1
                    self.SetLineState(self.LineFromPosition(pos), isCommentNest)
                    flag = True
                    state = self.STC_AVS_BLOCKCOMMENT
                elif ch == '[' and unichr(self.GetCharAt(pos+1)) == '<':
                    pos += 1
                    state = self.STC_AVS_USERSLIDER
                elif ch.isalpha() or ch == '_' or ch in self.app.avssingleletters:
                    fragment = [ch]
                    state = self.STC_AVS_IDENTIFIER
                elif ch.isdigit():
                    state = self.STC_AVS_NUMBER
                elif ch in self.app.avsoperators:
                    self.ColourTo(pos - 1, state)
                    self.ColourTo(pos, self.STC_AVS_OPERATOR)
                    if ch == '{':
                        flag = True
                    elif ch == '}':
                        flag = None if flag else False
                else:
                    if isEOD:
                        self.ColourTo(pos - 1, self.STC_AVS_DEFAULT)
                    else:
                        self.ColourTo(pos, self.STC_AVS_DEFAULT)
            elif state == self.STC_AVS_COMMENT:
                if isEOL:
                    if isEOD:
                        self.ColourTo(pos - 1, self.STC_AVS_COMMENT)
                    else:
                        self.ColourTo(pos, self.STC_AVS_COMMENT)
                    state = self.STC_AVS_DEFAULT
            elif state == self.STC_AVS_BLOCKCOMMENT:
                if isEOD or pos == end:
                    self.ColourTo(pos - 1, self.STC_AVS_BLOCKCOMMENT)
                elif isEOL:
                    self.SetLineState(self.LineFromPosition(pos), isCommentNest)
                elif isCommentNest:
                    if ch == '*' and unichr(self.GetCharAt(pos+1)) == ']':
                        pos += 1
                        isCommentNest -= 1
                        self.SetLineState(self.LineFromPosition(pos), isCommentNest)
                        flag = None if flag else False
                        if not isCommentNest:
                            self.ColourTo(pos, self.STC_AVS_BLOCKCOMMENT)
                            state = self.STC_AVS_DEFAULT
                    elif ch == '[' and unichr(self.GetCharAt(pos+1)) == '*':
                        pos += 1
                        isCommentNest += 1
                        self.SetLineState(self.LineFromPosition(pos), isCommentNest)
                        flag = True
                elif ch == '*' and unichr(self.GetCharAt(pos+1)) == '/':
                    pos += 1
                    self.ColourTo(pos, self.STC_AVS_BLOCKCOMMENT)
                    flag = None if flag else False
                    state = self.STC_AVS_DEFAULT
            elif state == self.STC_AVS_IDENTIFIER:
                if fragment[0] not in self.app.avssingleletters and (ch.isalnum() or ch == '_'):
                    fragment.append(ch)
                else:
                    pos2 = pos
                    pos -= 1
                    word =''.join(fragment).lower()
                    while unichr(self.GetCharAt(pos2)) in (u' ', u'\t'):
                        pos2 += 1
                    ch2 = unichr(self.GetCharAt(pos2))
                    if word in self.app.avsdatatypes and unichr(self.GetCharAt(pos+1)).isspace():
                        self.ColourTo(pos, self.STC_AVS_DATATYPE)
                    elif word in self.app.avskeywords:
                        self.ColourTo(pos, self.STC_AVS_KEYWORD)
                    elif word in self.app.avsmiscwords:
                        self.ColourTo(pos, self.STC_AVS_MISCWORD)
                        if word == '__end__':
                            line = self.LineFromPosition(pos)
                            self.UpdateFolding(line, True, prev_flag)
                            level = (self.GetFoldLevel(line) & stc.STC_FOLDLEVELNUMBERMASK) + 1
                            for line in range(line + 1, self.LineFromPosition(end) + 1):
                                self.SetFoldLevel(line, level)
                            self.ColourTo(end, self.STC_AVS_ENDCOMMENT)
                            break
                    elif ch2 == u'(':
                        if word in self.avsfilterdict:
                            #~ self.ColourTo(pos, self.keywordstyles[word])
                            self.ColourTo(pos, self.avsfilterdict[word][1])
                            if word == 'loadplugin':
                                isLoadPlugin = True
                        else:
                            self.ColourTo(pos, self.STC_AVS_UNKNOWNFUNCTION)
                    elif ch2 == u'=' and unichr(self.GetCharAt(pos2 + 1)) != '=':
                        if self.GetOpenParenthesesPos(pos - len(word)):
                            self.ColourTo(pos, self.STC_AVS_PARAMETER)
                        else:
                            self.ColourTo(pos, self.STC_AVS_ASSIGN)
                    else:
                        if self.app.options['syntaxhighlight_preferfunctions'] and \
                                word in self.avsfilterdict:
                            #~ self.ColourTo(pos, self.keywordstyles[word])
                            self.ColourTo(pos, self.avsfilterdict[word][1])
                        else:
                            self.ColourTo(pos, self.STC_AVS_DEFAULT)
                    fragment = []
                    state = self.STC_AVS_DEFAULT
            elif state == self.STC_AVS_STRING:
                if self.app.options['usestringeol']:
                    if unichr(self.GetCharAt(pos-1)) in string_delimiters and unichr(self.GetCharAt(pos)) in string_delimiters and unichr(self.GetCharAt(pos+1)) in string_delimiters:
                        state = self.STC_AVS_TRIPLE
                        pos += 1
                    elif ch in string_delimiters or isEOL:
                        if isEOL:
                            if isEOD:
                                self.ColourTo(pos - 1, self.STC_AVS_STRINGEOL)
                            else:
                                self.ColourTo(pos, self.STC_AVS_STRINGEOL)
                            isLoadPlugin = False
                        else:
                            self.ColourTo(pos, self.STC_AVS_STRING)
                            if isLoadPlugin:
                                self.parseDllname(isLoadPlugin, pos)
                                isLoadPlugin = False
                        state = self.STC_AVS_DEFAULT
                else:
                    if unichr(self.GetCharAt(pos-1)) in string_delimiters and unichr(self.GetCharAt(pos)) in string_delimiters and unichr(self.GetCharAt(pos+1)) in string_delimiters:
                        state = self.STC_AVS_TRIPLE
                        pos += 1
                    elif ch in string_delimiters:
                        self.ColourTo(pos, self.STC_AVS_STRING)
                        state = self.STC_AVS_DEFAULT
                        if isLoadPlugin:
                            self.parseDllname(isLoadPlugin, pos)
                            isLoadPlugin = False
                    elif isEOD:
                        self.ColourTo(pos - 1, self.STC_AVS_STRING)
                        state = self.STC_AVS_DEFAULT
                        isLoadPlugin = False
            elif state == self.STC_AVS_TRIPLE:
                # AviSynth interprets """"""" as '"' etc.
                triple_quote_quirk = False
                if ch == '"' and pos - triple_start == 1:
                    last_quote_pos = pos
                    while unichr(self.GetCharAt(last_quote_pos)) == '"':
                        last_quote_pos += 1
                    quote_number = last_quote_pos - pos
                    if quote_number > 3:
                        pos += quote_number - 1 - 1
                        triple_quote_quirk = True
                if not triple_quote_quirk:
                    if isEOD or ((pos - triple_start > 2) and ch in string_delimiters and unichr(self.GetCharAt(pos-1)) in string_delimiters and unichr(self.GetCharAt(pos-2)) in string_delimiters):
                        self.ColourTo(pos, self.STC_AVS_TRIPLE)
                        state = self.STC_AVS_DEFAULT
                        if isLoadPlugin:
                            if not isEOD:
                                self.parseDllname(isLoadPlugin, pos)
                            isLoadPlugin = False
                    elif isEOL:
                        self.ColourTo(pos, self.STC_AVS_TRIPLE)
            elif state == self.STC_AVS_NUMBER:
                if not ch.isdigit():
                    pos -= 1
                    self.ColourTo(pos, self.STC_AVS_NUMBER)
                    state = self.STC_AVS_DEFAULT
            elif state == self.STC_AVS_NUMBERBAD:
                if ch.isalnum() or ch == '_':
                    hexfragment.append(ch)
                else:
                    pos -= 1
                    #~ if len(hexfragment) == 6 and sum([c.isdigit() or c.lower() in ('a', 'b', 'c', 'd', 'e', 'f') for c in hexfragment]) == 6:
                        #~ self.ColourTo(pos, self.STC_AVS_NUMBER)
                    #~ else:
                        #~ self.ColourTo(pos, self.STC_AVS_NUMBERBAD)
                    try:
                        int(''.join(hexfragment), 16)
                        self.ColourTo(pos, self.STC_AVS_NUMBER)
                    except:
                        self.ColourTo(pos, self.STC_AVS_NUMBERBAD)
                    hexfragment = []
                    state = self.STC_AVS_DEFAULT
            elif state == self.STC_AVS_USERSLIDER:
                if isEOL or (ch == ']' and unichr(self.GetCharAt(pos-1)) == '>'):
                    if isEOL:
                        self.ColourTo(pos, self.STC_AVS_NUMBERBAD)
                    else:
                        self.ColourTo(pos, self.STC_AVS_USERSLIDER)
                    state = self.STC_AVS_DEFAULT
            elif state == self.STC_AVS_ENDCOMMENT:
                line = self.LineFromPosition(pos)
                if self.GetStyleAt(self.PositionFromLine(line)) != self.STC_AVS_ENDCOMMENT:
                    line += 1
                level = (self.GetFoldLevel(line) & stc.STC_FOLDLEVELNUMBERMASK)
                for line in range(line, self.LineFromPosition(end) + 1):
                    self.SetFoldLevel(line, level)
                self.ColourTo(end, self.STC_AVS_ENDCOMMENT)
                break
            ch = unichr(self.GetCharAt(pos))
            if pos != start and (ch == unichr(0) or ch == '\n' or ch == '\r'):
                self.UpdateFolding(self.LineFromPosition(pos), flag, prev_flag)
                prev_flag = flag
                flag = None
            pos += 1
        if wx.VERSION > (2, 9):
            self.app.IdleCall.append((self.Refresh, tuple(), dict()))

    def ColourTo(self, pos, style):
        self.SetStyling(pos +1 - self.endstyled, style)
        self.endstyled = pos+1

    def parseDllname(self, start, end):
        path = self.GetTextRange(start, end).lower().strip('"')
        #~ print path
        ext = os.path.splitext(path)[1]
        if ext in ('.dll', '.so'):
            dllname = os.path.basename(path[:-len(ext)])
            if dllname.count('_') and dllname not in self.app.dllnameunderscored:
                self.app.dllnameunderscored.add(dllname)
                self.app.defineScriptFilterInfo()

    def UpdateFolding(self, line, flag, prev_flag):
        if line == 0:
            level = stc.STC_FOLDLEVELBASE
        else:
            level = self.GetFoldLevel(line - 1) & stc.STC_FOLDLEVELNUMBERMASK
            if prev_flag:
                level += 1
        if flag == True:
            level |= stc.STC_FOLDLEVELHEADERFLAG
        elif flag == False:
            level = max(stc.STC_FOLDLEVELBASE, level - 1)
        elif not self.GetLine(line).strip():
            level |=  stc.STC_FOLDLEVELWHITEFLAG
        self.SetFoldLevel(line, level)

    def OnMarginClick(self, evt):
        # fold and unfold as needed
        if evt.GetMargin() == 2:
            if evt.GetShift() and evt.GetControl():
                self.FoldAll()
            else:
                lineClicked = self.LineFromPosition(evt.GetPosition())

                if self.GetFoldLevel(lineClicked) & stc.STC_FOLDLEVELHEADERFLAG:
                    if evt.GetShift():
                        self.SetFoldExpanded(lineClicked, True)
                        self.Expand(lineClicked, True, True, 1)
                    elif evt.GetControl():
                        if self.GetFoldExpanded(lineClicked):
                            self.SetFoldExpanded(lineClicked, False)
                            self.Expand(lineClicked, False, True, 0)
                        else:
                            self.SetFoldExpanded(lineClicked, True)
                            self.Expand(lineClicked, True, True, 100)
                    else:
                        self.ToggleFold(lineClicked)

    def FoldAll(self):
        if self.GetEndStyled() != self.GetLength():
            self.OnStyleNeeded(None, forceAll=True)
        lineCount = self.GetLineCount()
        expanding = True

        # find out if we are folding or unfolding
        for lineNum in range(lineCount):
            if self.GetFoldLevel(lineNum) & stc.STC_FOLDLEVELHEADERFLAG:
                expanding = not self.GetFoldExpanded(lineNum)
                break

        lineNum = 0

        while lineNum < lineCount:
            level = self.GetFoldLevel(lineNum)
            if level & stc.STC_FOLDLEVELHEADERFLAG and \
               (level & stc.STC_FOLDLEVELNUMBERMASK) == stc.STC_FOLDLEVELBASE:

                if expanding:
                    self.SetFoldExpanded(lineNum, True)
                    lineNum = self.Expand(lineNum, True)
                    lineNum = lineNum - 1
                else:
                    lastChild = self.GetLastChild(lineNum, -1)
                    self.SetFoldExpanded(lineNum, False)

                    if lastChild > lineNum:
                        self.HideLines(lineNum+1, lastChild)

            lineNum = lineNum + 1

    def Expand(self, line, doExpand, force=False, visLevels=0, level=-1):
        lastChild = self.GetLastChild(line, level)
        line = line + 1

        while line <= lastChild:
            if force:
                if visLevels > 0:
                    self.ShowLines(line, line)
                else:
                    self.HideLines(line, line)
            else:
                if doExpand:
                    self.ShowLines(line, line)

            if level == -1:
                level = self.GetFoldLevel(line)

            if level & stc.STC_FOLDLEVELHEADERFLAG:
                if force:
                    if visLevels > 1:
                        self.SetFoldExpanded(line, True)
                    else:
                        self.SetFoldExpanded(line, False)

                    line = self.Expand(line, doExpand, force, visLevels-1)

                else:
                    if doExpand and self.GetFoldExpanded(line):
                        line = self.Expand(line, True, force, visLevels-1)
                    else:
                        line = self.Expand(line, False, force, visLevels-1)
            else:
                line = line + 1

        return line
