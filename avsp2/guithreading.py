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

import threading
import functools

import wx

# Make safe calls to the main thread from other threads
# Adapted from <http://thread.gmane.org/gmane.comp.python.wxpython/54892/focus=55223>
class AsyncCall:
    ''' Queues a func to run in thread of MainLoop.
    Code may wait() on self.complete for self.result to contain
    the result of func(*ar,**kwar).  It is set upon completion.
    Wait() does this.'''
    def __init__(self, func, *ar, **kwar):
        self.result = self.noresult = object()
        self.complete = threading.Event()
        self.func, self.ar, self.kwar = func, ar, kwar
        if threading.current_thread().name == 'MainThread':
            self.TimeToRun()
        else:
            wx.CallAfter(self.TimeToRun)
    def TimeToRun(self):
        try:
            self.result = self.func(*self.ar, **self.kwar)
        except:
            self.exception = sys.exc_info()
        else:
            self.exception = None
        self.complete.set()
    def Wait(self, timeout=None, failval=None):
        self.complete.wait(timeout)
        if self.exception:
            raise self.exception[0], self.exception[1], self.exception[2]
        if self.result is self.noresult:
            return failval
        return self.result

# Decorator for AsyncCall class
def AsyncCallWrapper(wrapped):
    '''Decorator for AsyncCall class'''
    def wrapper(*args, **kwargs):
        return AsyncCall(wrapped, *args, **kwargs).Wait()
    functools.update_wrapper(wrapper, wrapped)
    return wrapper