# AvsP - an AviSynth editor
# AvsP.Timers - A refactoring of timers out of the main window class.
#
# Copyright 2007 Peter Jang <http://www.avisynth.org/qwerpoi>
#           2010-2014 the AvsPmod authors <https://github.com/avspmod/avspmod>
#
# Refactored by:
#           2014 StuxCrystal <https://github.com/StuxSoftware>
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
import traceback
import platform

# Check if wx is available.
try:
    import wx
except ImportError:
    wx_available = False
else:
    wx_available = True
    del wx


class _CatchExceptions(object):
    """
    Internal context manager that will swallow all exceptions and will call
    a callback function when an exception occures.
    """

    def __init__(self, errback):
        self.errback = errback

    def __enter__(self):
        pass

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is not None:
            return self.errback(exc_type, exc_val, exc_tb)
        return False


class TimerBase(object):
    """
    Base class for timers. It is an internal class to allow the same bootstrap
    functions.
    """

    def __init__(self, interval, cb=None, repeat=True):
        """
        :param interval  The interval in milliseconds.
        :param cb        Optional. The function that will be called on tick.
        :param repeat    Optional. Should the timer repeat after being started?
                         [default:false]
        """
        self.cb = cb
        self.interval = interval
        self.repeat = repeat

    def _call(self):
        """
        Internal method that will call the callback specified for the timer.
        If this timer is a oneshot timer, this function will call the stop
        function automatically to ensure that the timer will not fire a second
        time.
        """
        # Only use my own context manager to make sure that
        # all exceptions get their timer appended to the traceback.
        with _CatchExceptions(self._on_exception):
            self.run()

        if not self.repeat:
            self.stop()

    def _on_exception(self, exc, val, tb):
        """
        Called when a exception occurs while executing the callback.
        """
        print >>sys.stderr, "%r callback threw the following exception:" % self
        traceback.print_exception(exc, val, tb)
        self.stop()
        return True

    def run(self):
        """
        Used defined sub-classes of the timer can override this function as
        this function will be called instead of the callback.
        """
        self.cb()

    @property
    def running(self):
        """
        Checks if the timer is running.
        """
        raise NotImplemented

    def start(self):
        """
        Starts the timer.
        """
        if self.running:
            return
        self._start()

    def stop(self):
        """
        Stops the timer.
        """
        if not self.running:
            return
        self._stop()

    def _start(self):
        """
        Actual implementation of the start function. To be overridden.
        """
        raise NotImplemented

    def _stop(self):
        """
        Actual implementation of the stop function. To be overridden.
        """
        raise NotImplemented


# Implementations of timers.
_timers = []


def get_timer_class():
    """
    Returns the best suitable timer class to use for subclassing
    (or instantiation).
    """
    # Ensure we have a timer class available.
    if len(_timers) == 0:
        raise LookupError("No suitable timers found.")

    # Return the first timer.
    return _timers[0]


def Timer(interval, cb, repeat=False):
    """
    Creates the timer with the highest known resolution in the operating
    system.
    """
    return get_timer_class()(interval, cb, repeat)

if platform.platform().startswith("Windows"):
    import ctypes

    class WinMM(object):
        """
        Windows Multimedia Timer API.
        """
        timeGetDevCaps = ctypes.windll.winmm.timeGetDevCaps
        timeBeginPeriod = ctypes.windll.winmm.timeBeginPeriod
        timeEndPeriod = ctypes.windll.winmm.timeEndPeriod
        timeSetEvent = ctypes.windll.winmm.timeSetEvent
        timeKillEvent = ctypes.windll.winmm.timeKillEvent

        callback_prototype = ctypes.WINFUNCTYPE(
            None,
            ctypes.c_uint, ctypes.c_uint, ctypes.c_ulong, ctypes.c_ulong,
            ctypes.c_ulong
        )

        TIME_ONESHOT = 0x0000
        TIME_PERIODIC = 0x0001

    class TIMECAPS(ctypes.Structure):
        """
        Structure that will contain the capabilities of the multimedia timer.
        """
        _fields_ = [
            ("wPeriodMin", ctypes.c_uint),
            ("wPeriodMax", ctypes.c_uint),
        ]

        @classmethod
        def resolve(cls):
            self = cls()
            WinMM.timeGetDevCaps(ctypes.byref(self), ctypes.sizeof(self))
            return self

    class WindowsTimer(TimerBase):
        """
        Implementation of the windows timer.
        """

        def __init__(self, interval, cb, repeat=True):
            super(WindowsTimer, self).__init__(interval, cb, repeat)

            # Internal data for the timer.
            self._resolution = -1
            self.id = -1

            # Get a function pointer to the bootstrap method that will call
            # the _call method of the timer.
            self._bootstrap_cb = WinMM.callback_prototype(self._bootstrap)

        def _bootstrap(self, id, reserved, factor, reserved1, reserved2):
            """
            Internal method that will call the _call-method that will call
            the actual callback.
            """
            # Ensure we get the right id.
            if self.id != id:
                # Make sure the timer does not throw an exception
                # even if we throw it ourself.
                with _CatchExceptions(self._on_exception):
                    raise WindowsError(
                        "%r received tick for timer with id %d" % (self, id)
                    )

            # Call the function.
            self._call()

        @property
        def running(self):
            return self.id != -1

        def _start(self):
            caps = TIMECAPS.resolve()

            # Clamp resolution to the margins set by the operating system.
            self._resolution = max(1, caps.wPeriodMin)
            if caps.wPeriodMax < self.interval:
                raise WindowsError("Interval too large.")


            factor = max(1, int(round(self._resolution / self.interval)))
            interval = int(round(self.interval * factor))

            WinMM.timeBeginPeriod(self._resolution)
            self.id = WinMM.timeSetEvent(
                interval,
                self._resolution,
                self._bootstrap_cb,
                factor,
                WinMM.TIME_PERIODIC if self.repeat else WinMM.TIME_ONESHOT
            )

        def _stop(self):
            WinMM.timeKillEvent(self.id)
            WinMM.timeEndPeriod(self._resolution)

        def __repr__(self):
            return "<Timer type:Windows-Multimedia id:%d>" % self.id

    # Register timer.
    _timers.append(WindowsTimer)


if wx_available:
    import wx

    class WxProxyTimer(wx.Timer):
        """
        Implementation of a timer that will call the _call method of the
        parent timer.
        """

        def __init__(self, parent, factor, timer):
            super(WxProxyTimer, self).__init__()
            self.parent = parent
            self.factor = factor
            self.timer = timer

        def Notify(self):
            self.timer._call()

    class WxTimer(TimerBase):
        """
        Implementation of a timer using wx.
        """

        def __init__(self, interval, cb, repeat=True):
            super(WxTimer, self).__init__(interval, cb, repeat)

            # I don't see where this is going...
            factor = max(1, int(round(1/self.interval)))
            self._wx_interval = int(round(interval * factor))

            self.timer = WxProxyTimer(self.parent, factor, self)

        @property
        def running(self):
            return self.timer.IsRunning()

        def _start(self):
            self.timer.Start(self.interval, not self.repeat)

        def _stop(self):
            self.timer.Stop()

        def __repr__(self):
            return "<Timer type:WxTimer handle:%r>" % self.timer

    # Register timer.
    _timers.append(WxTimer)

