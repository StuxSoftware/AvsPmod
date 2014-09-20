
        # if self.playing_video:
        #     if os.name == 'nt':
        #         self.timeKillEvent(self.play_timer_id)
        #         self.timeEndPeriod(self.play_timer_resolution)
        #     else:
        #         self.play_timer.Stop()
        #         #signal.setitimer(signal.ITIMER_REAL, 0) # see below
        #         #signal.signal(signal.SIGALRM, self.previous_signal_handler)
        #     self.playing_video = False
        #     self.play_button.SetBitmapLabel(self.bmpPlay)
        #     self.play_button.Refresh()
        #     if self.separatevideowindow:
        #         self.play_button2.SetBitmapLabel(self.bmpPlay)
        #         self.play_button2.Refresh()
        # elif self.ShowVideoFrame(focus=False) and not self.currentScript.AVI.IsErrorClip():
        #     script = self.currentScript
        #     if self.currentframenum == script.AVI.Framecount - 1:
        #         return
        #     self.playing_video = True
        #     self.play_button.SetBitmapLabel(self.bmpPause)
        #     self.play_button.Refresh()
        #     if self.separatevideowindow:
        #         self.play_button2.SetBitmapLabel(self.bmpPause)
        #         self.play_button2.Refresh()
        #     if self.play_speed_factor == 'max':
        #         interval = 1.0 # use a timer anyway to avoid GUI refreshing issues
        #     else:
        #         interval =  1000 / (script.AVI.Framerate * self.play_speed_factor)
        #
        #     if os.name == 'nt': # default Windows resolution is ~10 ms
        #
        #         def playback_timer(id, reserved, factor, reserved1, reserved2):
        #             """"Callback for a Windows Multimedia timer"""
        #             if not self.playing_video:
        #                 return
        #             if debug_stats:
        #                 current_time = time.time()
        #                 debug_stats_str = str((current_time - self.previous_time) * 1000)
        #                 self.previous_time = current_time
        #             if self.play_drop and self.play_speed_factor != 'max':
        #                 frame = self.play_initial_frame
        #                 increment = int(round(1000 * (time.time() - self.play_initial_time) / interval)) * factor
        #                 if debug_stats:
        #                     debug_stats_str += ' dropped: ' + str(increment - self.increment - 1)
        #                     self.increment = increment
        #             else:
        #                 frame = self.currentframenum
        #                 increment = 1
        #             if debug_stats:
        #                 print debug_stats_str
        #             if not AsyncCall(self.ShowVideoFrame, frame + increment,
        #                              check_playing=True, focus=False).Wait():
        #                 return
        #             if self.currentframenum == script.AVI.Framecount - 1:
        #                 self.PlayPauseVideo()
        #             else:
        #                 wx.Yield()
        #
        #         def WindowsTimer(interval, callback, periodic=True):
        #             """High precision timer (1 ms) using Windows Multimedia"""
        #
        #             self.timeGetDevCaps = ctypes.windll.winmm.timeGetDevCaps
        #             self.timeBeginPeriod = ctypes.windll.winmm.timeBeginPeriod
        #             self.timeEndPeriod = ctypes.windll.winmm.timeEndPeriod
        #             self.timeSetEvent = ctypes.windll.winmm.timeSetEvent
        #             self.timeKillEvent = ctypes.windll.winmm.timeKillEvent
        #
        #             callback_prototype = ctypes.WINFUNCTYPE(None, ctypes.c_uint,
        #                 ctypes.c_uint, ctypes.c_ulong, ctypes.c_ulong, ctypes.c_ulong)
        #             self.timeSetEvent.argtypes = [ctypes.c_uint, ctypes.c_uint,
        #                 callback_prototype, ctypes.c_ulong, ctypes.c_uint]
        #
        #             class TIMECAPS(ctypes.Structure):
        #                 _fields_ = [("wPeriodMin", ctypes.c_uint),
        #                             ("wPeriodMax", ctypes.c_uint)]
        #
        #             caps = TIMECAPS()
        #             self.timeGetDevCaps(ctypes.byref(caps), ctypes.sizeof(caps))
        #             self.play_timer_resolution = max(1, caps.wPeriodMin)
        #             self.timeBeginPeriod(self.play_timer_resolution)
        #
        #             interval0 = interval
        #             factor = max(1, int(round(self.play_timer_resolution / interval)))
        #             interval = int(round(interval * factor))
        #             self.callback_c = callback_prototype(callback)
        #             self.play_initial_frame = self.currentframenum
        #             self.play_initial_time = time.time()
        #             if debug_stats:
        #                 print 'speed_factor: {0}, required_interval: {1} '\
        #                       'interval: {2} interval_factor: {3}'.format(
        #                       self.play_speed_factor, interval0, interval, factor)
        #                 self.increment = 0
        #                 self.previous_time = self.play_initial_time
        #             self.play_timer_id = self.timeSetEvent(interval,
        #                 self.play_timer_resolution, self.callback_c, factor, periodic)
        #
        #         WindowsTimer(interval, playback_timer)
        #
        #     else: # wx.Timer on *nix.  There's some pending events issues
        #         # TODO: fix/replace wx.Timer
        #
        #         # signal module causes segmentation fault on high fps
        #         # similar issues using librt with ctypes
        #         '''
        #         global signal
        #         import signal
        #
        #         def playback_timer(signum, frame):
        #             """"SIGALRM handler"""
        #             if not self.playing_video:
        #                 return
        #             if debug_stats:
        #                 current_time = time.time()
        #                 debug_stats_str = str((current_time - self.previous_time) * 1000)
        #                 self.previous_time = current_time
        #             if self.play_drop and self.play_speed_factor != 'max':
        #                 frame = self.play_initial_frame
        #                 increment = int(round((time.time() - self.play_initial_time) / interval)) * factor
        #                 if debug_stats:
        #                     debug_stats_str += ' dropped: ' + str(increment - self.increment - 1)
        #                     self.increment = increment
        #             else:
        #                 frame = self.currentframenum
        #                 increment = 1
        #             if debug_stats:
        #                 print debug_stats_str
        #             if not AsyncCall(self.ShowVideoFrame, frame + increment,
        #                              check_playing=True, focus=False).Wait():
        #                 return
        #             if self.currentframenum == script.AVI.Framecount - 1:
        #                 self.PlayPauseVideo()
        #             elif not wx.GetApp().Yield(True):
        #                 self.parent.PlayPauseVideo()
        #
        #         interval0 = interval
        #         factor = max(1, int(round(1 / interval)))
        #         interval = interval * factor / 1000
        #         self.previous_signal_handler = signal.signal(signal.SIGALRM, playback_timer)
        #         self.play_initial_frame = self.currentframenum
        #         self.play_initial_time = time.time()
        #         if debug_stats:
        #             print 'speed_factor: {0}, required_interval: {1} '\
        #                   'interval: {2} interval_factor: {3}'.format(
        #                   self.play_speed_factor, interval0, interval * 1000, factor)
        #             self.increment = 0
        #             self.previous_time = self.play_initial_time
        #         signal.setitimer(signal.ITIMER_REAL, interval, interval)
        #
        #         return
        #         '''
        #
        #         class RunVideoTimer(wx.Timer):
        #             def __init__(self, parent, factor=1):
        #                 wx.Timer.__init__(self)
        #                 self.parent = parent
        #                 self.factor = factor
        #                 self.play_initial_frame = self.parent.currentframenum
        #                 self.play_initial_time = time.time()
        #                 self.Yield = wx.GetApp().Yield
        #                 if debug_stats:
        #                     self.increment = 0
        #                     self.previous_time = self.play_initial_time
        #             def Notify(self):
        #                 if not self.parent.playing_video:
        #                     self.parent.PlayPauseVideo()
        #                     return
        #                 if debug_stats:
        #                     current_time = time.time()
        #                     debug_stats_str = str((current_time - self.previous_time) * 1000)
        #                     self.previous_time = current_time
        #                 if self.parent.play_drop and self.parent.play_speed_factor != 'max':
        #                     frame = self.play_initial_frame
        #                     increment = int(round(1000 * (time.time() - self.play_initial_time) / self.GetInterval())) * self.factor
        #                     if debug_stats:
        #                         debug_stats_str += ' dropped: ' + str(increment - self.increment - 1)
        #                         self.increment = increment
        #                 else:
        #                     frame = self.parent.currentframenum
        #                     increment = 1
        #                 if debug_stats:
        #                     print debug_stats_str
        #                 if not self.parent.ShowVideoFrame(frame + increment,
        #                                                   check_playing=True, focus=False):
        #                     return
        #                 if self.parent.currentframenum == script.AVI.Framecount - 1:
        #                     self.parent.PlayPauseVideo()
        #                 elif not self.Yield(True):
        #                     self.parent.PlayPauseVideo()
        #
        #         interval0 = interval
        #         factor = max(1, int(round(1 / interval)))
        #         interval = int(round(interval * factor))
        #         self.play_timer = RunVideoTimer(self, factor)
        #         if debug_stats:
        #             print 'speed_factor: {0}, required_interval: {1} '\
        #                   'interval: {2} interval_factor: {3}'.format(
        #                   self.play_speed_factor, interval0, interval, factor)
        #         self.play_timer.Start(interval)