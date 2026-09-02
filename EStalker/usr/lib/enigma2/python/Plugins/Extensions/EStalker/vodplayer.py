#!/usr/bin/python
# -*- coding: utf-8 -*-

# Standard library imports
from __future__ import absolute_import, print_function
from __future__ import division

import re
import json
import hashlib
import os
import tempfile
from itertools import cycle, islice

try:
    from urlparse import urlparse
    from urllib import unquote, quote
except ImportError:
    from urllib.parse import urlparse
    from urllib.parse import unquote, quote
try:
    from http.client import HTTPConnection
    HTTPConnection.debuglevel = 0
except ImportError:
    from httplib import HTTPConnection
    HTTPConnection.debuglevel = 0

# Third-party imports
from twisted.web.client import downloadPage

# https twisted client hack #
try:
    from twisted.internet import ssl
    from twisted.internet._sslverify import ClientTLSOptions
    sslverify = True
except:
    sslverify = False

if sslverify:
    class SNIFactory(ssl.ClientContextFactory):
        def __init__(self, hostname=None):
            self.hostname = hostname

        def getContext(self):
            ctx = self._contextFactory(self.method)
            if self.hostname:
                ClientTLSOptions(self.hostname, ctx)
            return ctx

# Enigma2 components
from Components.ActionMap import ActionMap
from Components.Label import Label
from Components.Pixmap import MultiPixmap, Pixmap
from Components.ServiceEventTracker import ServiceEventTracker, InfoBarBase
from enigma import eTimer, eServiceReference, iPlayableService, ePicLoad
from Screens.InfoBarGenerics import InfoBarSeek, InfoBarAudioSelection, InfoBarSummarySupport, InfoBarMoviePlayerSummarySupport, InfoBarSubtitleSupport, InfoBarNotifications
from Screens.MessageBox import MessageBox
from Screens.Screen import Screen
from Tools import Notifications
from Tools.BoundFunction import boundFunction

try:
    from .resumepoints import setResumePoint, getResumePoint
except ImportError as e:
    print(e)

# Local application/library-specific imports
from . import _
from . import estalker_globals as glob
from .plugin import cfg, common_path, dir_tmp, pythonVer, screenwidth, skin_directory
from .eStaticText import StaticText
from .utils import get_local_timezone, make_request, reauthorize_portal, _get_current_aspect_ratio, clearCaches

try:
    from enigma import eAVSwitch
except Exception:
    from enigma import eAVControl as eAVSwitch

if cfg.subs.value is True:
    try:
        from Plugins.Extensions.SubsSupport import SubsSupport, SubsSupportStatus
    except ImportError:
        class SubsSupport(object):
            def __init__(self, *args, **kwargs):
                pass

        class SubsSupportStatus(object):
            def __init__(self, *args, **kwargs):
                pass
else:
    class SubsSupport(object):
        def __init__(self, *args, **kwargs):
            pass

    class SubsSupportStatus(object):
        def __init__(self, *args, **kwargs):
            pass

VIDEO_ASPECT_RATIO_MAP = {
    0: "4:3 Letterbox",
    1: "4:3 PanScan",
    2: "16:9",
    3: "16:9 Always",
    4: "16:10 Letterbox",
    5: "16:10 PanScan",
    6: "16:9 Letterbox"
}

vodstreamtypelist = ["4097"]

if os.path.exists("/usr/bin/gstplayer"):
    vodstreamtypelist.append("5001")


if os.path.exists("/usr/bin/exteplayer3"):
    vodstreamtypelist.append("5002")

if os.path.exists("/usr/bin/apt-get"):
    vodstreamtypelist.append("8193")

class IPTVInfoBarShowHide():
    STATE_HIDDEN = 0
    STATE_HIDING = 1
    STATE_SHOWING = 2
    STATE_SHOWN = 3
    FLAG_CENTER_DVB_SUBS = 2048
    skipToggleShow = False

    def __init__(self):
        self.__event_tracker = ServiceEventTracker(screen=self, eventmap={
            iPlayableService.evStart: self.serviceStarted,
        })

        self.__state = self.STATE_SHOWN
        self.__locked = 0

        self.hideTimer = eTimer()
        try:
            self.hideTimer_conn = self.hideTimer.timeout.connect(self.doTimerHide)
        except:
            self.hideTimer.callback.append(self.doTimerHide)
        self.hideTimer.start(4000, True)

        self.onShow.append(self.__onShow)
        self.onHide.append(self.__onHide)

    def OkPressed(self):
        self.toggleShow()

    def __onShow(self):
        self.__state = self.STATE_SHOWN
        self.startHideTimer()

    def __onHide(self):
        self.__state = self.STATE_HIDDEN

    def serviceStarted(self):
        if self.execing:
            self.doShow()

    def startHideTimer(self):
        if self.__state == self.STATE_SHOWN and not self.__locked:
            self.hideTimer.stop()
            self.hideTimer.start(4000, True)

        elif hasattr(self, "pvrStateDialog"):
            self.hideTimer.stop()
        self.skipToggleShow = False

    def doShow(self):
        self.hideTimer.stop()
        self.show()
        self.startHideTimer()

    def doTimerHide(self):
        self.hideTimer.stop()
        if self.__state == self.STATE_SHOWN:
            self.hide()

    def toggleShow(self):
        if self.skipToggleShow:
            self.skipToggleShow = False
            return

        if self.__state == self.STATE_HIDDEN:
            self.show()
            self.hideTimer.stop()
        else:
            self.hide()
            self.startHideTimer()

    def lockShow(self):
        try:
            self.__locked += 1
        except:
            self.__locked = 0
        if self.execing:
            self.show()
            self.hideTimer.stop()
            self.skipToggleShow = False

    def unlockShow(self):
        try:
            self.__locked -= 1
        except:
            self.__locked = 0
        if self.__locked < 0:
            self.__locked = 0
        if self.execing:
            self.startHideTimer()


class PVRState2(Screen):
    def __init__(self, session):
        Screen.__init__(self, session)
        self["eventname"] = Label()
        self["state"] = Label()
        self["speed"] = Label()
        self["statusicon"] = MultiPixmap()


PVRState = PVRState2


class IPTVInfoBarPVRState:
    def __init__(self, screen=PVRState, force_show=True):
        self.onChangedEntry = []
        self.onPlayStateChanged.append(self.__playStateChanged)
        self.pvrStateDialog = self.session.instantiateDialog(screen)
        self.onShow.append(self._mayShow)
        self.onHide.append(self.pvrStateDialog.hide)
        self.force_show = force_show

    def _mayShow(self):
        if "state" in self and not self.force_show:
            self["state"].setText("")
            self["statusicon"].setPixmapNum(6)
            self["speed"].setText("")
        if self.shown and self.seekstate != self.SEEK_STATE_EOF and not self.force_show:
            self.pvrStateDialog.show()
            self.startHideTimer()

    def __playStateChanged(self, state):
        playstateString = state[3]
        state_summary = playstateString

        if "statusicon" in self.pvrStateDialog:
            self.pvrStateDialog["state"].setText(playstateString)
            speedtext = ""
            self.pvrStateDialog["speed"].setText("")
            speed_summary = self.pvrStateDialog["speed"].text
            if playstateString:
                if playstateString == ">":
                    statusicon_summary = 0
                    self.pvrStateDialog["statusicon"].setPixmapNum(statusicon_summary)

                elif playstateString == "||":
                    statusicon_summary = 1
                    self.pvrStateDialog["statusicon"].setPixmapNum(statusicon_summary)

                elif playstateString == "END":
                    statusicon_summary = 2
                    self.pvrStateDialog["statusicon"].setPixmapNum(statusicon_summary)

                elif playstateString.startswith(">>"):
                    speed = state[3].split()
                    statusicon_summary = 3
                    self.pvrStateDialog["statusicon"].setPixmapNum(statusicon_summary)
                    self.pvrStateDialog["speed"].setText(speed[1])
                    speedtext = speed[1]

                elif playstateString.startswith("<<"):
                    speed = state[3].split()
                    statusicon_summary = 4
                    self.pvrStateDialog["statusicon"].setPixmapNum(statusicon_summary)
                    self.pvrStateDialog["speed"].setText(speed[1])
                    speedtext = speed[1]

                elif playstateString.startswith("/"):
                    statusicon_summary = 5
                    self.pvrStateDialog["statusicon"].setPixmapNum(statusicon_summary)
                    self.pvrStateDialog["speed"].setText(playstateString)

                    speedtext = playstateString

            if "state" in self and self.force_show:
                self["state"].setText(playstateString)
                self["statusicon"].setPixmapNum(statusicon_summary)
                self["speed"].setText(speedtext)

            for cb in self.onChangedEntry:
                cb(state_summary, speed_summary, statusicon_summary)


class EStalkerCueSheetSupport:
    ENABLE_RESUME_SUPPORT = False

    def __init__(self):
        self.cut_list = []
        self.is_closing = False
        self.started = False
        self.resume_point = ""
        if not os.path.exists("/etc/enigma2/estalker/resumepoints.pkl"):
            with open("/etc/enigma2/estalker/resumepoints.pkl", "w"):
                pass

        self.__event_tracker = ServiceEventTracker(screen=self, eventmap={
            iPlayableService.evUpdatedInfo: self.__serviceStarted,
        })

    def __serviceStarted(self):
        if self.is_closing:
            return

        if self.ENABLE_RESUME_SUPPORT and not self.started:
            self.started = True
            last = None

            service = self.session.nav.getCurrentService()

            if service is None:
                return

            seekable = service.seek()
            if seekable is None:
                return  # Should not happen?

            length = seekable.getLength() or (None, 0)
            length[1] = abs(length[1])

            try:
                last = getResumePoint(self.session)
            except Exception as e:
                print(e)
                return

            if last is None:
                return
            if (last > 900000) and (not length[1] or (last < length[1] - 900000)):
                self.resume_point = last
                newlast = last // 90000
                Notifications.AddNotificationWithCallback(self.playLastCB, MessageBox, _("Do you want to resume this playback?") + "\n" + (_("Resume position at %s") % ("%d:%02d:%02d" % (newlast // 3600, newlast % 3600 // 60, newlast % 60))), MessageBox.TYPE_YESNO, 10)

    def playLastCB(self, answer):
        if answer is True and self.resume_point:
            service = self.session.nav.getCurrentService()
            seekable = service.seek()
            if seekable is not None:
                seekable.seekTo(self.resume_point)
        self.hideAfterResume()

    def hideAfterResume(self):
        if isinstance(self, IPTVInfoBarShowHide):
            try:
                self.hide()
            except Exception as e:
                print(e)


class EStalker_VodPlayer(
    InfoBarBase,
    IPTVInfoBarShowHide,
    IPTVInfoBarPVRState,
    EStalkerCueSheetSupport,
    InfoBarAudioSelection,
    InfoBarSeek,
    InfoBarNotifications,
    InfoBarSummarySupport,
    InfoBarSubtitleSupport,
    InfoBarMoviePlayerSummarySupport,
    SubsSupportStatus,
    SubsSupport,
        Screen):

    ENABLE_RESUME_SUPPORT = True
    ALLOW_SUSPEND = True

    def __init__(self, session, streamurl, servicetype, stream_id=None, storage_id="", link_metadata=None):
        Screen.__init__(self, session)

        clearCaches()

        self.session = session

        for x in (
            InfoBarBase,
            IPTVInfoBarShowHide,
            InfoBarAudioSelection,
            InfoBarSeek,
            InfoBarNotifications,
            InfoBarSummarySupport,
            InfoBarSubtitleSupport,
            InfoBarMoviePlayerSummarySupport
        ):
            x.__init__(self)

        try:
            EStalkerCueSheetSupport.__init__(self)
        except Exception as e:
            print(e)

        IPTVInfoBarPVRState.__init__(self, PVRState, True)

        self.ar_id_player = -1
        try:
            self.ar_id_player = int(cfg.ar_id_player.value)
        except Exception:
            self.ar_id_player = -1

        if cfg.subs.value is True:
            SubsSupport.__init__(self, searchSupport=True, embeddedSupport=True)
            SubsSupportStatus.__init__(self)

        self.streamurl = streamurl
        self.servicetype = servicetype
        self.originalservicetype = self.servicetype
        self.stream_id = stream_id
        self.storage_id = storage_id or ""
        self.link_metadata = link_metadata if isinstance(link_metadata, dict) else {}
        self.track_portal_playback = stream_id is not None
        self.archive_hist_id = ""
        self.playlists_json = cfg.playlists_json.value

        skin_path = os.path.join(skin_directory, cfg.skin.value)
        skin = os.path.join(skin_path, "vodplayer.xml")
        with open(skin, "r") as f:
            self.skin = f.read()

        self["streamcat"] = StaticText()
        self["streamtype"] = StaticText()
        self["extension"] = StaticText()
        self["cover"] = Pixmap()
        self["eventname"] = Label()
        self["state"] = Label()
        self["speed"] = Label()
        self["statusicon"] = MultiPixmap()
        self["PTSSeekBack"] = Pixmap()
        self["PTSSeekPointer"] = Pixmap()

        self.PicLoad = ePicLoad()
        try:
            self.PicLoad.PictureData.get().append(self.DecodePicture)
        except:
            self.PicLoad_conn = self.PicLoad.PictureData.connect(self.DecodePicture)

        self.setup_title = _("VOD")

        self.timezone = get_local_timezone()
        self.token = glob.active_playlist["playlist_info"]["token"]
        self.token_random = glob.active_playlist["playlist_info"]["token_random"]
        self.domain = str(glob.active_playlist["playlist_info"].get("domain", ""))
        self.port = glob.active_playlist["playlist_info"].get("port", "")
        self.host = str(glob.active_playlist["playlist_info"].get("host", "")).rstrip("/")
        self.mac = glob.active_playlist["playlist_info"].get("mac", "").upper()
        self.portal = glob.active_playlist["playlist_info"].get("portal", None)
        self.portal_version = glob.active_playlist["playlist_info"].get("version", "5.3.1")
        self.path_prefix = glob.active_playlist["playlist_info"].get("path_prefix", "")

        self.referer = self.host + self.path_prefix + "index.html"

        self.sn = hashlib.md5(self.mac.encode()).hexdigest().upper()[:13]
        self.adid = hashlib.md5((self.sn + self.mac).encode()).hexdigest()

        encoded_mac = quote(self.mac, safe='')
        encoded_timezone = quote(self.timezone, safe='')

        saved_headers = glob.active_playlist["playlist_info"].get("headers", {})
        self.headers = saved_headers.copy() if isinstance(saved_headers, dict) else {}

        if not self.headers:
            cookie = "mac={}; stb_lang=en; timezone={}".format(encoded_mac, encoded_timezone)
            if self.portal and "/stalker_portal/" in self.portal:
                cookie += "; adid={}".format(self.adid)

            self.headers = {
                "Pragma": "no-cache",
                "Accept-Language": "en-US,en;q=0.5",
                "Accept-Encoding": "gzip, deflate",
                "Host": "{}:{}".format(self.domain, self.port) if self.port else self.domain,
                "User-Agent": "Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 (KHTML, like Gecko) MAG200 stbapp ver: 2 rev: 250 Safari/533.3",
                "X-User-Agent": "Model: MAG250; Link: WiFi",
                "Connection": "Close",
                "Referer": self.referer,
                "Cookie": cookie,
            }

        self.headers["Authorization"] = "Bearer " + self.token
        self.watchdog_initialized = False

        self["actions"] = ActionMap(["EStalkerActions"], {
            "cancel": self.back,
            "stop": self.back,
            "red": self.back,
            "channelUp": self.__next__,
            "down": self.__next__,
            "channelDown": self.prev,
            "up": self.prev,
            "tv": self.toggleStreamType,
            "info": self.toggleStreamType,
            "green": self.nextAR,
            "ok": self.refreshInfobar,
        }, -2)

        self._cover_req_id = 0

        self.timerWatched = eTimer()
        try:
            self.timerWatched.callback.append(self.addWatchedList)
        except:
            self.timerWatched_conn = self.timerWatched.timeout.connect(self.addWatchedList)

        self.timerWatchdog = eTimer()
        try:
            self.timerWatchdog.callback.append(self.sendWatchdog)
        except:
            self.timerWatchdog_conn = self.timerWatchdog.timeout.connect(self.sendWatchdog)

        self.onFirstExecBegin.append(boundFunction(self.playStream, self.servicetype, self.streamurl))

    def sendWatchdog(self):
        init = "0" if self.watchdog_initialized else "1"
        cur_play_type = "11" if glob.categoryname == "catchup" else "2"
        watchdog_url = "{0}?type=watchdog&action=get_events&cur_play_type={1}&event_active_id=0&init={2}&JsHttpRequest=1-xml".format(
            self.portal, cur_play_type, init
        )
        response = make_request(watchdog_url, method="GET", headers=self.headers, params=None, response_type="json")
        if not response:
            self.reauthorize()
            response = make_request(watchdog_url, method="GET", headers=self.headers, params=None, response_type="json")

        if response:
            self.watchdog_initialized = True
        self.timerWatchdog.start(30000, True)

    def _stopTimer(self, name):
        t = getattr(self, name, None)
        if t:
            try:
                t.stop()
            except:
                pass

    def _cleanupTimer(self, name):
        t = getattr(self, name, None)
        if t:
            try:
                t.stop()
            except:
                pass
            try:
                t.callback[:] = []
            except:
                pass
        try:
            setattr(self, name, None)
        except:
            pass

    def refreshInfobar(self):
        IPTVInfoBarShowHide.OkPressed(self)

    def addWatchedList(self):
        stream_id = self.stream_id

        if glob.categoryname == "vod":
            if stream_id not in glob.active_playlist["player_info"]["vodwatched"]:
                glob.active_playlist["player_info"]["vodwatched"].append(stream_id)

            params = {
                "type": "vod",
                "action": "set_played",
                "video_id": stream_id,
                "storage_id": self.storage_id,
                "JsHttpRequest": "1-xml",
            }
            response = make_request(self.portal, method="GET", headers=self.headers, params=params, response_type="json")
            if not response:
                self.reauthorize()
                make_request(self.portal, method="GET", headers=self.headers, params=params, response_type="json")

        elif glob.categoryname == "series":
            if stream_id not in glob.active_playlist["player_info"]["serieswatched"]:
                glob.active_playlist["player_info"]["serieswatched"].append(stream_id)

        elif glob.categoryname == "catchup":
            channel_id = str(self.link_metadata.get("archive_channel_id", ""))
            if channel_id:
                params = {
                    "type": "tv_archive",
                    "action": "set_played",
                    "ch_id": channel_id,
                    "JsHttpRequest": "1-xml",
                }
                response = make_request(self.portal, method="GET", headers=self.headers, params=params, response_type="json")
                if not response:
                    self.reauthorize()
                    response = make_request(self.portal, method="GET", headers=self.headers, params=params, response_type="json")
                if isinstance(response, dict):
                    history_id = response.get("js", "")
                    if isinstance(history_id, dict):
                        history_id = history_id.get("id", "")
                    self.archive_hist_id = str(history_id or "")

        self.playlists_all = []
        playlists_json = cfg.playlists_json.value
        if os.path.exists(playlists_json):
            try:
                with open(playlists_json, "r") as f:
                    self.playlists_all = json.load(f) or []
            except:
                try:
                    os.remove(playlists_json)
                except:
                    pass
                self.playlists_all = []

        if self.playlists_all:
            for i, playlist in enumerate(self.playlists_all):
                playlist_info = playlist.get("playlist_info", {})
                current_playlist_info = glob.active_playlist.get("playlist_info", {})
                if (playlist_info.get("domain") == current_playlist_info.get("domain") and
                        playlist_info.get("mac") == current_playlist_info.get("mac")):
                    self.playlists_all[i] = glob.active_playlist
                    break

        with open(playlists_json, "w") as f:
            json.dump(self.playlists_all, f, indent=4)

    def playStream(self, servicetype, streamurl):
        self._stopTimer("timerWatched")

        if not streamurl:
            return

        self.streamurl = streamurl

        if glob.categoryname == "vod":
            stream_category = "VOD"
        elif glob.categoryname == "catchup":
            stream_category = _("TV Archive")
        else:
            stream_category = _("Series")
        self["streamcat"].setText(stream_category)
        self["streamtype"].setText(str(servicetype))

        try:
            path = urlparse(streamurl).path
            path = unquote(path)
            ext = os.path.splitext(path)[-1].lower()
            if ext in [".mp4", ".mkv", ".avi", ".m3u8", ".mpd", ".ts"]:
                self["extension"].setText(ext)
            else:
                self["extension"].setText("")
        except:
            pass

        self.reference = eServiceReference(int(self.servicetype), 0, streamurl)
        self.reference.setName(glob.currentchannellist[glob.currentchannellistindex][0])

        self.session.nav.playService(self.reference)

        if cfg.infobarcovers.value is True:
            self.downloadImage()

        if self.session.nav.getCurrentlyPlayingServiceReference():
            glob.newPlayingServiceRef = self.session.nav.getCurrentlyPlayingServiceReference()
            glob.newPlayingServiceRefString = self.session.nav.getCurrentlyPlayingServiceReference().toString()

            if self.track_portal_playback:
                watched_delay = 60 * 1000 if glob.categoryname == "catchup" else 15 * 60 * 1000
                self.timerWatched.start(watched_delay, True)
                # watchdog
                if not self.watchdog_initialized:
                    self.sendWatchdog()
                self.timerWatchdog.start(30000, True)

        try:
            self.arTimer.stop()
        except:
            pass

        self.arTimer = eTimer()

        try:
            self.arTimer.callback.append(self.applyAspectRatio)
        except:
            self.arTimer_conn = self.arTimer.timeout.connect(self.applyAspectRatio)

        self.arTimer.start(200, True)

    def applyAspectRatio(self):
        current_ar = _get_current_aspect_ratio()
        try:
            if self.ar_id_player != -1 and current_ar is not None and int(current_ar) != int(self.ar_id_player):
                self.setAspectRatio(self.ar_id_player)
        except Exception:
            pass

    def loadDefaultImage(self, data=None):
        if self["cover"].instance:
            self["cover"].instance.setPixmapFromFile(
                os.path.join(common_path, "cover.png")
            )

    def downloadImage(self):
        self.loadDefaultImage()

        try:
            self._cover_req_id += 1
        except:
            self._cover_req_id = 1

        req_id = self._cover_req_id

        desc_image = ""
        try:
            desc_image = glob.currentchannellist[glob.currentchannellistindex][5]
        except:
            desc_image = ""

        if not desc_image or str(desc_image).lower() == "n/a":
            self.loadDefaultImage()
            return

        if not desc_image.startswith(("http://", "https://")):
            self.loadDefaultImage()
            return

        fd = None
        temp = None

        try:
            fd, temp = tempfile.mkstemp(prefix="xst_cover_", suffix=".jpg", dir=dir_tmp)
            try:
                os.close(fd)
            except:
                pass

            self._cover_tmp = temp

            parsed = urlparse(desc_image)
            domain = parsed.hostname
            scheme = parsed.scheme

            url = desc_image
            if pythonVer == 3:
                try:
                    url = desc_image.encode()
                except:
                    url = desc_image

            def _cleanup_temp():
                try:
                    if temp and os.path.exists(temp):
                        os.remove(temp)
                except:
                    pass

            def _ok(_data=None):
                if getattr(self, "_cover_req_id", 0) != req_id:
                    _cleanup_temp()
                    return

                self.resizeImage(temp, req_id=req_id)

            def _err(_failure=None):
                if getattr(self, "_cover_req_id", 0) != req_id:
                    _cleanup_temp()
                    return

                _cleanup_temp()
                self.loadDefaultImage()

            if scheme == "https" and sslverify:
                sniFactory = SNIFactory(domain)
                d = downloadPage(url, temp, sniFactory, timeout=5)
            else:
                d = downloadPage(url, temp, timeout=5)

            d.addCallback(_ok)
            d.addErrback(_err)

        except:
            try:
                if fd:
                    os.close(fd)
            except:
                pass

            try:
                if temp and os.path.exists(temp):
                    os.remove(temp)
            except:
                pass

            self.loadDefaultImage()

    def resizeImage(self, preview, req_id=None):
        if not self["cover"].instance:
            return

        self._cover_preview = preview
        self._cover_preview_req_id = req_id

        if screenwidth.width() == 2560:
            width = 293
            height = 440
        elif screenwidth.width() > 1280:
            width = 220
            height = 330
        else:
            width = 147
            height = 220

        self.PicLoad.setPara([width, height, 1, 1, 0, 1, "FF000000"])

        if self.PicLoad.startDecode(preview):
            self.PicLoad = ePicLoad()
            try:
                self.PicLoad.PictureData.get().append(self.DecodePicture)
            except:
                self.PicLoad_conn = self.PicLoad.PictureData.connect(self.DecodePicture)

            self.PicLoad.setPara([width, height, 1, 1, 0, 1, "FF000000"])
            self.PicLoad.startDecode(preview)

    def DecodePicture(self, PicInfo=None):
        preview = getattr(self, "_cover_preview", None)
        preview_req_id = getattr(self, "_cover_preview_req_id", None)
        current_req_id = getattr(self, "_cover_req_id", None)

        ptr = self.PicLoad.getData()
        if (ptr is not None and self["cover"].instance and
                preview_req_id == current_req_id):
            self["cover"].instance.setPixmap(ptr)
            self["cover"].instance.show()

        try:
            if preview and os.path.exists(preview):
                os.remove(preview)
        except:
            pass

        try:
            if getattr(self, "_cover_tmp", None) == preview:
                self._cover_tmp = None
        except:
            pass

        try:
            self._cover_preview = None
            self._cover_preview_req_id = None
        except:
            pass

    def back(self):
        if glob.categoryname == "catchup" and self.archive_hist_id:
            params = {
                "type": "tv_archive",
                "action": "update_played_end_time",
                "hist_id": self.archive_hist_id,
                "JsHttpRequest": "1-xml",
            }
            response = make_request(self.portal, method="GET", headers=self.headers, params=params, response_type="json")
            if not response:
                self.reauthorize()
                make_request(self.portal, method="GET", headers=self.headers, params=params, response_type="json")

        try:
            self.timerWatchdog.stop()
        except:
            pass

        self._cleanupTimer("timerWatched")

        glob.nextlist[-1]["index"] = glob.currentchannellistindex
        try:
            setResumePoint(self.session)
        except Exception as e:
            print(e)

        try:
            self.session.nav.stopService()
        except:
            pass

        try:
            self.session.nav.playService(eServiceReference(glob.currentPlayingServiceRefString))
        except:
            pass

        try:
            tmp = getattr(self, "_cover_tmp", None)
            if tmp and os.path.exists(tmp):
                os.remove(tmp)
        except:
            pass

        self.close()

    def toggleStreamType(self):
        try:
            setResumePoint(self.session)
        except Exception as e:
            print(e)

        currentindex = 0

        for index, item in enumerate(vodstreamtypelist, start=0):
            if str(item) == str(self.servicetype):
                currentindex = index
                break

        nextStreamType = islice(cycle(vodstreamtypelist), currentindex + 1, None)

        try:
            self.servicetype = int(next(nextStreamType))
        except:
            pass

        self.playStream(self.servicetype, self.streamurl)

    def __next__(self):
        if glob.categoryname == "series":
            self.servicetype = self.originalservicetype

            if glob.currentchannellist:
                list_length = len(glob.currentchannellist)
                glob.currentchannellistindex += 1
                if glob.currentchannellistindex >= list_length:
                    glob.currentchannellistindex = 0

                episode_id = str(glob.currentchannellist[glob.currentchannellistindex][20])
                command = str(glob.currentchannellist[glob.currentchannellistindex][21])

                if not command:
                    glob.currentchannellistindex -= 1
                    self.back()
                    return

                media_id = str(glob.currentchannellist[glob.currentchannellistindex][4])
                next_url = self.resolveVodCommand(command, episode_id, self.link_metadata, media_id)
                if not next_url:
                    return

                if str(os.path.splitext(next_url)[-1]) == ".m3u8" and str(self.servicetype) == "1":
                    self.servicetype = "4097"

                str_servicetype = str(self.servicetype)

                next_url = str(next_url) if next_url else ""

                self.playStream(str_servicetype, next_url)

    def prev(self):
        if glob.categoryname == "series":
            self.servicetype = self.originalservicetype

            if glob.currentchannellist:
                list_length = len(glob.currentchannellist)
                glob.currentchannellistindex -= 1
                if glob.currentchannellistindex < 0:
                    glob.currentchannellistindex = list_length - 1

                episode_id = str(glob.currentchannellist[glob.currentchannellistindex][20])
                command = str(glob.currentchannellist[glob.currentchannellistindex][21])

                if not command:
                    glob.currentchannellistindex += 1
                    self.back()
                    return

                media_id = str(glob.currentchannellist[glob.currentchannellistindex][4])
                next_url = self.resolveVodCommand(command, episode_id, self.link_metadata, media_id)
                if not next_url:
                    return

                if str(os.path.splitext(next_url)[-1]) == ".m3u8" and str(self.servicetype) == "1":
                    self.servicetype = "4097"

                str_servicetype = str(self.servicetype)

                next_url = str(next_url) if next_url else ""

                self.playStream(str_servicetype, next_url)

    def setAspectRatio(self, ar_index):
        try:
            eAVSwitch.getInstance().setAspectRatio(int(ar_index))
        except Exception as e:
            print("[EStalker] setAspectRatio failed: %s" % e)

    def nextARfunction(self):
        self.ar_id_player += 1
        if self.ar_id_player > 6:
            self.ar_id_player = 0
        try:
            eAVSwitch.getInstance().setAspectRatio(self.ar_id_player)
            return VIDEO_ASPECT_RATIO_MAP[self.ar_id_player]
        except Exception as e:
            print(e)
            return _("Resolution Change Failed")

    def nextAR(self):
        message = self.nextARfunction()
        self.session.open(MessageBox, message, type=MessageBox.TYPE_INFO, timeout=1)

    def createLink(self, url, params):
        response = make_request(url, method="GET", headers=self.headers, params=params, response_type="json")

        if not response:
            self.reauthorize()
            response = make_request(url, method="GET", headers=self.headers, params=params, response_type="json")

        return response

    def resolveVodCommand(self, command, series="", metadata=None, media_id=""):
        if not isinstance(command, str):
            return ""

        metadata = metadata if isinstance(metadata, dict) else {}

        if command.startswith("/media/") and media_id:
            content_type = "series" if glob.categoryname == "series" else "vod"
            media_params = {
                "type": content_type,
                "action": "get_ordered_list",
                "movie_id": str(media_id),
                "category": "1",
                "sortby": "",
                "p": "1",
                "JsHttpRequest": "1-xml",
            }
            if content_type == "series":
                media_params.update({
                    "season_id": "0",
                    "episode_id": "0",
                })

            media_response = make_request(
                self.portal,
                method="GET",
                headers=self.headers,
                params=media_params,
                response_type="json"
            )
            if not media_response:
                self.reauthorize()
                media_response = make_request(
                    self.portal,
                    method="GET",
                    headers=self.headers,
                    params=media_params,
                    response_type="json"
                )

            media_js = media_response.get("js", {}) if isinstance(media_response, dict) else {}
            media_items = media_js.get("data", []) if isinstance(media_js, dict) else media_js
            if isinstance(media_items, list) and media_items:
                media_item = media_items[0] if isinstance(media_items[0], dict) else {}
                resolved_media_id = media_item.get("id")
                if resolved_media_id:
                    extension = os.path.splitext(command)[1]
                    command = "/media/file_{}{}".format(resolved_media_id, extension)

        create_link_required = "://" not in command or metadata.get("protocol") == "custom"
        stream_url = command

        if create_link_required:
            params = {
                "type": "vod",
                "action": "create_link",
                "cmd": command,
                "series": series or "",
                "forced_storage": metadata.get("forced_storage", ""),
                "disable_ad": metadata.get("disable_ad", "0"),
                "download": metadata.get("download", "0"),
                "force_ch_link_check": "0",
                "JsHttpRequest": "1-xml",
            }
            response = self.createLink(self.portal, params)
            stream_url = ""
            link_error = ""
            link_data = response.get("js", {}) if isinstance(response, dict) else {}

            if isinstance(link_data, list):
                for candidate in link_data:
                    if isinstance(candidate, dict) and candidate.get("type") != "ad" and candidate.get("cmd"):
                        stream_url = str(candidate.get("cmd"))
                        self.storage_id = str(candidate.get("storage_id", ""))
                        break
            elif isinstance(link_data, dict):
                stream_url = str(link_data.get("cmd", ""))
                self.storage_id = str(link_data.get("storage_id", ""))
                link_error = str(link_data.get("error", ""))

            if not stream_url:
                error_messages = {
                    "limit": _("Maximum number of connections reached."),
                    "nothing_to_play": _("Nothing to play."),
                    "link_fault": _("Server error or invalid link."),
                    "access_denied": _("Access denied."),
                }
                self.session.open(MessageBox, error_messages.get(link_error, _("Server error or invalid link.")), MessageBox.TYPE_ERROR, timeout=3)
                return ""

        stream_url = re.sub(r"%mac%", self.mac, stream_url, flags=re.IGNORECASE)
        parts = stream_url.split(None, 1)
        if len(parts) == 2:
            stream_url = parts[1].lstrip()

        parsed = urlparse(stream_url)
        if parsed.scheme in ("http", "https"):
            stream_url = parsed.geturl()

        return stream_url

    def reauthorize(self):
        result = reauthorize_portal(self.portal, self.host, self.mac, self.headers)

        if not result:
            return

        self.portal, self.token, self.token_random, self.headers, play_token, status, blocked = result

        glob.active_playlist["playlist_info"].update({
            "portal": self.portal,
            "token": self.token,
            "token_random": self.token_random,
            "headers": self.headers,
            "play_token": play_token,
            "status": status,
            "blocked": blocked,
        })

        try:
            with open(self.playlists_json, "r") as f:
                playlists_all = json.load(f)

            for index, playlist in enumerate(playlists_all):
                playlist_info = playlist.get("playlist_info", {})
                if (
                    playlist_info.get("domain") == glob.active_playlist["playlist_info"].get("domain")
                    and playlist_info.get("mac") == glob.active_playlist["playlist_info"].get("mac")
                ):
                    playlists_all[index] = glob.active_playlist
                    break

            with open(self.playlists_json, "w") as f:
                json.dump(playlists_all, f, indent=4)
        except (IOError, OSError, ValueError, TypeError):
            pass
