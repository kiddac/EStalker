#!/usr/bin/python
# -*- coding: utf-8 -*-

# Standard library imports
from __future__ import absolute_import, print_function
from __future__ import division

import json
import hashlib
import os
import re
from itertools import cycle, islice

try:
    from urlparse import urlparse
    from urllib import unquote
except ImportError:
    from urllib.parse import urlparse
    from urllib.parse import unquote
try:
    from http.client import HTTPConnection
    HTTPConnection.debuglevel = 0
except ImportError:
    from httplib import HTTPConnection
    HTTPConnection.debuglevel = 0

# Third-party imports
from PIL import Image, ImageFile, PngImagePlugin
from twisted.web.client import downloadPage

# Enigma2 components
from Components.ActionMap import ActionMap
from Components.Label import Label
from Components.Pixmap import MultiPixmap, Pixmap
from Components.ServiceEventTracker import ServiceEventTracker, InfoBarBase
from enigma import eTimer, eServiceReference, iPlayableService, ePicLoad
from Tools import Notifications
from Screens.InfoBarGenerics import InfoBarSeek, InfoBarAudioSelection, InfoBarSummarySupport, InfoBarMoviePlayerSummarySupport, InfoBarSubtitleSupport, InfoBarNotifications
from Screens.MessageBox import MessageBox
from Screens.Screen import Screen
from Tools.BoundFunction import boundFunction

try:
    from enigma import eAVSwitch
except Exception:
    from enigma import eAVControl as eAVSwitch

try:
    from .resumepoints import setResumePoint, getResumePoint
except ImportError as e:
    print(e)

# Local application/library-specific imports
from . import _
from . import estalker_globals as glob
from .plugin import cfg, dir_tmp, pythonVer, screenwidth, skin_directory, debugs
from .eStaticText import StaticText
from .utils import get_local_timezone, make_request, perform_handshake, get_profile_data

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


# png hack
def mycall(self, cid, pos, length):
    if cid.decode("ascii") == "tRNS":
        return self.chunk_TRNS(pos, length)
    else:
        return getattr(self, "chunk_" + cid.decode("ascii"))(pos, length)


def mychunk_TRNS(self, pos, length):
    i16 = PngImagePlugin.i16
    _simple_palette = re.compile(b"^\xff*\x00\xff*$")
    s = ImageFile._safe_read(self.fp, length)
    if self.im_mode == "P":
        if _simple_palette.match(s):
            i = s.find(b"\0")
            if i >= 0:
                self.im_info["transparency"] = i
        else:
            self.im_info["transparency"] = s
    elif self.im_mode in ("1", "L", "I"):
        self.im_info["transparency"] = i16(s)
    elif self.im_mode == "RGB":
        self.im_info["transparency"] = i16(s), i16(s, 2), i16(s, 4)
    return s


if pythonVer != 2:
    PngImagePlugin.ChunkStream.call = mycall
    PngImagePlugin.PngStream.chunk_TRNS = mychunk_TRNS


_initialized = 0


def _mypreinit():
    global _initialized
    if _initialized >= 1:
        return
    try:
        from . import MyPngImagePlugin
        assert MyPngImagePlugin
    except ImportError:
        pass

    _initialized = 1


Image.preinit = _mypreinit


VIDEO_ASPECT_RATIO_MAP = {
    0: "4:3 Letterbox",
    1: "4:3 PanScan",
    2: "16:9",
    3: "16:9 Always",
    4: "16:10 Letterbox",
    5: "16:10 PanScan",
    6: "16:9 Letterbox"
}

streamtypelist = ["1", "4097"]
vodstreamtypelist = ["4097"]

if os.path.exists("/usr/bin/gstplayer"):
    streamtypelist.append("5001")
    vodstreamtypelist.append("5001")


if os.path.exists("/usr/bin/exteplayer3"):
    streamtypelist.append("5002")
    vodstreamtypelist.append("5002")

if os.path.exists("/usr/bin/apt-get"):
    streamtypelist.append("8193")
    vodstreamtypelist.append("8193")


def clear_caches():
    try:
        with open("/proc/sys/vm/drop_caches", "w") as drop_caches:
            drop_caches.write("1\n2\n3\n")
    except IOError:
        pass


playlists_json = cfg.playlists_json.value


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
        self.hideTimer.start(3000, True)

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
            self.hideTimer.start(3000, True)

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

    def __init__(self, session, streamurl, servicetype, stream_id=None):
        Screen.__init__(self, session)
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

        if cfg.subs.value is True:
            SubsSupport.__init__(self, searchSupport=True, embeddedSupport=True)
            SubsSupportStatus.__init__(self)

        self.streamurl = streamurl
        self.servicetype = servicetype
        self.stream_id = stream_id
        self.originalservicetype = self.servicetype

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

        self.ar_id_player = 0

        self.setup_title = _("VOD")

        self.retry = False

        self.timezone = get_local_timezone()
        self.token = glob.active_playlist["playlist_info"]["token"]
        self.token_random = glob.active_playlist["playlist_info"]["token_random"]
        self.domain = str(glob.active_playlist["playlist_info"].get("domain", ""))
        self.host = str(glob.active_playlist["playlist_info"].get("host", "")).rstrip("/")
        self.mac = glob.active_playlist["playlist_info"].get("mac", "").upper()
        self.portal = glob.active_playlist["playlist_info"].get("portal", None)
        self.portal_version = glob.active_playlist["playlist_info"].get("version", "5.3.1")

        self.sn = hashlib.md5(self.mac.encode()).hexdigest().upper()[:13]
        self.device_id = hashlib.sha256(self.mac.encode()).hexdigest().upper()
        self.adid = hashlib.md5((self.sn + self.mac).encode()).hexdigest()

        self.headers = {
            "Host": self.domain,
            "Accept": "*/*",
            "User-Agent": "Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 (KHTML, like Gecko) MAG250 stbapp ver: 2 rev: 369 Safari/533.3",
            "Accept-Encoding": "gzip, deflate",
            "X-User-Agent": "Model: MAG250; Link: WiFi",
            "Connection": "close",
            "Pragma": "no-cache",
            "Cache-Control": "no-store, no-cache, must-revalidate",
        }

        if "/stalker_portal/" in self.portal:
            host_headers = {
                "Cookie": ("mac={}; stb_lang=en; timezone={}; adid={}").format(self.mac, self.timezone, self.adid)
            }
        else:
            host_headers = {

                "Cookie": ("mac={}; stb_lang=en; timezone={}").format(self.mac, self.timezone)
            }

        self.headers.update(host_headers)

        self.headers["Authorization"] = "Bearer " + self.token

        self["actions"] = ActionMap(["EStalkerActions"], {
            "cancel": self.back,
            "stop": self.back,
            "red": self.back,
            "tv": self.toggleStreamType,
            "info": self.toggleStreamType,
            "green": self.nextAR,
            "ok": self.refreshInfobar,
            "channelUp": self.__next__,
            "down": self.__next__,
            "channelDown": self.prev,
            "up": self.prev,
        }, -2)

        self.onFirstExecBegin.append(boundFunction(self.playStream, self.servicetype, self.streamurl))

    def refreshInfobar(self):
        IPTVInfoBarShowHide.OkPressed(self)

    def addWatchedList(self):
        stream_id = self.stream_id

        if glob.categoryname == "vod":
            if stream_id not in glob.active_playlist["player_info"]["vodwatched"]:
                glob.active_playlist["player_info"]["vodwatched"].append(stream_id)

        elif glob.categoryname == "series":
            if stream_id not in glob.active_playlist["player_info"]["serieswatched"]:
                glob.active_playlist["player_info"]["serieswatched"].append(stream_id)

        with open(playlists_json, "r") as f:
            try:
                self.playlists_all = json.load(f)
            except:
                os.remove(playlists_json)

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

    def stripjunk(self, text, database=None):
        searchtitle = text

        # Move "the" from the end to the beginning (case-insensitive)
        if searchtitle.strip().lower().endswith("the"):
            searchtitle = "The " + searchtitle[:-3].strip()

        # remove xx: at start (case-insensitive)
        searchtitle = re.sub(r'^\w{2}:', '', searchtitle, flags=re.IGNORECASE)

        # remove xx|xx at start (case-insensitive)
        searchtitle = re.sub(r'^\w{2}\|\w{2}\s', '', searchtitle, flags=re.IGNORECASE)

        # remove xx - at start (case-insensitive)
        searchtitle = re.sub(r'^.{2}\+? ?- ?', '', searchtitle, flags=re.IGNORECASE)

        # remove all leading content between and including || or |
        searchtitle = re.sub(r'^\|\|.*?\|\|', '', searchtitle)
        searchtitle = re.sub(r'^\|.*?\|', '', searchtitle)
        searchtitle = re.sub(r'\|.*?\|', '', searchtitle)

        # remove all leading content between and including ┃┃ or ┃
        searchtitle = re.sub(r'^┃┃.*?┃┃', '', searchtitle)
        searchtitle = re.sub(r'^┃.*?┃', '', searchtitle)
        searchtitle = re.sub(r'┃.*?┃', '', searchtitle)

        # remove all content between and including () unless it's all digits
        searchtitle = re.sub(r'\((?!\d+\))[^()]*\)', '', searchtitle)

        # remove all content between and including []
        searchtitle = re.sub(r'\[\[.*?\]\]|\[.*?\]', '', searchtitle)

        # remove trailing year (but not if the whole title *is* a year)
        if not re.match(r'^\d{4}$', searchtitle.strip()):
            searchtitle = re.sub(r'[\s\-]*(?:[\(\[\"]?\d{4}[\)\]\"]?)$', '', searchtitle)

        # Bad substrings to strip (case-insensitive)
        bad_strings = [
            "ae|", "al|", "ar|", "at|", "ba|", "be|", "bg|", "br|", "cg|", "ch|", "cz|", "da|", "de|", "dk|",
            "ee|", "en|", "es|", "eu|", "ex-yu|", "fi|", "fr|", "gr|", "hr|", "hu|", "in|", "ir|", "it|", "lt|",
            "mk|", "mx|", "nl|", "no|", "pl|", "pt|", "ro|", "rs|", "ru|", "se|", "si|", "sk|", "sp|", "tr|",
            "uk|", "us|", "yu|",
            "1080p", "1080p-dual-lat-cine-calidad.com", "1080p-dual-lat-cine-calidad.com-1",
            "1080p-dual-lat-cinecalidad.mx", "1080p-lat-cine-calidad.com", "1080p-lat-cine-calidad.com-1",
            "1080p-lat-cinecalidad.mx", "1080p.dual.lat.cine-calidad.com", "3d", "'", "#", "(", ")", "-", "[]", "/",
            "4k", "720p", "aac", "blueray", "ex-yu:", "fhd", "hd", "hdrip", "hindi", "imdb", "multi:", "multi-audio",
            "multi-sub", "multi-subs", "multisub", "ozlem", "sd", "top250", "u-", "uhd", "vod", "x264"
        ]

        bad_strings_pattern = re.compile('|'.join(map(re.escape, bad_strings)), flags=re.IGNORECASE)
        searchtitle = bad_strings_pattern.sub('', searchtitle)

        # Bad suffixes to remove (case-insensitive, only if at end)
        bad_suffix = [
            " al", " ar", " ba", " da", " de", " en", " es", " eu", " ex-yu", " fi", " fr", " gr", " hr", " mk",
            " nl", " no", " pl", " pt", " ro", " rs", " ru", " si", " swe", " sw", " tr", " uk", " yu"
        ]

        bad_suffix_pattern = re.compile(r'(' + '|'.join(map(re.escape, bad_suffix)) + r')$', flags=re.IGNORECASE)
        searchtitle = bad_suffix_pattern.sub('', searchtitle)

        # Replace '.', '_', "'", '*' with space
        searchtitle = re.sub(r'[._\'\*]', ' ', searchtitle)

        # Trim leading/trailing hyphens and whitespace
        searchtitle = searchtitle.strip(' -').strip()

        return str(searchtitle)

    def playStream(self, servicetype, streamurl):
        if cfg.infobarcovers.value is True:
            self.downloadImage()

        self["streamcat"].setText("VOD" if glob.categoryname == "vod" else "Series")
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

        name = self.stripjunk(glob.currentchannellist[glob.currentchannellistindex][0])
        self.reference = eServiceReference(int(self.servicetype), 0, streamurl)
        self.reference.setName(name)

        if self.session.nav.getCurrentlyPlayingServiceReference():
            if self.session.nav.getCurrentlyPlayingServiceReference().toString() != self.reference.toString():

                try:
                    self.session.nav.stopService()
                except:
                    pass

                self.session.nav.playService(self.reference)

        else:
            self.session.nav.playService(self.reference)

        if self.session.nav.getCurrentlyPlayingServiceReference():
            glob.newPlayingServiceRef = self.session.nav.getCurrentlyPlayingServiceReference()
            glob.newPlayingServiceRefString = self.session.nav.getCurrentlyPlayingServiceReference().toString()

            self.timerCache = eTimer()

            try:
                self.timerCache.callback.append(clear_caches)
            except:
                self.timerCache_conn = self.timerCache.timeout.connect(clear_caches)
            self.timerCache.start(5 * 60 * 1000, False)

            self.timerWatched = eTimer()
            try:
                self.timerWatched.callback.append(self.addWatchedList)
            except:
                self.timerWatched_conn = self.timerWatched.timeout.connect(self.addWatchedList)
            self.timerWatched.start(15 * 60 * 1000, True)

    def downloadImage(self):
        self.loadDefaultImage()
        try:
            os.remove(os.path.join(dir_tmp, "cover.jpg"))
        except:
            pass

        desc_image = ""
        try:
            desc_image = glob.currentchannellist[glob.currentchannellistindex][5]
        except:
            pass

        if desc_image and desc_image != "n/A":
            temp = os.path.join(dir_tmp, "cover.jpg")
            try:
                parsed = urlparse(desc_image)
                domain = parsed.hostname
                scheme = parsed.scheme

                if pythonVer == 3:
                    desc_image = desc_image.encode()

                if scheme == "https" and sslverify:
                    sniFactory = SNIFactory(domain)
                    downloadPage(desc_image, temp, sniFactory, timeout=5).addCallback(self.resizeImage).addErrback(self.loadDefaultImage)
                else:
                    downloadPage(desc_image, temp, timeout=5).addCallback(self.resizeImage).addErrback(self.loadDefaultImage)
            except:
                self.loadDefaultImage()
        else:
            self.loadDefaultImage()

    def loadDefaultImage(self, data=None):
        if self["cover"].instance:
            self["cover"].instance.setPixmapFromFile(os.path.join(skin_directory, "common/cover.png"))

    def resizeImage(self, data=None):
        if self["cover"].instance:
            preview = os.path.join(dir_tmp, "cover.jpg")

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
                # if this has failed, then another decode is probably already in progress
                # throw away the old picload and try again immediately
                self.PicLoad = ePicLoad()
                try:
                    self.PicLoad.PictureData.get().append(self.DecodePicture)
                except:
                    self.PicLoad_conn = self.PicLoad.PictureData.connect(self.DecodePicture)
                self.PicLoad.setPara([width, height, 1, 1, 0, 1, "FF000000"])
                self.PicLoad.startDecode(preview)

    def DecodePicture(self, PicInfo=None):
        ptr = self.PicLoad.getData()
        if ptr is not None:
            self["cover"].instance.setPixmap(ptr)
            self["cover"].instance.show()

    def back(self):
        glob.nextlist[-1]["index"] = glob.currentchannellistindex
        try:
            setResumePoint(self.session)
        except Exception as e:
            print(e)

        try:
            self.timerCache.stop()
        except:
            pass

        try:
            self.session.nav.stopService()
        except:
            pass

        try:
            self.session.nav.playService(eServiceReference(glob.currentPlayingServiceRefString))
        except:
            pass

        self.close()

    def toggleStreamType(self):
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

    def createLink(self, url):
        response = make_request(url, method="POST", headers=self.headers, params=None, response_type="json")

        if not response and self.retry is False:
            self.retry = True
            self.reauthorize()
            response = make_request(url, method="POST", headers=self.headers, params=None, response_type="json")

        return response

    def reauthorize(self):
        self.portal, self.token, self.token_random, self.headers = perform_handshake(portal=self.portal, host=self.host, mac=self.mac, headers=self.headers)

        if not self.token:
            return

        play_token, status, blocked, _, returned_mac, returned_id = get_profile_data(
            portal=self.portal,
            mac=self.mac,
            token=self.token,
            token_random=self.token_random,
            headers=self.headers,
            param_mode="full"
        )

        account_info_url = str(self.portal) + "?type=account_info&action=get_main_info&JsHttpRequest=1-xml"
        account_info = make_request(account_info_url, method="POST", headers=self.headers, params=None, response_type="json")

        if not account_info and isinstance(account_info, dict):
            if not returned_mac or not returned_id:
                play_token, status, blocked, _, returned_mac, returned_id = get_profile_data(
                    portal=self.portal,
                    mac=self.mac,
                    token=self.token,
                    token_random=self.token_random,
                    headers=self.headers,
                    param_mode="basic"
                )

        glob.active_playlist["playlist_info"]["token"] = self.token
        glob.active_playlist["playlist_info"]["token_random"] = self.token_random
        glob.active_playlist["playlist_info"]["play_token"] = play_token
        glob.active_playlist["playlist_info"]["status"] = status
        glob.active_playlist["playlist_info"]["blocked"] = blocked

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
                next_url = command

                if str(command).startswith("/media/"):
                    pre_vod_url = (str(self.portal) + "?type=vod&action=get_ordered_list&movie_id={}&season_id=0&episode_id=0&category=1&fav=0&sortby=&hd=0&not_ended=0&p=1&JsHttpRequest=1-xml").format(self.stream_id)

                    pre_response = make_request(pre_vod_url, method="POST", headers=self.headers, params=None, response_type="json")

                    movie_id = None

                    js_data = pre_response.get("js", {}).get("data", [])

                    if isinstance(js_data, list) and len(js_data) > 0:
                        movie_id = js_data[0].get("id")
                    if movie_id:
                        # Extract the file extension from the original command
                        ext = ""
                        if "." in command:
                            ext = command[command.rfind("."):]

                        command = "/media/file_{}{}".format(movie_id, ext)

                if isinstance(command, str):
                    if "localhost" in command or "http" not in command or "///" in command:
                        url = "{0}?type=vod&action=create_link&cmd={1}&series={2}&forced_storage=&disable_ad=0&download=0&force_ch_link_check=0&JsHttpRequest=1-xml".format(self.portal, command, episode_id)
                        self.retry = False
                        response = self.createLink(url)
                        next_url = ""

                        if isinstance(response, dict) and "js" in response and "cmd" in response["js"]:
                            next_url = str(response["js"]["cmd"])

                    else:
                        next_url = command

                    if isinstance(next_url, str):
                        parts = next_url.split(None, 1)
                        if len(parts) == 2:
                            next_url = parts[1].lstrip()

                        parsed = urlparse(next_url)
                        if parsed.scheme in ["http", "https"]:
                            next_url = parsed.geturl()

                        if str(os.path.splitext(next_url)[-1]) == ".m3u8":
                            if self.streamtype == "1":
                                self.streamtype = "4097"
                    else:
                        next_url = ""

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
                next_url = command

                if str(command).startswith("/media/"):
                    pre_vod_url = (str(self.portal) + "?type=vod&action=get_ordered_list&movie_id={}&season_id=0&episode_id=0&category=1&fav=0&sortby=&hd=0&not_ended=0&p=1&JsHttpRequest=1-xml").format(self.stream_id)

                    pre_response = make_request(pre_vod_url, method="POST", headers=self.headers, params=None, response_type="json")

                    movie_id = None

                    js_data = pre_response.get("js", {}).get("data", [])

                    if isinstance(js_data, list) and len(js_data) > 0:
                        movie_id = js_data[0].get("id")
                    if movie_id:
                        # Extract the file extension from the original command
                        ext = ""
                        if "." in command:
                            ext = command[command.rfind("."):]

                        command = "/media/file_{}{}".format(movie_id, ext)

                if isinstance(command, str):
                    if "localhost" in command or "http" not in command or "///" in command:
                        url = "{0}?type=vod&action=create_link&cmd={1}&series={2}&forced_storage=&disable_ad=0&download=0&force_ch_link_check=0&JsHttpRequest=1-xml".format(self.portal, command, episode_id)
                        self.retry = False
                        response = self.createLink(url)
                        next_url = ""

                        if isinstance(response, dict) and "js" in response and "cmd" in response["js"]:
                            next_url = str(response["js"]["cmd"])

                    else:
                        next_url = command

                    if isinstance(next_url, str):
                        parts = next_url.split(None, 1)
                        if len(parts) == 2:
                            next_url = parts[1].lstrip()

                        parsed = urlparse(next_url)
                        if parsed.scheme in ["http", "https"]:
                            next_url = parsed.geturl()

                        if str(os.path.splitext(next_url)[-1]) == ".m3u8":
                            if self.streamtype == "1":
                                self.streamtype = "4097"
                    else:
                        next_url = ""

                str_servicetype = str(self.servicetype)

                next_url = str(next_url) if next_url else ""

                self.playStream(str_servicetype, next_url)
