#!/usr/bin/python
# -*- coding: utf-8 -*-

from __future__ import absolute_import, print_function
from __future__ import division

# Standard library imports
import json
import os
import re
import time
from datetime import datetime
from itertools import cycle, islice
import hashlib
import tempfile

try:
    from urlparse import urlparse, parse_qs, urlunparse
    from urllib import unquote, quote
except ImportError:
    from urllib.parse import urlparse, parse_qs, urlunparse
    from urllib.parse import unquote, quote


try:
    from http.client import HTTPConnection
    HTTPConnection.debuglevel = 0
except ImportError:
    from httplib import HTTPConnection
    HTTPConnection.debuglevel = 0

# Third-party imports
from PIL import Image
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
from Components.ProgressBar import ProgressBar
from Components.Pixmap import MultiPixmap, Pixmap
from Components.ServiceEventTracker import ServiceEventTracker, InfoBarBase
from enigma import eTimer, eServiceReference, iPlayableService
from Screens.InfoBarGenerics import InfoBarSeek, InfoBarAudioSelection, InfoBarSummarySupport, InfoBarMoviePlayerSummarySupport, InfoBarSubtitleSupport
from Screens.MessageBox import MessageBox
from Screens.Screen import Screen
from Tools.BoundFunction import boundFunction
from Tools.LoadPixmap import LoadPixmap

try:
    from enigma import eAVSwitch
except Exception:
    from enigma import eAVControl as eAVSwitch

# Local application/library-specific imports
from . import _
from . import estalker_globals as glob
from .plugin import cfg, common_path, dir_tmp, pythonVer, screenwidth, skin_directory, debugs
from .eStaticText import StaticText
from .utils import get_local_timezone, make_request, perform_handshake, get_profile_data

playlists_json = cfg.playlists_json.value


if pythonVer == 3:
    superscript_to_normal = str.maketrans(
        '⁰¹²³⁴⁵⁶⁷⁸⁹ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖʳˢᵗᵘᵛʷˣʸᶻ'
        'ᴬᴮᴰᴱᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾᴿᵀᵁⱽᵂ⁺⁻⁼⁽⁾',
        '0123456789abcdefghijklmnoprstuvwxyz'
        'ABDEGHIJKLMNOPRTUVW+-=()'
    )


def normalize_superscripts(text):
    return text.translate(superscript_to_normal)


def clean_names(response):
    if "js" in response and "data" in response["js"]:
        data_block = response["js"]["data"]

        if isinstance(data_block, list):
            for item in data_block:
                if isinstance(item, dict):
                    if "name" in item and isinstance(item["name"], str):
                        item["name"] = normalize_superscripts(item["name"])
    return response


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


class EStalker_StreamPlayer(
    InfoBarBase,
    IPTVInfoBarShowHide,
    IPTVInfoBarPVRState,
    InfoBarAudioSelection,
    InfoBarSeek,
    InfoBarSummarySupport,
    InfoBarSubtitleSupport,
    InfoBarMoviePlayerSummarySupport,
        Screen):

    ALLOW_SUSPEND = True

    def __init__(self, session, streamurl, servicetype, stream_id=None):
        Screen.__init__(self, session)
        self.session = session

        if str(os.path.splitext(streamurl)[-1]) == ".m3u8" and servicetype == "1":
            servicetype = "4097"

        for x in (
            InfoBarBase,
            IPTVInfoBarShowHide,
            InfoBarAudioSelection,
            InfoBarSeek,
            InfoBarSummarySupport,
            InfoBarSubtitleSupport,
            InfoBarMoviePlayerSummarySupport
        ):
            x.__init__(self)

        IPTVInfoBarPVRState.__init__(self, PVRState, True)

        self.streamurl = streamurl
        self.servicetype = servicetype
        self.originalservicetype = self.servicetype

        skin_path = os.path.join(skin_directory, cfg.skin.value)
        skin = os.path.join(skin_path, "streamplayer.xml")
        with open(skin, "r") as f:
            self.skin = f.read()

        self["x_description"] = StaticText()
        self["nowchannel"] = StaticText()
        self["nowtitle"] = StaticText()
        self["nexttitle"] = StaticText()
        self["nowtime"] = StaticText()
        self["nexttime"] = StaticText()
        self["streamcat"] = StaticText()
        self["streamtype"] = StaticText()
        self["extension"] = StaticText()

        self["progress"] = ProgressBar()
        self["progress"].hide()

        self["picon"] = Pixmap()
        self["PTSSeekBack"] = Pixmap()
        self["PTSSeekPointer"] = Pixmap()

        self["eventname"] = Label()
        self["state"] = Label()
        self["speed"] = Label()
        self["statusicon"] = MultiPixmap()

        self.ar_id_player = 0

        self.setup_title = _("TV")

        self.retry = False

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

        self.headers = {
            "Pragma": "no-cache",
            "Accept-Language": "en-US,en;q=0.5",
            "Accept-Encoding": "gzip, deflate",
            "Host": "{}:{}".format(self.domain, self.port) if self.port else self.domain,
            "User-Agent": "Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 (KHTML, like Gecko) MAG200 stbapp ver: 2 rev: 250 Safari/533.3",
            "X-User-Agent": "Model: MAG250; Link: WiFi",
            "Connection": "Close",
            "Referer": self.referer,
        }

        if self.portal and "/stalker_portal/" in self.portal:
            host_headers = {
                "Cookie": "mac={}; stb_lang=en; timezone={}; adid={}".format(encoded_mac, encoded_timezone, self.adid)
            }
        else:
            host_headers = {
                "Cookie": "mac={}; stb_lang=en; timezone={}".format(encoded_mac, encoded_timezone)
            }

        self.headers.update(host_headers)

        self.headers["Authorization"] = "Bearer " + self.token

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
            "0": self.restartStream,
            "ok": self.OKButton,
        }, -2)

        self.timerImage = eTimer()
        try:
            self.timerImage.callback.append(self.downloadImage)
        except:
            self.timerImage_conn = self.timerImage.timeout.connect(self.downloadImage)

        self.timerRecent = eTimer()
        try:
            self.timerRecent.callback.append(self.addRecentLiveList)
        except:
            self.timerRecent_conn = self.timerRecent.timeout.connect(self.addRecentLiveList)

        self.timerWatchdog = eTimer()
        try:
            self.timerWatchdog.callback.append(self.sendWatchdog)
        except:
            self.timerWatchdog_conn = self.timerWatchdog.timeout.connect(self.sendWatchdog)

        # Pagination variables - add these
        self.all_data = []
        self.pages_downloaded = set()
        self.current_page = 1
        self.itemsperpage = 14
        self.total_items = 0
        self.sortby = "number"
        self.epg_downloaded_channels = set()
        self.short_epg_results = {}

        self.onFirstExecBegin.append(boundFunction(self.playStream, self.servicetype, self.streamurl))

    def sendWatchdog(self):
        if debugs:
            print("*** sendWatchdog ***")

        watchdog_url = "{0}?type=watchdog&action=get_events&cur_play_type=0&event_active_id=0&init=0&JsHttpRequest=1-xml".format(self.portal)
        make_request(watchdog_url, method="GET", headers=self.headers, params=None, response_type="json")

        # restart timer for next ping
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

    def restartStream(self):
        if debugs:
            print("*** restartStream ***")

        if self.session:
            self.session.nav.stopService()
            self.playStream(self.servicetype, self.streamurl)

    def OKButton(self):
        if debugs:
            print("*** OK Button ***")

        self.refreshInfobar()
        IPTVInfoBarShowHide.OkPressed(self)

    # this needs re-coding
    def refreshInfobar(self):
        if debugs:
            print("*** refreshInfobar ***")

        if glob.currentepglist:
            startnowunixtime = glob.currentepglist[glob.currentchannellistindex][9]
            startnextunixtime = glob.currentepglist[glob.currentchannellistindex][10]

            percent = 0

            if startnowunixtime and startnextunixtime:
                self["progress"].show()

                now = int(time.time())
                total_time = startnextunixtime - startnowunixtime
                elapsed = now - startnowunixtime

                percent = int(elapsed / total_time * 100) if total_time > 0 else 0

                self["progress"].setValue(percent)
            else:
                self["progress"].hide()

            self["x_description"].setText(glob.currentepglist[glob.currentchannellistindex][4])
            self["nowchannel"].setText(glob.currentchannellist[glob.currentchannellistindex][0])
            self["nowtitle"].setText(glob.currentepglist[glob.currentchannellistindex][3])
            self["nexttitle"].setText(glob.currentepglist[glob.currentchannellistindex][6])
            self["nowtime"].setText(glob.currentepglist[glob.currentchannellistindex][2])
            self["nexttime"].setText(glob.currentepglist[glob.currentchannellistindex][5])
        else:
            self["x_description"].setText("")
            self["nowchannel"].setText(glob.currentchannellist[glob.currentchannellistindex][0])
            self["nowtitle"].setText("")
            self["nexttitle"].setText("")
            self["nowtime"].setText("")
            self["nexttime"].setText("")

    def addRecentLiveList(self):
        if glob.adultChannel:
            return

        name = glob.originalChannelList2[glob.currentchannellistindex][1]
        id = glob.originalChannelList2[glob.currentchannellistindex][2]
        logo = glob.originalChannelList2[glob.currentchannellistindex][3]
        xmltv_id = glob.originalChannelList2[glob.currentchannellistindex][4]
        number = glob.originalChannelList2[glob.currentchannellistindex][5]
        tv_genre_id = glob.originalChannelList2[glob.currentchannellistindex][6]
        cmd = glob.originalChannelList2[glob.currentchannellistindex][7]

        # Remove existing entry if stream_id matches
        recent_entries = glob.active_playlist["player_info"]["liverecents"]
        recent_entries[:] = [recent for recent in recent_entries if recent["id"] != id]

        new_recent = {
            "name": name,
            "id": id,
            "logo": logo,
            "xmltv_id": xmltv_id,
            "number": number,
            "tv_genre_id": tv_genre_id,
            "cmd": cmd
        }

        recent_entries.insert(0, new_recent)

        if len(recent_entries) >= 28:
            recent_entries.pop()

        self.playlists_all = []
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
            for playlists in self.playlists_all:
                if (playlists["playlist_info"]["host"] == glob.active_playlist["playlist_info"]["host"] and playlists["playlist_info"]["mac"] == glob.active_playlist["playlist_info"]["mac"]):
                    playlists.update(glob.active_playlist)
                    break
        with open(playlists_json, "w") as f:
            json.dump(self.playlists_all, f, indent=4)

    def playStream(self, servicetype, streamurl):
        if debugs:
            print("*** playStream ***")

        self._stopTimer("timerImage")
        self._stopTimer("timerRecent")

        if not streamurl:
            return

        self["streamcat"].setText("Live")
        self["streamtype"].setText(str(servicetype))

        try:
            path = urlparse(streamurl).path
            path = unquote(path)
            ext = os.path.splitext(path)[-1].lower()
            if ext in [".ts", ".m3u8"]:
                self["extension"].setText(ext)
            else:
                self["extension"].setText("")
        except:
            pass

        self.reference = eServiceReference(int(servicetype), 0, str(streamurl))
        self.reference.setName(glob.currentchannellist[glob.currentchannellistindex][0])

        def strip_query_from_ref(ref):
            if not ref:
                return ""

            s = ref.toString() if hasattr(ref, "toString") else str(ref)

            # Only decode if it's bytes (Python 2 compatibility)
            if isinstance(s, bytes):
                try:
                    s = s.decode("utf-8")
                except:
                    s = s.decode("latin-1", "ignore")

            parsed = urlparse(s)
            query = parse_qs(parsed.query)

            if "stream" in query:
                new_query = "stream=" + query["stream"][0]
            else:
                new_query = ""

            return urlunparse((parsed.scheme, parsed.netloc, parsed.path, '', new_query, ''))

        playing = self.session.nav.getCurrentlyPlayingServiceReference()

        if playing:
            current_ref = strip_query_from_ref(playing)
            new_ref = strip_query_from_ref(self.reference)

            if current_ref != new_ref:
                try:
                    self.session.nav.playService(self.reference)
                except Exception as e:
                    print(e)
        else:
            try:
                self.session.nav.playService(self.reference)
            except Exception as e:
                print(e)

        nowref = self.session.nav.getCurrentlyPlayingServiceReference()
        if nowref:
            glob.newPlayingServiceRef = nowref
            glob.newPlayingServiceRefString = nowref.toString()

        if cfg.infobarpicons.value is True:
            self.timerImage.start(250, True)

        # add to recently watched
        self.timerRecent.start(5 * 60 * 1000, True)

        # start watchdog
        self._stopTimer("timerWatchdog")
        self.timerWatchdog.start(30000, True)

        self.originalservicetype = self.servicetype

        self.refreshInfobar()

    def back(self):
        if debugs:
            print("*** back ***")

        self._cleanupTimer("timerImage")
        self._cleanupTimer("timerRecent")
        self._cleanupTimer("timerWatchdog")

        glob.nextlist[-1]["index"] = glob.currentchannellistindex

        self.close()

    def toggleStreamType(self):
        if debugs:
            print("*** toggleStreamType ***")

        current_index = 0
        for index, item in enumerate(streamtypelist):
            if str(item) == str(self.servicetype):
                current_index = index
                break
        next_stream_type = islice(cycle(streamtypelist), current_index + 1, None)
        try:
            self.servicetype = int(next(next_stream_type))
        except:
            pass

        self.playStream(self.servicetype, self.streamurl)

    def downloadImage(self):
        # Clear picon immediately on zap so previous one doesn't remain if new fails
        self.loadDefaultImage()

        try:
            self._picon_req_id += 1
        except:
            self._picon_req_id = 1

        req_id = self._picon_req_id

        desc_image = ""
        try:
            desc_image = glob.currentchannellist[glob.currentchannellistindex][5]
        except:
            desc_image = ""

        if not desc_image or desc_image == "n/A":
            return

        fd = None
        temp = None

        try:
            fd, temp = tempfile.mkstemp(prefix="xst_picon_", suffix=".png", dir=dir_tmp)
            try:
                os.close(fd)
            except:
                pass

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
                # Ignore stale callbacks (e.g. user zapped again)
                if getattr(self, "_picon_req_id", 0) != req_id:
                    _cleanup_temp()
                    return

                self.resizeImage(temp)

            def _err(_failure=None):
                # Ignore stale callbacks
                if getattr(self, "_picon_req_id", 0) != req_id:
                    _cleanup_temp()
                    return

                _cleanup_temp()
                self.loadDefaultImage()

            if scheme == "https" and sslverify:
                sniFactory = SNIFactory(domain)
                d = downloadPage(url, temp, sniFactory, timeout=2)
            else:
                d = downloadPage(url, temp, timeout=2)

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

    def loadDefaultImage(self, data=None):
        if debugs:
            print("*** loadDefaultImage ***")

        if self["picon"].instance:
            self["picon"].instance.setPixmapFromFile(os.path.join(common_path, "picon.png"))

    def resizeImage(self, original, data=None):
        if screenwidth.width() == 2560:
            size = [294, 176]
        elif screenwidth.width() > 1280:
            size = [220, 130]
        else:
            size = [147, 88]

        if os.path.exists(original):
            im = None
            try:
                im = Image.open(original)
                if im.mode != "RGBA":
                    im = im.convert("RGBA")

                try:
                    im.thumbnail(size, Image.Resampling.LANCZOS)
                except:
                    im.thumbnail(size, Image.ANTIALIAS)

                bg = Image.new("RGBA", size, (255, 255, 255, 0))
                left = (size[0] - im.size[0]) // 2
                top = (size[1] - im.size[1]) // 2
                bg.paste(im, (left, top), mask=im)
                bg.save(original, "PNG")

                if self["picon"].instance:
                    self["picon"].instance.setPixmapFromFile(original)

            except Exception as e:
                print("Error resizing image:", e)
                self.loadDefaultImage()
            finally:
                if im is not None:
                    try:
                        im.close()
                    except:
                        pass

            try:
                os.remove(original)
            except:
                pass
        else:
            self.loadDefaultImage()

    def createLink(self, url):
        if debugs:
            print("*** createLink ***", url)

        response = make_request(url, method="GET", headers=self.headers, params=None, response_type="json")

        if debugs:
            print("*** createlink response ***", response)

        if not response and self.retry is False:
            self.retry = True
            self.reauthorize()
            response = make_request(url, method="GET", headers=self.headers, params=None, response_type="json")
            if debugs:
                print("*** createlink response 2 ***", response)

        return response

    def _get_profile(self, portal, mac, token, token_random, headers, param_mode):
        return get_profile_data(portal, mac, token, token_random, headers, param_mode)

    def _get_account_info(self, portal, mac, token, token_random, headers):
        account_info_url = "{}?".format(portal)
        account_info_params = {
            "type": "account_info",
            "action": "get_main_info",
            "JsHttpRequest": "1-xml",
        }
        account_info = make_request(account_info_url, method="GET", headers=headers, params=account_info_params, response_type="json")

        if debugs:
            print("*** account_info ***", account_info)

        if account_info and isinstance(account_info, dict):
            js_data = account_info.get("js") or {}
            expiry = js_data.get("phone") or js_data.get("end_date", _("Unknown"))
            return expiry, True

        return None, False

    def reauthorize(self):
        if debugs:
            print("*** reauthorize ***")

        self.portal, self.token, self.token_random, self.headers = perform_handshake(portal=self.portal, host=self.host, mac=self.mac, headers=self.headers)

        if not self.token:
            return

        play_token, status, blocked, returned_mac, returned_id = self._get_profile(
            self.portal, self.mac, self.token, self.token_random, self.headers, param_mode="full"
        )

        expiry, account_valid = self._get_account_info(self.portal, self.mac, self.token, self.token_random, self.headers)

        if not account_valid:
            play_token, status, blocked, returned_mac, returned_id = self._get_profile(self.portal, self.mac, self.token, self.token_random, self.headers, "basic")

        glob.active_playlist["playlist_info"]["token"] = self.token
        glob.active_playlist["playlist_info"]["token_random"] = self.token_random
        glob.active_playlist["playlist_info"]["play_token"] = play_token
        glob.active_playlist["playlist_info"]["status"] = status
        glob.active_playlist["playlist_info"]["blocked"] = blocked

    def __next__(self):
        if debugs:
            print("*** __next___ ***")

        self.servicetype = self.originalservicetype

        if glob.currentchannellist:
            list_length = len(glob.currentchannellist)
            glob.currentchannellistindex += 1
            if glob.currentchannellistindex >= list_length:
                glob.currentchannellistindex = 0
                glob.nextlist[-1]["index"] = glob.currentchannellistindex

            command = str(glob.currentchannellist[glob.currentchannellistindex][7])

            if not command:
                self.load_page_data()
                command = str(glob.currentchannellist[glob.currentchannellistindex][7])

            if isinstance(command, str):
                if ("localhost" in command or "///" in command or "/ch/" in command or "http" not in command):
                    url = "{0}?type=itv&action=create_link&cmd={1}&series=0&forced_storage=0&disable_ad=0&download=0&force_ch_link_check=0&JsHttpRequest=1-xml".format(self.portal, command)
                    self.retry = False
                    response = self.createLink(url)
                    self.streamurl = ""

                    if isinstance(response, dict) and "js" in response and "cmd" in response["js"]:
                        self.streamurl = str(response["js"]["cmd"])
                else:
                    self.streamurl = command

            if isinstance(self.streamurl, str):
                parts = self.streamurl.split(None, 1)
                if len(parts) == 2:
                    self.streamurl = parts[1].lstrip()

                parsed = urlparse(self.streamurl)
                if parsed.scheme in ["http", "https"]:
                    self.streamurl = parsed.geturl()

            else:
                self.streamurl = ""

            str_servicetype = str(self.servicetype)
            str_streamurl = str(self.streamurl) if self.streamurl else ""

            self.playStream(str_servicetype, str_streamurl)

    def prev(self):
        if debugs:
            print("*** prev ***")

        self.servicetype = self.originalservicetype

        if glob.currentchannellist:
            list_length = len(glob.currentchannellist)
            glob.currentchannellistindex -= 1
            if glob.currentchannellistindex < 0:
                glob.currentchannellistindex = list_length - 1
                glob.nextlist[-1]["index"] = glob.currentchannellistindex

            command = str(glob.currentchannellist[glob.currentchannellistindex][7])

            if not command:
                self.load_page_data()
                command = str(glob.currentchannellist[glob.currentchannellistindex][7])

            if isinstance(command, str):
                if ("localhost" in command or "///" in command or "/ch/" in command or "http" not in command):
                    url = "{0}?type=itv&action=create_link&cmd={1}&series=0&forced_storage=0&disable_ad=0&download=0&force_ch_link_check=0&JsHttpRequest=1-xml".format(self.portal, command)
                    self.retry = False
                    response = self.createLink(url)
                    self.streamurl = ""

                    if isinstance(response, dict) and "js" in response and "cmd" in response["js"]:
                        self.streamurl = str(response["js"]["cmd"])
                else:
                    self.streamurl = command

            if isinstance(self.streamurl, str):
                parts = self.streamurl.split(None, 1)
                if len(parts) == 2:
                    self.streamurl = parts[1].lstrip()

                parsed = urlparse(self.streamurl)
                if parsed.scheme in ["http", "https"]:
                    self.streamurl = parsed.geturl()
            else:
                self.streamurl = ""

            str_servicetype = str(self.servicetype)
            str_streamurl = str(self.streamurl) if self.streamurl else ""

            self.playStream(str_servicetype, str_streamurl)

    def nextARfunction(self):
        if debugs:
            print("*** nextARfunction ***")

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
        if debugs:
            print("*** nextAR ***")

        message = self.nextARfunction()
        self.session.open(MessageBox, message, type=MessageBox.TYPE_INFO, timeout=1)

    def load_page_data(self):
        self.pages_downloaded = set()
        self.retry = False

        self.itemsperpage = 14
        current_index = glob.currentchannellistindex
        position = current_index + 1
        page = (position - 1) // self.itemsperpage + 1

        if not hasattr(self, 'current_page') or page != self.current_page:
            self.current_page = page
            response = self.downloadApiData(glob.nextlist[-1]["next_url"])
            self.processdata(response)

    def downloadApiData(self, url, page=1):
        if debugs:
            print("*** downloadApiData ***", url)

        # Initialize storage for all data if it doesn't exist
        if not hasattr(self, 'all_data') or not isinstance(self.all_data, list):
            self.all_data = []

        if "all_channels" not in url:
            paged_url = self._updateUrlPage(url, self.current_page)
        else:
            paged_url = url

        if paged_url in self.pages_downloaded:
            return self.all_data

        try:
            data = make_request(paged_url, method="GET", headers=self.headers, params=None, response_type="json")

            if not data and self.retry is False:
                self.retry = True
                self.reauthorize()
                data = make_request(paged_url, method="GET", headers=self.headers, params=None, response_type="json")

            if data:
                if pythonVer == 3 and glob.hassuperscript:
                    data = clean_names(data)

                js = data.get("js", {})

                try:
                    self.total_items = int(js.get("total_items", 0))
                except (ValueError, TypeError):
                    self.total_items = 0
                current_page_data = js.get("data", [])

                if "all_channels" in url:
                    return current_page_data

                if not hasattr(self, 'all_data') or not isinstance(self.all_data, list) or not self.all_data:
                    self.all_data = [{} for _ in range(self.total_items)]

                # Calculate the position where this page's data should be stored
                start_index = (self.current_page - 1) * 14

                # Insert the new data at the correct positions
                for i, item in enumerate(current_page_data):
                    self.all_data[start_index + i] = item
                    self.pages_downloaded.add(paged_url)

                return self.all_data

        except Exception as e:
            print("Error downloading API data for page {}: {}".format(self.current_page, e))
            return self.all_data

        self.session.openWithCallback(self.back, MessageBox, _("Server error or invalid link."), MessageBox.TYPE_ERROR, timeout=3)
        return self.all_data

    def _updateUrlPage(self, url, page):
        if "p=" in url:
            return re.sub(r"p=\d+", "p=" + str(page), url)
        else:
            sep = "&" if "?" in url else "?"
            return url + sep + "p=" + str(page)

    def processdata(self, response):
        if debugs:
            print("*** processdata ***")
        self.list2 = []

        if response:
            for index, channel in enumerate(response):
                if not isinstance(channel, dict) or not channel:
                    self.list2.append([index, "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", False, False, False, None, None])
                    continue

                stream_id = str(channel.get("id", ""))

                if not stream_id or stream_id == "0" or stream_id == "*":
                    continue

                name = str(channel.get("name", ""))

                if not name or name == "None":
                    continue

                if name and '\" ' in name:
                    parts = name.split('\" ', 1)
                    if len(parts) > 1:
                        name = parts[0]

                number = str(channel.get("number", ""))
                cmd = str(channel.get("cmd", ""))
                hidden = False
                stream_icon = str(channel.get("logo", ""))

                if stream_icon and stream_icon.startswith("http"):
                    if stream_icon.startswith("https://vignette.wikia.nocookie.net/tvfanon6528"):
                        if "scale-to-width-down" not in stream_icon:
                            stream_icon = str(stream_icon) + "/revision/latest/scale-to-width-down/220"
                else:
                    stream_icon = ""

                epg_channel_id = str(channel.get("id", ""))
                category_id = str(channel.get("tv_genre_id", ""))
                service_ref = ""
                next_url = ""
                favourite = False

                if "livefavourites" in glob.active_playlist["player_info"]:
                    for fav in glob.active_playlist["player_info"]["livefavourites"]:

                        if str(stream_id) == str(fav["id"]):
                            favourite = True
                            break
                else:
                    glob.active_playlist["player_info"]["livefavourites"] = []

                self.list2.append([
                    index,
                    str(name),
                    str(stream_id),
                    str(stream_icon),
                    str(epg_channel_id),
                    str(number),
                    str(category_id),
                    str(cmd),
                    str(service_ref),
                    "",
                    "",
                    "",
                    "",
                    "",
                    "",
                    str(next_url),
                    favourite,
                    False,
                    hidden,
                    None,
                    None
                ])

        self.main_list = [buildLiveStreamList(x[0], x[1], x[2], x[3], x[5], x[7], x[15], x[16], x[17], x[18], x[6]) for x in self.list2 if x[18] is False]
        glob.currentchannellist = self.main_list[:]

        self.updateDisplay()

        self.epglist = [buildEPGListEntry(x[0], x[1], x[9], x[10], x[11], x[12], x[13], x[14], x[18], x[19], x[20]) for x in self.list2 if x[18] is False]
        glob.currentepglist = self.epglist[:]

    def updateDisplay(self):
        visible_channels = self.getVisibleChannels()
        channels_to_fetch = [ch_id for ch_id in visible_channels if ch_id not in self.epg_downloaded_channels]

        if not channels_to_fetch:
            self.updateEPGListWithShortEPG()
            return

        for ch_id in channels_to_fetch:
            self.epg_downloaded_channels.add(ch_id)

        from .getshortepg import EStalker_EPG_Short
        # EStalker_EPG_Short(channels_to_fetch, done_callback=self.handle_epg_done)

        EStalker_EPG_Short(channels_to_fetch, done_callback=self.handle_epg_done, partial_callback=self.handle_epg_partial)

    def getVisibleChannels(self):
        current_index = glob.currentchannellistindex
        position = current_index + 1
        page = (position - 1) // self.itemsperpage + 1
        start = (page - 1) * self.itemsperpage
        end = start + self.itemsperpage
        channel_list = self.main_list if hasattr(self, 'main_list') else []

        return [item[4] for item in channel_list[start:end] if len(item) > 4]

    def handle_epg_done(self, epg_data):
        if not epg_data or "js" not in epg_data:
            return

        for entry in epg_data["js"]:
            ch_id = str(entry.get("ch_id"))
            if not ch_id:
                continue
            if ch_id not in self.short_epg_results:
                self.short_epg_results[ch_id] = []
            self.short_epg_results[ch_id].append(entry)

        self.updateEPGListWithShortEPG()

    def handle_epg_partial(self, result):
        for entry in result.get("js", []):
            ch_id = str(entry.get("ch_id"))
            if not ch_id:
                continue
            if ch_id not in self.short_epg_results:
                self.short_epg_results[ch_id] = []
            self.short_epg_results[ch_id].append(entry)

        self.updateEPGListWithShortEPG()

    def updateEPGListWithShortEPG(self):
        def extract_main_description(descr):
            if not descr:
                return ""

            descr = descr.replace("\r\n", "\n")
            match = re.search(r"Description:\s*(.+)", descr, re.DOTALL)
            if not match:
                return descr.strip()

            description = match.group(1)

            stop_labels = ["Credits:", "Director:", "Producer:", "Actor:", "Category:"]
            for label in stop_labels:
                index = description.find(label)
                if index != -1:
                    description = description[:index]
                    break

            return description.strip()

        now = int(time.time())
        epgoffset_sec = 0

        if self.list2:
            for channel in self.list2:
                epg_channel_id = channel[4]

                if epg_channel_id in self.short_epg_results:
                    events = self.short_epg_results[epg_channel_id]

                    for index, entry in enumerate(events):
                        time_str = entry.get("time", "")
                        time_to_str = entry.get("time_to", "")

                        if time_str and time_to_str:
                            try:
                                dt_start = datetime.strptime(time_str, "%Y-%m-%d %H:%M:%S")
                                dt_stop = datetime.strptime(time_to_str, "%Y-%m-%d %H:%M:%S")

                                start = int(time.mktime(dt_start.timetuple())) + epgoffset_sec
                                stop = int(time.mktime(dt_stop.timetuple())) + epgoffset_sec
                            except Exception:
                                start = 0
                                stop = 0
                        else:
                            start = 0
                            stop = 0

                        next_entry = events[index + 1] if (index + 1) < len(events) else None

                        if start < now and stop > now:
                            channel[9] = str(time.strftime("%H:%M", time.localtime(start)))
                            channel[10] = str(entry.get("name", "") or "")
                            channel[11] = str(extract_main_description(entry.get("descr", "") or ""))
                            channel[19] = start

                            if next_entry:
                                next_start_str = next_entry.get("time", "")
                                try:
                                    dt_next_start = datetime.strptime(next_start_str, "%Y-%m-%d %H:%M:%S")
                                    next_start = int(time.mktime(dt_next_start.timetuple())) + epgoffset_sec
                                except Exception:
                                    next_start = 0

                                channel[12] = str(time.strftime("%H:%M", time.localtime(next_start)) if next_start else "")
                                channel[13] = str(next_entry.get("name", "") or "")
                                channel[14] = str(extract_main_description(next_entry.get("descr", "") or ""))
                                channel[20] = next_start
                            else:
                                channel[12] = ""
                                channel[13] = ""
                                channel[14] = ""
                                channel[20] = 0

                            break

            self.epglist = [
                buildEPGListEntry(x[0], x[1], x[9], x[10], x[11], x[12], x[13], x[14], x[18], x[19], x[20])
                for x in self.list2 if x[18] is False
            ]

            glob.currentepglist = self.epglist[:]


def buildEPGListEntry(index, title, epgNowTime, epgNowTitle, epgNowDesc, epgNextTime, epgNextTitle, epgNextDesc, hidden, epgNowUnixTime, epgNextUnixTime):
    return (title, index, epgNowTime, epgNowTitle, epgNowDesc, epgNextTime, epgNextTitle, epgNextDesc, hidden, epgNowUnixTime, epgNextUnixTime)


def buildLiveStreamList(index, name, stream_id, stream_icon, number, command, next_url, favourite, watching, hidden, category_id):
    png = LoadPixmap(os.path.join(common_path, "play.png"))
    if favourite:
        png = LoadPixmap(os.path.join(common_path, "favourite.png"))
    if watching:
        png = LoadPixmap(os.path.join(common_path, "watching.png"))
    return (name, png, index, next_url, stream_id, stream_icon, number, command, hidden, category_id)
