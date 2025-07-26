#!/usr/bin/python
# -*- coding: utf-8 -*-

from __future__ import absolute_import, print_function
from __future__ import division

# Standard library imports
import os
import re
import time
from datetime import datetime
from itertools import cycle, islice
import hashlib

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


skin_path = os.path.join(skin_directory, cfg.skin.value)


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

        self.onFirstExecBegin.append(boundFunction(self.playStream, self.servicetype, self.streamurl))

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

            # Check every 5 mins to see if EPG needs to be updated
            nowtime = datetime.now()
            minutes = nowtime.minute
            if minutes % 5 == 1:

                now = int(time.time())

                """
                if startnextunixtime and now >= startnextunixtime:
                    try:
                        player_api = str(glob.active_playlist["playlist_info"]["player_api"])
                        stream_id = str(glob.currentchannellist[glob.currentchannellistindex][4])

                        shortEPGJson = []
                        url = player_api + "&action=get_short_epg&stream_id=" + str(stream_id) + "&limit=2"

                        retries = Retry(total=3, backoff_factor=1)
                        adapter = HTTPAdapter(max_retries=retries)

                        with requests.Session() as http:
                            http.mount("http://", adapter)
                            http.mount("https://", adapter)

                            try:
                                r = http.get(url, headers=hdr, timeout=(10, 20), verify=False)
                                r.raise_for_status()

                                if r.status_code == requests.codes.ok:
                                    response = r.json()
                                    shortEPGJson = response.get("epg_listings", [])
                            except Exception as e:
                                print("Error fetching or processing response:", e)
                                response = None
                                shortEPGJson = []

                        if shortEPGJson and len(shortEPGJson) > 1:
                            self.epgshortlist = []
                            for listing in shortEPGJson:
                                title = base64.b64decode(listing.get("title", "")).decode("utf-8")
                                description = base64.b64decode(listing.get("description", "")).decode("utf-8")
                                shift = int(glob.active_playlist["player_info"].get("serveroffset", 0))
                                start = listing.get("start", "")
                                end = listing.get("end", "")
                                if start and end:
                                    time_formats = ["%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H-%M-%S", "%Y-%m-%d-%H:%M:%S", "%Y- %m-%d %H:%M:%S"]
                                    for time_format in time_formats:
                                        try:
                                            start_datetime = datetime.strptime(start, time_format) + timedelta(hours=shift)
                                            start_time = start_datetime.strftime("%H:%M")
                                            self.epgshortlist.append([str(title), str(description), str(start_time)])
                                            break
                                        except ValueError:
                                            pass

                            templist = list(glob.currentepglist[glob.currentchannellistindex])
                            if self.epgshortlist:
                                templist[4] = str(self.epgshortlist[0][1])  # description
                                templist[3] = str(self.epgshortlist[0][0])  # title
                                templist[2] = str(self.epgshortlist[0][2])  # now start
                                templist[6] = str(self.epgshortlist[1][0])  # next title
                                templist[5] = str(self.epgshortlist[1][2])  # next start

                            glob.currentepglist[glob.currentchannellistindex] = tuple(templist)
                        else:
                            templist = list(glob.currentepglist[glob.currentchannellistindex])
                            templist[4] = glob.currentepglist[glob.currentchannellistindex][7]  # description
                            templist[3] = glob.currentepglist[glob.currentchannellistindex][6]  # title
                            templist[2] = glob.currentepglist[glob.currentchannellistindex][5]  # now start
                            templist[6] = ""  # next title
                            templist[5] = ""  # next start
                            glob.currentepglist[glob.currentchannellistindex] = tuple(templist)
                    except Exception as e:
                        print("Error during short EPG update:", e)
                        """

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

    def playStream(self, servicetype, streamurl):
        if debugs:
            print("*** playStream ***")

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

        startnowunixtime = glob.currentepglist[glob.currentchannellistindex][9]
        startnextunixtime = glob.currentepglist[glob.currentchannellistindex][10]
        service_ref = ""

        if startnowunixtime and startnextunixtime:
            self.unique_ref = 0
            stream_id = str(glob.currentchannellist[glob.currentchannellistindex][4])

            for j in str(self.streamurl):
                value = ord(j)
                self.unique_ref += value

            bouquet_id1 = int(stream_id) // 65535
            bouquet_id2 = int(stream_id) - int(bouquet_id1 * 65535)
            service_ref = eServiceReference(str(servicetype) + ":0:1:" + str(format(bouquet_id1, "x")) + ":" + str(format(bouquet_id2, "x")) + ":" + str(format(self.unique_ref, "x")) + ":0:0:0:0:" + str(streamurl).replace(":", "%3a"))
            service_ref.setName(glob.currentchannellist[glob.currentchannellistindex][0])
            self.reference = service_ref

        if not service_ref:
            if streamurl:
                self.reference = eServiceReference(int(servicetype), 0, str(streamurl))
            else:
                return
            self.reference.setName(glob.currentchannellist[glob.currentchannellistindex][0])

        currently_playing_ref = self.session.nav.getCurrentlyPlayingServiceReference()

        try:
            self.session.nav.stopService()
        except Exception as e:
            print(e)

        try:
            self.session.nav.playService(self.reference)
        except Exception as e:
            print(e)

        currently_playing_ref = self.session.nav.getCurrentlyPlayingServiceReference()

        if currently_playing_ref:
            glob.newPlayingServiceRef = currently_playing_ref
            glob.newPlayingServiceRefString = currently_playing_ref.toString()

        if cfg.infobarpicons.value is True:
            self.timerimage = eTimer()

            try:
                self.timerimage.callback.append(self.downloadImage)
            except:
                self.timerimage_conn = self.timerimage.timeout.connect(self.downloadImage)
            self.timerimage.start(250, True)

        self.timerCache = eTimer()
        try:
            self.timerCache.callback.append(clear_caches)
        except:
            self.timerCache_conn = self.timerCache.timeout.connect(clear_caches)
        self.timerCache.start(5 * 60 * 1000, False)

        self.originalservicetype = self.servicetype

        self.refreshInfobar()

        self.timerrefresh = eTimer()
        try:
            self.timerrefresh.callback.append(self.refreshInfobar)
        except:
            self.timerrefresh_conn = self.timerrefresh.timeout.connect(self.refreshInfobar)

        self.timerrefresh.start(1 * 60 * 1000, False)

    def back(self):
        if debugs:
            print("*** back ***")

        glob.nextlist[-1]["index"] = glob.currentchannellistindex
        try:
            self.timerCache.stop()
        except:
            pass

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
        if debugs:
            print("*** downloadImage ***")

        self.loadDefaultImage()
        try:
            os.remove(os.path.join(dir_tmp, "original.png"))
            os.remove(os.path.join(dir_tmp, "temp.png"))
        except:
            pass

        desc_image = ""
        try:
            desc_image = glob.currentchannellist[glob.currentchannellistindex][5]
        except:
            pass

        if not desc_image:
            self.loadDefaultImage()
            return

        temp = os.path.join(dir_tmp, "temp.png")
        try:
            parsed = urlparse(desc_image)
            domain = parsed.hostname
            scheme = parsed.scheme

            if pythonVer == 3:
                desc_image = desc_image.encode()

            if scheme == "https" and sslverify:
                sniFactory = SNIFactory(domain)
                downloadPage(desc_image, temp, sniFactory, timeout=2).addCallback(self.resizeImage).addErrback(self.loadDefaultImage)
            else:
                downloadPage(desc_image, temp, timeout=2).addCallback(self.resizeImage).addErrback(self.loadDefaultImage)
        except:
            self.loadDefaultImage()

    def loadDefaultImage(self, data=None):
        if debugs:
            print("*** loadDefaultImage ***")

        if self["picon"].instance:
            self["picon"].instance.setPixmapFromFile(os.path.join(common_path, "picon.png"))

    def resizeImage(self, data=None):
        if debugs:
            print("*** resizeImage ***")

        original = os.path.join(dir_tmp, "temp.png")

        # Determine the target size based on screen width
        if screenwidth.width() == 2560:
            size = [294, 176]
        elif screenwidth.width() > 1280:
            size = [220, 130]
        else:
            size = [147, 88]

        if os.path.exists(original):
            try:
                im = Image.open(original)

                if im.mode != "RGBA":
                    im = im.convert("RGBA")

                target_w, target_h = size
                src_w, src_h = im.size

                scale = min(float(target_w) / src_w, float(target_h) / src_h)

                new_w = int(src_w * scale)
                new_h = int(src_h * scale)

                try:
                    resized = im.resize((new_w, new_h), Image.Resampling.LANCZOS)
                except:
                    resized = im.resize((new_w, new_h), Image.ANTIALIAS)

                bg = Image.new("RGBA", (target_w, target_h), (255, 255, 255, 0))

                left = (target_w - new_w) // 2
                top = (target_h - new_h) // 2

                bg.paste(resized, (left, top), mask=resized)

                bg.save(original, "PNG")

                if self["picon"].instance:
                    self["picon"].instance.setPixmapFromFile(original)

            except Exception as e:
                print("Error resizing image:", e)
                self.loadDefaultImage()
        else:
            self.loadDefaultImage()

    def createLink(self, url):
        if debugs:
            print("*** createLink ***", url)

        response = make_request(url, method="POST", headers=self.headers, params=None, response_type="json")

        if debugs:
            print("*** createlink response ***", response)

        if not response and self.retry is False:
            self.retry = True
            self.reauthorize()
            response = make_request(url, method="POST", headers=self.headers, params=None, response_type="json")
            if debugs:
                print("*** createlink response 2 ***", response)

        return response

    def reauthorize(self):
        if debugs:
            print("*** reauthorize ***")

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
        if debugs:
            print("*** __next___ ***")

        self.servicetype = self.originalservicetype

        if glob.currentchannellist:
            list_length = len(glob.currentchannellist)
            glob.currentchannellistindex += 1
            if glob.currentchannellistindex >= list_length:
                glob.currentchannellistindex = 0

            command = glob.currentchannellist[glob.currentchannellistindex][7]

            if isinstance(command, str):
                if "localhost" in command or "http" not in command or "///" in command:
                    url = "{0}?type=itv&action=create_link&cmd={1}&series=0&forced_storage=0&disable_ad=0&download=0&force_ch_link_check=0&JsHttpRequest=1-xml".format(self.portal, command)
                    self.retry = False
                    response = self.createLink(url)
                    self.streamurl = ""

                    if isinstance(response, dict) and "js" in response and "cmd" in response["js"]:
                        self.streamurl = response["js"]["cmd"]
                else:
                    self.streamurl = command

                parts = self.streamurl.split(None, 1)
                if len(parts) == 2:
                    self.streamurl = parts[1].lstrip()

            if isinstance(self.streamurl, str):
                parsed = urlparse(self.streamurl)
                if parsed.scheme in ["http", "https"]:
                    self.streamurl = parsed.geturl()

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

            command = glob.currentchannellist[glob.currentchannellistindex][7]

            if isinstance(command, str):
                if "localhost" in command or "http" not in command or "///" in command:
                    url = "{0}?type=itv&action=create_link&cmd={1}&series=0&forced_storage=0&disable_ad=0&download=0&force_ch_link_check=0&JsHttpRequest=1-xml".format(self.portal, command)
                    self.retry = False
                    response = self.createLink(url)
                    self.streamurl = ""

                    if isinstance(response, dict) and "js" in response and "cmd" in response["js"]:
                        self.streamurl = response["js"]["cmd"]
                else:
                    self.streamurl = command

                parts = self.streamurl.split(None, 1)
                if len(parts) == 2:
                    self.streamurl = parts[1].lstrip()

            if isinstance(self.streamurl, str):
                parsed = urlparse(self.streamurl)
                if parsed.scheme in ["http", "https"]:
                    self.streamurl = parsed.geturl()

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
