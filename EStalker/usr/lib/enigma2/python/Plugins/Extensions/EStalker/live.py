#!/usr/bin/python
# -*- coding: utf-8 -*-

from __future__ import division

# Standard library imports
import codecs
import json
import os
import re
import time
from datetime import datetime, timedelta
from itertools import cycle, islice

import hashlib

# Third-party imports
try:
    from http.client import HTTPConnection
    HTTPConnection.debuglevel = 0
except ImportError:
    from httplib import HTTPConnection
    HTTPConnection.debuglevel = 0

try:
    from urlparse import urlparse
except ImportError:
    from urllib.parse import urlparse

# Third-party imports
from PIL import Image, ImageFile, PngImagePlugin
from twisted.web.client import downloadPage

# Enigma2 components
from Components.ActionMap import ActionMap
from Components.Pixmap import Pixmap
from Components.ProgressBar import ProgressBar
from Components.Sources.List import List
from Screens.MessageBox import MessageBox
from Screens.Screen import Screen
from Screens.VirtualKeyBoard import VirtualKeyBoard
from Tools.LoadPixmap import LoadPixmap
from enigma import eServiceReference, eTimer

# Local imports
from . import _
from . import estalker_globals as glob
from .plugin import cfg, common_path, dir_tmp, pythonVer, screenwidth, skin_directory, debugs
from .eStaticText import StaticText
from .utils import get_local_timezone, make_request, perform_handshake, get_profile_data

# HTTPS twisted client hack
try:
    from twisted.internet import ssl
    from twisted.internet._sslverify import ClientTLSOptions
    sslverify = True
except ImportError:
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


class EStalker_Live_Categories(Screen):
    ALLOW_SUSPEND = True

    def __init__(self, session):
        if debugs:
            print("*** live init ***")

        Screen.__init__(self, session)
        self.session = session
        glob.categoryname = "live"

        self.skin_path = os.path.join(skin_directory, cfg.skin.value)
        skin = os.path.join(self.skin_path, "live_categories.xml")
        if os.path.exists("/var/lib/dpkg/status"):
            skin = os.path.join(self.skin_path, "DreamOS/live_categories.xml")

        with codecs.open(skin, "r", encoding="utf-8") as f:
            self.skin = f.read()

        self.setup_title = _("Live Categories")
        self.main_title = _("Live TV")

        self["main_title"] = StaticText(self.main_title)
        self.main_list = []
        self["main_list"] = List(self.main_list, enableWrapAround=True)

        self["x_title"] = StaticText()
        self["x_description"] = StaticText()

        self["picon"] = Pixmap()
        self["picon"].hide()

        self["progress"] = ProgressBar()
        self["progress"].hide()

        # skin epg variables
        self["epg_bg"] = Pixmap()
        self["epg_bg"].hide()

        self.epglist = []
        self["epg_list"] = List(self.epglist, enableWrapAround=True)

        # skin short epg variables
        self.epgshortlist = []
        self["epg_short_list"] = List(self.epgshortlist, enableWrapAround=True)
        self["epg_short_list"].onSelectionChanged.append(self.displayShortEPG)

        # xmltv variables
        self.xmltvdownloaded = False
        # self.xmltv_channel_list = []

        # pagination variables
        self["page"] = StaticText("")
        self["listposition"] = StaticText("")
        self.itemsperpage = 14

        self.searchString = ""
        self.filterresult = ""
        self.chosen_category = ""

        self.showingshortEPG = False
        self.pin = False
        self.sort_check = False
        self.showfav = False

        self.sortindex = 0
        self.sortText = _("Sort: A-Z")

        self.epgtimeshift = 0
        self.level = 1

        self.selectedlist = self["main_list"]

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

        # device_id = hashlib.sha256(self.sn.encode()).hexdigest().upper()
        # self.device_id2 = self.device_id
        # device_id2 = hashlib.sha256(self.mac.encode()).hexdigest().upper()
        # self.hw_version_2 = hashlib.sha1(self.mac.encode()).hexdigest()
        # self.hw_version_2 = hashlib.sha1((self.mac + self.token).encode()).hexdigest()
        # self.prehash = hashlib.sha1((self.sn + self.mac).encode()).hexdigest()
        # prehash = 0

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

        self.retry = False

        self.liveStreamsData = []

        next_url = ""

        self.unique_ref = 0

        self.sortby = "number"

        for j in str(self.host):
            value = ord(j)
            self.unique_ref += value

        self.epg_downloaded_channels = set()

        # buttons / keys
        self["key_red"] = StaticText(_("Back"))
        self["key_green"] = StaticText(_("OK"))
        self["key_yellow"] = StaticText(self.sortText)
        self["key_blue"] = StaticText(_("Search"))
        self["key_epg"] = StaticText("")
        self["key_menu"] = StaticText("")

        self["category_actions"] = ActionMap(["EStalkerActions"], {
            "cancel": self.back,
            "red": self.back,
            "ok": self.parentalCheck,
            "green": self.parentalCheck,
            "yellow": self.sort,
            "blue": self.search,
            "left": self.pageUp,
            "right": self.pageDown,
            "up": self.goUp,
            "down": self.goDown,
            "channelUp": self.pageUp,
            "channelDown": self.pageDown,
            "0": self.reset,
            "menu": self.showHiddenList,
            "tv": self.showfavourites,
            "stop": self.showfavourites
        }, -1)

        self["channel_actions"] = ActionMap(["EStalkerActions"], {
            "cancel": self.back,
            "red": self.back,
            "ok": self.parentalCheck,
            "green": self.parentalCheck,
            "yellow": self.sort,
            "blue": self.search,
            "epg": self.nownext,
            "info": self.nownext,
            "text": self.nownext,
            "epg_long": self.shortEPG,
            "info_long": self.shortEPG,
            "text_long": self.shortEPG,
            "left": self.pageUp,
            "right": self.pageDown,
            "up": self.goUp,
            "down": self.goDown,
            "channelUp": self.pageUp,
            "channelDown": self.pageDown,
            "tv": self.favourite,
            "stop": self.favourite,
            "0": self.reset,
            "menu": self.showHiddenList,
        }, -1)

        self["channel_actions"].setEnabled(False)

        glob.nextlist = []
        glob.nextlist.append({"next_url": next_url, "index": 0, "level": self.level, "sort": self.sortText, "filter": ""})

        self.onFirstExecBegin.append(self.createSetup)
        self.onLayoutFinish.append(self.__layoutFinished)

    def __layoutFinished(self):
        if debugs:
            print("*** __layoutFinished ***")

        self.setTitle(self.setup_title)

    def getAllChannels(self):
        if debugs:
            print("*** getAllChannels ***")

        # Step 1: Get all channels
        getallchannelsurl = self.portal + "?type=itv&action=get_all_channels"
        response = make_request(getallchannelsurl, method="POST", headers=self.headers, params=None, response_type="json")

        filtered_keys = [
            "id",
            "name",
            "number",
            "status",
            "tv_genre_id",
            "xmltv_id",
            "enable_tv_archive",
            "logo",
            "tv_archive_duration",
            "archive",
            "cmd"
        ]

        all_filtered_data = []

        if response and "js" in response and "data" in response["js"]:
            for item in response["js"]["data"]:
                filtered_item = {}

                for key in filtered_keys:
                    if key in item:
                        filtered_item[key] = item[key]

                all_filtered_data.append(filtered_item)

        all_filtered_data = sorted(all_filtered_data, key=lambda x: x.get("name", "").lower())

        # Step 2: Get all adult category IDs
        if glob.active_playlist["player_info"].get("showadult", False):
            self.adult_category_ids = []

            categories = glob.active_playlist["data"]["live_categories"]["js"]

            for cat in categories:
                title = cat.get("title", "")
                cat_id = cat.get("id")
                censored = cat.get("censored", 0)

                if "adult" in title or "xxx" in title or censored == 1:
                    self.adult_category_ids.append(cat_id)

            # Step 3: Append paginated adult channels
            if self.adult_category_ids:
                for adult_category_id in self.adult_category_ids:

                    page = 1
                    total_items = None
                    downloaded_items = 0

                    while True:
                        adulturl = "{0}?type=itv&action=get_ordered_list&genre={1}&force_ch_link_check=&fav=0&sortby={2}&hd=1&from_ch_id=0&JsHttpRequest=1-xml&p={3}".format(
                            self.portal, adult_category_id, self.sortby, page
                        )

                        response = make_request(adulturl, method="POST", headers=self.headers, params=None, response_type="json")

                        if not response or "js" not in response or "data" not in response["js"]:
                            break

                        if total_items is None:
                            total_items = int(response["js"].get("total_items", 0))

                        page_items = response["js"]["data"]
                        if not page_items:
                            break

                        for item in page_items:
                            filtered_item = {}

                            for key in filtered_keys:
                                if key in item:
                                    filtered_item[key] = item[key]

                            all_filtered_data.append(filtered_item)
                            downloaded_items += 1

                        if downloaded_items >= total_items:
                            break

                        page += 1

        with open("/tmp/allchannels.json", "w") as f:
            json.dump(all_filtered_data, f, indent=4)

    def createSetup(self, data=None):
        if debugs:
            print("*** createSetup ***")

        self["x_title"].setText("")
        self["x_description"].setText("")

        if self.level == 1:
            self.sortby = "number"
            self.getCategories()
            if not os.path.isfile("/tmp/allchannels.json"):
                self.getAllChannels()

        if self.level == 2:
            self.epg_downloaded_channels.clear()
            self.pages_downloaded = set()
            self.short_epg_results = {}
            self.current_page = None
            self.all_data = []

            self.getLevel2()

    def buildLists(self):
        if debugs:
            print("*** buildLists ***")

        if self.level == 1:
            self.buildList1()
        else:
            self.buildList2()

        self.resetButtons()
        self.selectionChanged()

    # working
    def getCategories(self):
        if debugs:
            print("*** getCategories **")

        self.list1 = []
        self.prelist = []

        currentPlaylist = glob.active_playlist
        currentCategoryList = currentPlaylist.get("data", {}).get("live_categories", {}).get("js", [])
        currentHidden = set(currentPlaylist.get("player_info", {}).get("livehidden", []))

        hidden = "0" in currentHidden

        for index, item in enumerate(currentCategoryList, start=len(self.prelist)):
            category_name = item.get("title", "No category")
            category_id = item.get("id", "999999")
            number = item.get("number", 0)
            hidden = category_id in currentHidden
            self.list1.append([index, str(category_name), str(category_id), hidden, number])

        glob.originalChannelList1 = self.list1[:]
        self.buildLists()

    def getLevel2(self):
        if debugs:
            print("*** getLevel2 ***")

        if self.chosen_category == "favourites":
            response = glob.active_playlist["player_info"].get("livefavourites", [])
        else:
            if os.path.isfile("/tmp/allchannels.json"):
                with open("/tmp/allchannels.json", "r") as f:
                    try:
                        response = json.load(f)
                    except:
                        os.remove("/tmp/allchannels.json")

        if not response:
            self.list2 = []
            return

        self.list2 = []
        category_id = glob.nextlist[-1]["next_url"]

        if self.chosen_category != "favourites":
            filteredresponse = []

            if str(category_id) != "0" and str(category_id) != "*":
                for item in response:
                    if "tv_genre_id" in item and str(item["tv_genre_id"]) == str(category_id):
                        filteredresponse.append(item)

                response = filteredresponse

        for index, channel in enumerate(response):
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
            hidden = str(stream_id) in glob.active_playlist["player_info"]["channelshidden"]
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

            """
            0 = index
            1 = name
            2 = stream_id
            3 = stream_icon
            4 = epg_channel_id
            5 = number
            6 = category_id
            7 = cmd
            8 = service_ref
            9 = nowtime
            10 = nowTitle
            11 = nowDescription
            12 = nexttime
            13 = nextTitle
            14 = nextDesc
            15 = next_url
            16 = favourite
            17 = watched
            18 = hidden
            19 = nowunixtime
            20 = nextunixtime
            """

            self.list2.append([index, str(name), str(stream_id), str(stream_icon), str(epg_channel_id), str(number), str(category_id), str(cmd), str(service_ref),
                              "", "", "", "", "", "", str(next_url), favourite, False, hidden, None, None])
        glob.originalChannelList2 = self.list2
        self.buildLists()

    def getVisibleChannels(self):
        if debugs:
            print("*** getVisibleChannels ***")

        current_index = self["main_list"].getIndex()
        position = current_index + 1
        page = (position - 1) // self.itemsperpage + 1
        start = (page - 1) * self.itemsperpage
        end = start + self.itemsperpage
        channel_list = self.main_list if hasattr(self, 'main_list') else []

        return [item[4] for item in channel_list[start:end] if len(item) > 4]

    def handle_epg_done(self, epg_data):
        if debugs:
            print("*** handle_epg_done ***")

        if not epg_data or "js" not in epg_data:
            return

        for event in epg_data["js"]:
            ch = event.get("ch_id")
            if ch not in self.short_epg_results:
                self.short_epg_results[ch] = []
            self.short_epg_results[ch].append(event)

        self.updateEPGListWithShortEPG()

    def updateEPGListWithShortEPG(self):
        if debugs:
            print("*** updateEPGListWithShortEPG ***")

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

        self["epg_list"].updateList(self.epglist)

        instance = self["epg_list"].master.master.instance
        instance.setSelectionEnable(0)

        self.refreshEPGInfo()

    def _updateUrlPage(self, url, page):
        import re

        if "p=" in url:
            return re.sub(r"p=\d+", "p=" + str(page), url)
        else:
            sep = "&" if "?" in url else "?"
            return url + sep + "p=" + str(page)

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

    def buildList1(self):
        if debugs:
            print("*** buildlist1 ***")

        self["key_epg"].setText("")
        self.hideEPG()
        self.xmltvdownloaded = False

        if self["key_blue"].getText() != _("Reset Search"):
            self.pre_list = [buildCategoryList(x[0], x[1], x[2], x[3], x[4]) for x in self.prelist if not x[3]]
        else:
            self.pre_list = []

        self.main_list = [buildCategoryList(x[0], x[1], x[2], x[3], x[4]) for x in self.list1 if not x[3]]

        self["main_list"].setList(self.pre_list + self.main_list)

        if self["main_list"].getCurrent() and glob.nextlist[-1]["index"] != 0:
            self["main_list"].setIndex(glob.nextlist[-1]["index"])

    def buildList2(self):
        if debugs:
            print("*** buildlist2 ***")

        self.main_list = []
        self.epglist = []

        """
        0 = index
        1 = name
        2 = stream_id
        3 = stream_icon
        4 = epg_channel_id
        5 = number
        6 = category_id
        7 = cmd
        8 = service_ref
        9 = nowtime
        10 = nowTitle
        11 = nowDescription
        12 = nexttime
        13 = nextTitle
        14 = nextDesc
        15 = next_url
        16 = favourite
        17 = watched
        18 = hidden
        19 = nowunixtime
        20 = nextunixtime
        """

        if self.list2:
            if self.chosen_category == "favourites":
                self.main_list = [buildLiveStreamList(x[0], x[1], x[2], x[3], x[5], x[7], x[15], x[16], x[17], x[18], x[6]) for x in self.list2 if x[16] is True]
                self.epglist = [buildEPGListEntry(x[0], x[1], x[9], x[10], x[11], x[12], x[13], x[14], x[18], x[19], x[20]) for x in self.list2 if x[16] is True]
            else:
                self.main_list = [buildLiveStreamList(x[0], x[1], x[2], x[3], x[5], x[7], x[15], x[16], x[17], x[18], x[6]) for x in self.list2 if x[18] is False]
                self.epglist = [buildEPGListEntry(x[0], x[1], x[9], x[10], x[11], x[12], x[13], x[14], x[18], x[19], x[20]) for x in self.list2 if x[18] is False]

        self["main_list"].setList(self.main_list)
        self["epg_list"].setList(self.epglist)
        if self.main_list:
            self.showEPG()

        if self["main_list"].getCurrent() and glob.nextlist[-1]["index"] != 0:
            self["main_list"].setIndex(glob.nextlist[-1]["index"])

    def resetButtons(self):
        if debugs:
            print("*** resetButtons ***")

        if glob.nextlist[-1]["filter"]:
            self["key_yellow"].setText("")
            self["key_blue"].setText(_("Reset Search"))
            self["key_menu"].setText("")
        else:
            self["key_blue"].setText(_("Search"))

            if not glob.nextlist[-1]["sort"]:
                if self.level == 1:
                    self.sortText = _("Sort: A-Z")
                else:
                    self.sortText = _("Sort: A-Z")
                glob.nextlist[-1]["sort"] = self.sortText

            self["key_yellow"].setText(_(glob.nextlist[-1]["sort"]))

            self["key_menu"].setText("+/-")

            if self.chosen_category == "favourites":
                self["key_menu"].setText("")

    def selectionChanged(self):
        if debugs:
            print("*** selectionChanged ***")

        current_item = self["main_list"].getCurrent()
        if current_item:
            channel_title = current_item[0]
            current_index = self["main_list"].getIndex()
            glob.currentchannellistindex = current_index
            glob.nextlist[-1]["index"] = current_index

            position = current_index + 1
            position_all = len(self.pre_list) + len(self.main_list) if self.level == 1 else len(self.main_list)
            page = (position - 1) // self.itemsperpage + 1
            page_all = (position_all + self.itemsperpage - 1) // self.itemsperpage

            self["page"].setText(_("Page: ") + "{}/{}".format(page, page_all))
            self["listposition"].setText("{}/{}".format(position, position_all))
            self["main_title"].setText("{}: {}".format(self.main_title, channel_title))

            self.loadBlankImage()

            if self.level == 2:
                if not self.showingshortEPG:
                    self["epg_list"].setIndex(current_index)

                if cfg.channelpicons.value:
                    self.timerimage = eTimer()

                    try:
                        self.timerimage.callback.append(self.downloadImage)
                    except:
                        self.timerimage_conn = self.timerimage.timeout.connect(self.downloadImage)
                    self.timerimage.start(250, True)

                self.current_page = page

                self.timerrefresh = eTimer()

                try:
                    self.timerrefresh.callback.append(self.updateDisplay)
                except:
                    self.timerrefresh_conn = self.timerrefresh.timeout.connect(self.updateDisplay)
                self.timerrefresh.start(260, True)

        else:
            position = 0
            position_all = 0
            page = 0
            page_all = 0

            self["page"].setText(_("Page: ") + "{}/{}".format(page, page_all))
            self["listposition"].setText("{}/{}".format(position, position_all))
            self["key_yellow"].setText("")
            self["key_blue"].setText("")
            self.hideEPG()

    def updateDisplay(self):
        self.refreshEPGInfo()

        visible_channels = self.getVisibleChannels()
        channels_to_fetch = [ch_id for ch_id in visible_channels if ch_id not in self.epg_downloaded_channels]

        if not channels_to_fetch:
            self.updateEPGListWithShortEPG()
            return

        for ch_id in channels_to_fetch:
            self.epg_downloaded_channels.add(ch_id)

        from .getshortepg import EStalker_EPG_Short
        EStalker_EPG_Short(channels_to_fetch, done_callback=self.handle_epg_done)

    def downloadImage(self):
        """
        if debugs:
            print("*** downloadimage ***")
            """

        if self["main_list"].getCurrent():
            try:
                for filename in ["original.png", "temp.png"]:
                    file_path = os.path.join(dir_tmp, filename)
                    if os.path.exists(file_path):
                        os.remove(file_path)
            except Exception:
                pass

            desc_image = ""
            try:
                desc_image = self["main_list"].getCurrent()[5]
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
            except Exception:
                self.loadDefaultImage()

    def loadBlankImage(self, data=None):
        """
        if debugs:
            print("*** loadblankimage ***")
            """

        if self["picon"].instance:
            self["picon"].instance.setPixmapFromFile(os.path.join(common_path, "picon_blank.png"))

    def loadDefaultImage(self, data=None):
        """
        if debugs:
            print("*** loaddefaultimage ***")
            """

        if self["picon"].instance:
            self["picon"].instance.setPixmapFromFile(os.path.join(common_path, "picon.png"))

    def resizeImage(self, data=None):
        """
        if debugs:
            print("*** resizeImage ***")
            """

        current_item = self["main_list"].getCurrent()
        if current_item:
            original = os.path.join(dir_tmp, "temp.png")

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

                    src_w, src_h = im.size
                    target_w, target_h = size

                    scale = min(float(target_w) / src_w, float(target_h) / src_h)
                    new_size = (int(src_w * scale), int(src_h * scale))

                    try:
                        im = im.resize(new_size, Image.Resampling.LANCZOS)
                    except:
                        im = im.resize(new_size, Image.ANTIALIAS)

                    bg = Image.new("RGBA", size, (255, 255, 255, 0))
                    left = (target_w - new_size[0]) // 2
                    top = (target_h - new_size[1]) // 2
                    bg.paste(im, (left, top), mask=im)

                    bg.save(original, "PNG")

                    if self["picon"].instance:
                        self["picon"].instance.setPixmapFromFile(original)

                except Exception:
                    self.loadDefaultImage()
            else:
                self.loadDefaultImage()

    def goUp(self):
        instance = self.selectedlist.master.master.instance
        instance.moveSelection(instance.moveUp)
        self.selectionChanged()

    def goDown(self):
        instance = self.selectedlist.master.master.instance
        instance.moveSelection(instance.moveDown)
        self.selectionChanged()

    def pageUp(self):
        instance = self.selectedlist.master.master.instance
        instance.moveSelection(instance.pageUp)
        self.selectionChanged()

    def pageDown(self):
        instance = self.selectedlist.master.master.instance
        instance.moveSelection(instance.pageDown)
        self.selectionChanged()

    # button 0
    def reset(self):
        if debugs:
            print("*** reset ***")
        self.selectedlist.setIndex(0)
        self.selectionChanged()

    def sort(self):
        if debugs:
            print("*** sort ***")

        current_sort = self["key_yellow"].getText()
        if not current_sort:
            return

        if self.level == 1:
            activelist = self.list1

            sortlist = [_("Sort: Original"), _("Sort: A-Z"), _("Sort: Z-A")]

            for index, item in enumerate(sortlist):
                if str(item) == str(self.sortText):
                    self.sortindex = index
                    break

            if self["main_list"].getCurrent():
                self["main_list"].setIndex(0)

            glob.nextlist[-1]["index"] = 0

            if current_sort == _("Sort: A-Z"):
                activelist.sort(key=lambda x: x[1].lower(), reverse=False)
            elif current_sort == _("Sort: Z-A"):
                activelist.sort(key=lambda x: x[1].lower(), reverse=True)
            elif current_sort == _("Sort: Original"):
                activelist.sort(key=lambda x: x[4], reverse=False)

            next_sort_type = next(islice(cycle(sortlist), self.sortindex + 1, None))
            self.sortText = str(next_sort_type)

            self["key_yellow"].setText(self.sortText)
            glob.nextlist[-1]["sort"] = self["key_yellow"].getText()

            self.list1 = activelist

            self.buildLists()

        if self.level == 2:
            activelist = self.list2
            sortlist = [_("Sort: Original"), _("Sort: A-Z"), _("Sort: Z-A")]

            for index, item in enumerate(sortlist):
                if str(item) == str(self.sortText):
                    self.sortindex = index
                    break

            if self["main_list"].getCurrent():
                self["main_list"].setIndex(0)

            glob.nextlist[-1]["index"] = 0

            if current_sort == _("Sort: A-Z"):
                activelist.sort(key=lambda x: x[1].lower(), reverse=False)
            elif current_sort == _("Sort: Z-A"):
                activelist.sort(key=lambda x: x[1].lower(), reverse=True)
            elif current_sort == _("Sort: Original"):
                activelist.sort(key=lambda x: x[5], reverse=False)

            next_sort_type = next(islice(cycle(sortlist), self.sortindex + 1, None))
            self.sortText = str(next_sort_type)

            self["key_yellow"].setText(self.sortText)
            glob.nextlist[-1]["sort"] = self["key_yellow"].getText()

            self.list2 = activelist

            self.buildLists()

    def search(self, result=None):
        if debugs:
            print("*** search ***")

        if not self["key_blue"].getText():
            return

        current_filter = self["key_blue"].getText()

        if current_filter == _("Reset Search"):
            self.resetSearch()
        else:
            self.session.openWithCallback(self.filterChannels, VirtualKeyBoard, title=_("Filter this category..."), text=self.searchString)

    def filterChannels(self, result=None):
        if debugs:
            print("*** filterChannels ***")

        activelist = []
        if result:
            self.filterresult = result
            glob.nextlist[-1]["filter"] = self.filterresult

            activelist = self.list1 if self.level == 1 else self.list2

            self.searchString = result
            activelist = [channel for channel in activelist if str(result).lower() in str(channel[1]).lower()]

            if not activelist:
                self.searchString = ""
                self.session.openWithCallback(self.search, MessageBox, _("No results found."), type=MessageBox.TYPE_ERROR, timeout=5)
            else:
                if self.level == 1:
                    self.list1 = activelist
                else:
                    self.list2 = activelist

                self["key_blue"].setText(_("Reset Search"))
                self["key_yellow"].setText("")

                self.buildLists()

    def resetSearch(self):
        if debugs:
            print("*** resetSearch ***")

        self["key_blue"].setText(_("Search"))
        self["key_yellow"].setText(self.sortText)

        if self.level == 1:
            activelist = glob.originalChannelList1[:]
            self.list1 = activelist
        else:
            activelist = glob.originalChannelList2[:]
            self.list2 = activelist

        self.filterresult = ""
        glob.nextlist[-1]["filter"] = self.filterresult

        self.buildLists()

    def pinEntered(self, result=None):
        if debugs:
            print("*** pinEntered ***")

        if not result:
            self.pin = False
            self.session.open(MessageBox, _("Incorrect pin code."), type=MessageBox.TYPE_ERROR, timeout=5)

        if self.pin is True:
            if pythonVer == 2:
                glob.pintime = int(time.mktime(datetime.now().timetuple()))
            else:
                glob.pintime = int(datetime.timestamp(datetime.now()))

            self.next()
        else:
            return

    def parentalCheck(self):
        if debugs:
            print("*** parentalCheck ***")

        self.pin = True
        nowtime = int(time.mktime(datetime.now().timetuple())) if pythonVer == 2 else int(datetime.timestamp(datetime.now()))

        if self.level == 1 and self["main_list"].getCurrent():
            adult_keywords = {
                "adult", "+18", "18+", "18 rated", "xxx", "sex", "porn",
                "voksen", "volwassen", "aikuinen", "Erwachsene", "dorosly",
                "взрослый", "vuxen", "£дорослий"
            }

            current_title = str(self["main_list"].getCurrent()[0])

            if current_title == "ALL" or current_title == _("ALL") or current_title == "All" or current_title == _("All"):
                glob.adultChannel = True

            elif "sport" in current_title.lower():
                glob.adultChannel = False

            elif any(keyword in current_title.lower() for keyword in adult_keywords):
                glob.adultChannel = True

            else:
                glob.adultChannel = False

            if cfg.adult.value and nowtime - int(glob.pintime) > 900 and glob.adultChannel:
                from Screens.InputBox import PinInput
                self.session.openWithCallback(
                    self.pinEntered,
                    PinInput,
                    pinList=[cfg.adultpin.value],
                    triesEntry=cfg.retries.adultpin,
                    title=_("Please enter the parental control pin code"),
                    windowTitle=_("Enter pin code")
                )
            else:
                self.next()
        else:
            self.next()

    def next(self):
        if debugs:
            print("*** next ***")

        if self["main_list"].getCurrent():
            current_index = self["main_list"].getIndex()
            glob.nextlist[-1]["index"] = current_index
            glob.currentchannellist = self.main_list[:]
            glob.currentchannellistindex = current_index

            if self.level == 1:
                if self.list1:
                    category_id = self["main_list"].getCurrent()[3]

                    next_url = category_id

                    self.chosen_category = ""

                    if self.showfav:
                        self.chosen_category = "favourites"

                    self.level += 1
                    self["main_list"].setIndex(0)
                    self["category_actions"].setEnabled(False)
                    self["channel_actions"].setEnabled(True)
                    self["key_yellow"].setText(_("Sort: A-Z"))
                    self.sortText = _("Sort: A-Z")

                    glob.nextlist.append({"next_url": next_url, "index": 0, "level": self.level, "sort": self["key_yellow"].getText(), "filter": ""})

                    self.createSetup()
                else:
                    self.createSetup()
            else:
                if self.list2:
                    from . import liveplayer
                    glob.currentepglist = self.epglist[:]

                    if self.selectedlist == self["epg_short_list"]:
                        self.shortEPG()

                    streamtype = glob.active_playlist["player_info"]["livetype"]
                    command = self["main_list"].getCurrent()[7]
                    next_url = command

                    stream_id = self["main_list"].getCurrent()[4]

                    if debugs:
                        print("*** original command **", command)

                    if isinstance(command, str):
                        if "localhost" in command or "http" not in command or "///" in command:
                            url = "{0}?type=itv&action=create_link&cmd={1}&series=0&forced_storage=0&disable_ad=0&download=0&force_ch_link_check=0&JsHttpRequest=1-xml".format(self.portal, command)
                            self.retry = False
                            response = self.createLink(url)
                            next_url = ""

                            if isinstance(response, dict) and "js" in response and "cmd" in response["js"]:
                                next_url = response["js"]["cmd"]

                        else:
                            next_url = command

                        parts = next_url.split(None, 1)
                        if len(parts) == 2:
                            next_url = parts[1].lstrip()

                    if isinstance(next_url, str):
                        parsed = urlparse(next_url)
                        if parsed.scheme in ["http", "https"]:
                            next_url = parsed.geturl()

                    if str(os.path.splitext(next_url)[-1]) == ".m3u8":
                        if streamtype == "1":
                            streamtype = "4097"

                    self.reference = eServiceReference(int(streamtype), 0, str(next_url))
                    self.reference.setName(glob.currentchannellist[glob.currentchannellistindex][0])

                    if self.session.nav.getCurrentlyPlayingServiceReference():

                        def strip_play_token(url):
                            return re.sub(r'([&?])(play_token|token)=[^&]*&?', lambda m: m.group(1) if not m.group(0).endswith('&') else '', url).rstrip('&?')

                        if strip_play_token(self.session.nav.getCurrentlyPlayingServiceReference().toString()) != strip_play_token(self.reference.toString()) and cfg.livepreview.value is True:
                            try:
                                self.session.nav.stopService()
                            except Exception as e:
                                print(e)

                            try:
                                self.session.nav.playService(self.reference)
                            except Exception as e:
                                print(e)

                            if self.session.nav.getCurrentlyPlayingServiceReference():
                                glob.newPlayingServiceRef = self.session.nav.getCurrentlyPlayingServiceReference()
                                glob.newPlayingServiceRefString = glob.newPlayingServiceRef.toString()

                            for channel in self.list2:
                                if channel[2] == stream_id:
                                    channel[17] = True  # set watching icon
                                else:
                                    channel[17] = False

                            if self.chosen_category == "favourites":
                                self.main_list = [buildLiveStreamList(x[0], x[1], x[2], x[3], x[5], x[7], x[15], x[16], x[17], x[18], x[6]) for x in self.list2 if x[16] is True]
                            else:
                                self.main_list = [buildLiveStreamList(x[0], x[1], x[2], x[3], x[5], x[7], x[15], x[16], x[17], x[18], x[6]) for x in self.list2 if x[18] is False]
                            self["main_list"].setList(self.main_list)

                        else:
                            for channel in self.list2:
                                if channel[2] == stream_id:
                                    channel[17] = True  # set watching icon
                                else:
                                    channel[17] = False

                            if self.chosen_category == "favourites":
                                self.main_list = [buildLiveStreamList(x[0], x[1], x[2], x[3], x[5], x[7], x[15], x[16], x[17], x[18], x[6]) for x in self.list2 if x[16] is True]
                            else:
                                self.main_list = [buildLiveStreamList(x[0], x[1], x[2], x[3], x[5], x[7], x[15], x[16], x[17], x[18], x[6]) for x in self.list2 if x[18] is False]
                            self["main_list"].setList(self.main_list)

                            try:
                                self.session.nav.stopService()
                            except:
                                pass

                            self.session.openWithCallback(self.setIndex, liveplayer.EStalker_StreamPlayer, str(next_url), str(streamtype), stream_id)
                    else:
                        try:
                            self.session.nav.stopService()
                        except:
                            pass

                        self.session.openWithCallback(self.setIndex, liveplayer.EStalker_StreamPlayer, str(next_url), str(streamtype), stream_id)

                    self["category_actions"].setEnabled(False)

                else:
                    self.createSetup()

    def setIndex(self, data=None):
        """
        if debugs:
            print("*** setIndex ***")
            """

        if self["main_list"].getCurrent():
            self["main_list"].setIndex(glob.currentchannellistindex)
            self["epg_list"].setIndex(glob.currentchannellistindex)
            self.xmltvdownloaded = False

    def back(self, data=None):
        if debugs:
            print("*** back ***")

        self.showfav = False
        self.chosen_category = ""

        if self.selectedlist == self["epg_short_list"]:
            self.shortEPG()
            return

        del glob.nextlist[-1]

        if not glob.nextlist:
            self.stopStream()
            self.close()
        else:
            self["x_title"].setText("")
            self["x_description"].setText("")
            if cfg.stopstream.value:
                self.stopStream()
            self.level -= 1

            self["category_actions"].setEnabled(True)
            self["channel_actions"].setEnabled(False)
            self.sortText = _("Sort: A-Z")

            self.buildLists()

    def showHiddenList(self):
        if debugs:
            print("*** showHiddenList ***")

        if self["key_menu"].getText() and self["main_list"].getCurrent():
            from . import hidden
            current_list = self.prelist + self.list1 if self.level == 1 else self.list2

            if self.level == 1 or (self.level == 2 and self.chosen_category != "favourites"):
                self.xmltvdownloaded = False
                self.session.openWithCallback(self.createSetup, hidden.EStalker_HiddenCategories, "live", current_list, self.level)

    def showfavourites(self):
        if debugs:
            print("*** show favourites ***")

        # self.chosen_category = "favourites"
        self.showfav = True
        self.parentalCheck()

    def favourite(self):
        if debugs:
            print("*** favourite ***")

        if not self["main_list"].getCurrent() or not self.list2:
            return

        current_index = self["main_list"].getIndex()
        favExists = False
        favStream_id = ""

        for fav in glob.active_playlist["player_info"]["livefavourites"]:
            if self["main_list"].getCurrent()[4] == fav["id"]:
                favExists = True
                favStream_id = fav["id"]
                break

        try:
            self.list2[current_index][16] = not self.list2[current_index][16]
        except:
            pass

        if favExists:
            glob.active_playlist["player_info"]["livefavourites"] = [x for x in glob.active_playlist["player_info"]["livefavourites"] if str(x["id"]) != str(favStream_id)]
        else:
            newfavourite = {
                "name": self.list2[current_index][1],
                "id": self.list2[current_index][2],
                "logo": self.list2[current_index][3],
                "xmltv_id": self.list2[current_index][4],
                "number": self.list2[current_index][5],
                "tv_genre_id": self.list2[current_index][6],
                "cmd": self.list2[current_index][7]
            }

            glob.active_playlist["player_info"]["livefavourites"].insert(0, newfavourite)
            # self.hideEPG()

        with open(playlists_json, "r") as f:
            try:
                self.playlists_all = json.load(f)
            except Exception as e:
                print("Error loading playlists JSON:", e)
                os.remove(playlists_json)
                self.playlists_all = []

        if self.playlists_all:
            for playlists in self.playlists_all:
                if (playlists["playlist_info"]["host"] == glob.active_playlist["playlist_info"]["host"]
                        and playlists["playlist_info"]["mac"] == glob.active_playlist["playlist_info"]["mac"]):
                    playlists.update(glob.active_playlist)
                    break

        with open(playlists_json, "w") as f:
            json.dump(self.playlists_all, f, indent=4)

        if self.chosen_category == "favourites":
            del self.list2[current_index]

        self.buildLists()

    def hideEPG(self):
        if debugs:
            print("*** hideEPG ***")

        self["epg_list"].setList([])
        self["picon"].hide()
        self["epg_bg"].hide()
        self["main_title"].setText("")
        self["x_title"].setText("")
        self["x_description"].setText("")
        self["progress"].hide()

    def showEPG(self):
        if debugs:
            print("*** showEPG ***")

        if self["main_list"].getCurrent():
            self["picon"].show()
            self["epg_bg"].show()
            self["progress"].show()

    def refreshEPGInfo(self):
        if debugs:
            print("*** refreshEPGInfo ***")

        current_item = self["epg_list"].getCurrent()
        if not current_item:
            return

        instance = self["epg_list"].master.master.instance
        instance.setSelectionEnable(1)

        titlenow = current_item[3]
        descriptionnow = current_item[4]
        startnowtime = current_item[2]
        startnexttime = current_item[5]
        startnowunixtime = current_item[9]
        startnextunixtime = current_item[10]

        if titlenow:
            nowTitle = "{} - {}  {}".format(startnowtime, startnexttime, titlenow)
            self["key_epg"].setText(_("Next Info"))
        else:
            nowTitle = ""
            self["key_epg"].setText("")
            instance.setSelectionEnable(0)

        self["x_title"].setText(nowTitle)
        self["x_description"].setText(descriptionnow)

        if startnowunixtime and startnextunixtime:
            self["progress"].show()

            now = int(time.time())
            total_time = startnextunixtime - startnowunixtime
            elapsed = now - startnowunixtime

            percent = int(elapsed / total_time * 100) if total_time > 0 else 0

            # Clamp percent between 0 and 100
            percent = max(0, min(percent, 100))

            self["progress"].setValue(percent)
        else:
            self["progress"].hide()

    def nownext(self):
        if debugs:
            print("*** nownext ***")

        current_item = self["main_list"].getCurrent()
        if not current_item:
            return

        if self.level == 2 and self["key_epg"].getText() and self["epg_list"].getCurrent():
            startnowtime = self["epg_list"].getCurrent()[2]
            titlenow = self["epg_list"].getCurrent()[3]
            descriptionnow = self["epg_list"].getCurrent()[4]

            startnexttime = self["epg_list"].getCurrent()[5]
            titlenext = self["epg_list"].getCurrent()[6]
            descriptionnext = self["epg_list"].getCurrent()[7]

            if self["key_epg"].getText() == _("Next Info"):
                nextTitle = "Next {}: {}".format(startnexttime, titlenext)
                self["x_title"].setText(nextTitle)
                self["x_description"].setText(descriptionnext)
                self["key_epg"].setText(_("Now Info"))
            else:
                nowTitle = "{} - {}  {}".format(startnowtime, startnexttime, titlenow)
                self["x_title"].setText(nowTitle)
                self["x_description"].setText(descriptionnow)
                self["key_epg"].setText(_("Next Info"))

    def parse_datetime(self, datetime_str):
        if debugs:
            print("*** parse_datetime ***")

        time_formats = ["%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H-%M-%S", "%Y-%m-%d-%H:%M:%S", "%Y- %m-%d %H:%M:%S"]

        for time_format in time_formats:
            try:
                return datetime.strptime(datetime_str, time_format)
            except ValueError:
                pass
        return ""

    def shortEPG(self):
        if debugs:
            print("*** shortEPG ***")

        if self["main_list"].getCurrent():
            self.showingshortEPG = not self.showingshortEPG

            if self.showingshortEPG:
                self["key_menu"].setText("")

                current_index = self["main_list"].getIndex()
                glob.nextlist[-1]["index"] = current_index

                self["epg_list"].setList([])

                if self.level == 2:
                    try:
                        stream_id = self["main_list"].getCurrent()[4]
                        url = self.portal + "?type=itv&action=get_short_epg&ch_id={}&limit=10&size=10".format(stream_id)

                        response = make_request(url, method="POST", headers=self.headers, params=None, response_type="json")

                        listings = []

                        if response:
                            listings = response.get("js", [])

                        if listings:
                            first_start = listings[0].get("start_timestamp", 0)
                            first_start_dt = datetime.utcfromtimestamp(first_start)

                            now = datetime.now()

                            self.epgshortlist = []
                            duplicatecheck = []

                            for index, listing in enumerate(listings):
                                try:
                                    title = listing.get("name", "")
                                    description = listing.get("descr", "")
                                    t_time = listing.get("t_time")
                                    t_time_to = listing.get("t_time_to")

                                    if not t_time or not t_time_to:
                                        continue

                                    # Build datetime objects using the date from first_start_dt and t_time fields
                                    date_base = first_start_dt.date()
                                    start_datetime = datetime.strptime("{} {}".format(date_base, t_time), "%Y-%m-%d %H:%M")
                                    end_datetime = datetime.strptime("{} {}".format(date_base, t_time_to), "%Y-%m-%d %H:%M")

                                    # If t_time_to is before t_time, assume it passes midnight
                                    if end_datetime < start_datetime:
                                        end_datetime += timedelta(days=1)

                                    epg_date_all = start_datetime.strftime("%a %d/%m")
                                    epg_time_all = "{} - {}".format(start_datetime.strftime("%H:%M"), end_datetime.strftime("%H:%M"))

                                    if [epg_date_all, epg_time_all] not in duplicatecheck and end_datetime >= now:
                                        duplicatecheck.append([epg_date_all, epg_time_all])
                                        self.epgshortlist.append(buildShortEPGListEntry(
                                            str(epg_date_all), str(epg_time_all), str(title), str(description),
                                            index, start_datetime, end_datetime,
                                            int(start_datetime.strftime("%s")), int(end_datetime.strftime("%s"))
                                        ))

                                except Exception as e:
                                    print("Error processing short EPG entry using t_time:", e)

                            self["epg_short_list"].setList(self.epgshortlist)
                            instance = self["epg_short_list"].master.master.instance
                            instance.setSelectionEnable(1)

                            self["progress"].hide()
                            self["key_yellow"].setText("")
                            self["key_blue"].setText("")
                            self["key_epg"].setText("")

                            self.selectedlist = self["epg_short_list"]

                        else:
                            self.showingshortEPG = not self.showingshortEPG

                    except Exception as e:
                        print("Error fetching short EPG:", e)
            else:
                self["epg_short_list"].setList([])
                self.selectedlist = self["main_list"]
                self.buildLists()

    def displayShortEPG(self):
        if debugs:
            print("*** displayshortEPG ***")

        if self["epg_short_list"].getCurrent():
            title = str(self["epg_short_list"].getCurrent()[0])
            description = str(self["epg_short_list"].getCurrent()[3])
            timeall = str(self["epg_short_list"].getCurrent()[2])
            self["x_title"].setText(timeall + " " + title)
            self["x_description"].setText(description)

    def stopStream(self):
        if debugs:
            print("*** stop stream ***")

        current_playing_ref = glob.currentPlayingServiceRefString
        new_playing_ref = glob.newPlayingServiceRefString

        if current_playing_ref and new_playing_ref and current_playing_ref != new_playing_ref:
            currently_playing_service = self.session.nav.getCurrentlyPlayingServiceReference()
            if currently_playing_service:
                self.session.nav.stopService()
            self.session.nav.playService(eServiceReference(current_playing_ref))
            glob.newPlayingServiceRefString = current_playing_ref


def buildEPGListEntry(index, title, epgNowTime, epgNowTitle, epgNowDesc, epgNextTime, epgNextTitle, epgNextDesc, hidden, epgNowUnixTime, epgNextUnixTime):
    return (title, index, epgNowTime, epgNowTitle, epgNowDesc, epgNextTime, epgNextTitle, epgNextDesc, hidden, epgNowUnixTime, epgNextUnixTime)


def buildShortEPGListEntry(date_all, time_all, title, description, index, start_datetime, end_datetime, start_timestamp, stop_timestamp):
    return (title, date_all, time_all, description, index, start_datetime, end_datetime, start_timestamp, stop_timestamp)


def buildCategoryList(index, title, category_id, hidden, number):
    png = LoadPixmap(os.path.join(common_path, "more.png"))
    return (title, png, index, category_id, hidden, number)


def buildLiveStreamList(index, name, stream_id, stream_icon, number, command, next_url, favourite, watching, hidden, category_id):
    png = LoadPixmap(os.path.join(common_path, "play.png"))
    if favourite:
        png = LoadPixmap(os.path.join(common_path, "favourite.png"))
    if watching:
        png = LoadPixmap(os.path.join(common_path, "watching.png"))
    return (name, png, index, next_url, stream_id, stream_icon, number, command, hidden, category_id)
