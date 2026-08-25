#!/usr/bin/python
# -*- coding: utf-8 -*-

from __future__ import division

# Standard library imports
import codecs
import json
import os
import re
import tempfile
import time
from datetime import datetime, timedelta
from itertools import cycle, islice

import hashlib


try:
    from http.client import HTTPConnection
    HTTPConnection.debuglevel = 0
except ImportError:
    from httplib import HTTPConnection
    HTTPConnection.debuglevel = 0

try:
    from urllib.parse import urlparse, parse_qs, urlunparse
except:
    from urlparse import urlparse, parse_qs, urlunparse

try:
    from urllib import quote
except ImportError:
    from urllib.parse import quote

# Third-party imports
from PIL import Image
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
from .plugin import cfg, common_path, dir_tmp, pythonVer, screenwidth, skin_directory, debugs, isDreambox
from .eStaticText import StaticText
from .utils import get_local_timezone, make_request, reauthorize_portal
from .getshortepg import EStalker_EPG_Short

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


class EStalker_Live_Categories(Screen):
    ALLOW_SUSPEND = True

    def __init__(self, session):
        if debugs:
            print("*** live init ***")

        Screen.__init__(self, session)
        self.session = session
        glob.categoryname = "live"

        skin_path = os.path.join(skin_directory, cfg.skin.value)
        skin = os.path.join(skin_path, "live_categories.xml")
        if isDreambox:
            skin = os.path.join(skin_path, "DreamOS/live_categories.xml")

        with codecs.open(skin, "r", encoding="utf-8") as f:
            self.skin = f.read()

        self.playlists_json = cfg.playlists_json.value
        self.setup_title = _("Live Categories")
        self.main_title = _("Live TV")
        self.group_title = ""

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

        # pagination variables
        self["page"] = StaticText("")
        self["listposition"] = StaticText("")
        self.itemsperpage = 14

        self.searchString = ""
        self.filterresult = ""

        self.showingshortEPG = False

        self.chosen_category = ""

        self.pin = False

        self.showfav = False
        self.firstlist = True
        self.do_sort = False

        self.sortindex = 0
        self.sortText = _("Sort: A-Z")

        self.level = 1

        self.selectedlist = self["main_list"]

        self._picon_req_id = 0

        self.liveStreamsData = []

        next_url = ""

        self._px_play = LoadPixmap(os.path.join(common_path, "play.png"))
        self._px_fav = LoadPixmap(os.path.join(common_path, "favourite.png"))
        self._px_watching = LoadPixmap(os.path.join(common_path, "watching.png"))
        self._px_more = LoadPixmap(os.path.join(common_path, "more.png"))

        self._re_bouquet_marker = re.compile(r"[^\w\s()\[\]]", re.U)

        if screenwidth.width() == 2560:
            self.picon_size = (294, 176)
        elif screenwidth.width() > 1280:
            self.picon_size = (220, 130)
        else:
            self.picon_size = (147, 88)

        self.adult_keywords = set([
            "adult", "+18", "18+", "18 rated", "xxx", "sex", "porn",
            "voksen", "volwassen", "aikuinen", "Erwachsene", "dorosly",
            "взрослый", "vuxen", "£дорослий"
        ])

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
        self.force_ch_link_check = glob.active_playlist["playlist_info"].get("force_ch_link_check", "0")

        self.referer = self.host + self.path_prefix + "index.html"

        self.sn = hashlib.md5(self.mac.encode()).hexdigest().upper()[:13]
        self.adid = hashlib.md5((self.sn + self.mac).encode()).hexdigest()

        encoded_mac = quote(self.mac, safe='')
        encoded_timezone = quote(self.timezone, safe='')

        # self.device_id = hashlib.sha256(self.mac.encode()).hexdigest().upper()
        # device_id = hashlib.sha256(self.sn.encode()).hexdigest().upper()
        # self.device_id2 = self.device_id
        # device_id2 = hashlib.sha256(self.mac.encode()).hexdigest().upper()
        # self.hw_version_2 = hashlib.sha1(self.mac.encode()).hexdigest()
        # self.hw_version_2 = hashlib.sha1((self.mac + self.token).encode()).hexdigest()
        # self.prehash = hashlib.sha1((self.sn + self.mac).encode()).hexdigest()
        # prehash = 0

        saved_headers = glob.active_playlist["playlist_info"].get("headers", {})
        self.headers = saved_headers.copy() if isinstance(saved_headers, dict) else {}

        # Compatibility fallback for playlists saved before authenticated
        # xpcom-derived headers were persisted.
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

        self.sortby = "number"

        self.epg_downloaded_channels = set()
        self.epg_cache_dirty = False

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
        }, -1)

        self["channel_actions"].setEnabled(False)

        glob.nextlist = []
        glob.nextlist.append({"next_url": next_url, "index": 0, "level": self.level, "sort": self.sortText, "filter": ""})

        self.timerImage = eTimer()
        try:
            self.timerImage.callback.append(self.downloadImage)
        except:
            self.timerImage_conn = self.timerImage.timeout.connect(self.downloadImage)

        self.timerGetEPG = eTimer()
        try:
            self.timerGetEPG.callback.append(self.getEPG)
        except:
            self.timerGetEPG_conn = self.timerGetEPG.timeout.connect(self.getEPG)

        self.onFirstExecBegin.append(self.createSetup)
        self.onLayoutFinish.append(self.__layoutFinished)

    def __layoutFinished(self):
        self.setTitle(self.setup_title)

    def _stopTimer(self, name):
        t = getattr(self, name, None)
        if t:
            try:
                t.stop()
            except:
                pass
        if name == "timerImage":
            try:
                self._picon_req_id += 1
            except:
                self._picon_req_id = 1

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

    def createSetup(self, data=None):
        if debugs:
            print("*** createSetup ***")

        self["x_title"].setText("")
        self["x_description"].setText("")

        if self.level == 1:
            self.getCategories()

        if self.level == 2:
            self.all_data = []
            self.pages_downloaded = set()
            self.current_page = 1
            self.epg_downloaded_channels.clear()
            self.short_epg_results = {}

            if self.chosen_category != "favourites":
                response = self.downloadApiData(glob.nextlist[-1]["next_url"])
            else:
                response = ""
            self.firstlist = True
            self.getLevel2(response)

    def buildLists(self):
        if debugs:
            print("*** buildLists ***")

        if self.level == 1:
            self.buildList1()
        else:
            self.buildList2()

        if self.do_sort:
            self.do_sort = False
            self.applyPreviousSort()

        else:
            self.resetButtons()
            self.selectionChanged()

    def getCategories(self):
        if debugs:
            print("*** getCategories **")

        self.list1 = []
        self.prelist = []

        currentPlaylist = glob.active_playlist
        currentCategoryList = currentPlaylist.get("data", {}).get("live_categories", {}).get("js", [])
        currentHidden = set(currentPlaylist.get("player_info", {}).get("livehidden", []))

        hiddenfavourites = "-1" in currentHidden
        hiddenrecent = "-2" in currentHidden
        hidden = "0" in currentHidden

        i = 0

        self.prelist.extend([
            [i, _("FAVOURITES"), "-1", hiddenfavourites, "-1"],
            [i + 1, _("RECENTLY WATCHED"), "-2", hiddenrecent, "-2"],
        ])

        for index, item in enumerate(currentCategoryList, start=len(self.prelist)):
            if not isinstance(item, dict):
                continue

            category_name = item.get("title", "No category")
            category_id = item.get("id", "999999")
            number = item.get("number", 0)
            hidden = category_id in currentHidden
            self.list1.append([index, str(category_name), str(category_id), hidden, number])

        glob.originalChannelList1 = self.list1[:]
        self.buildLists()

    def getLevel2(self, response):
        if debugs:
            print("*** getLevel2 ***")

        if self.chosen_category == "favourites":
            response = glob.active_playlist["player_info"].get("livefavourites", [])
        elif self.chosen_category == "recents":
            response = glob.active_playlist["player_info"].get("liverecents", [])

        self.list2 = []
        glob.live_link_metadata = {}

        if response:
            for index, channel in enumerate(response):
                if not isinstance(channel, dict) or not channel:
                    self.list2.append([index, "", "", "", "", "", "", "", "", "", "", "", "", "", "", "", False, False, False, None, None, {}])
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
                link_metadata = {
                    "available": any(key in channel for key in ("use_http_tmp_link", "use_load_balancing", "disable_ad")),
                    "use_http_tmp_link": channel.get("use_http_tmp_link", "0"),
                    "use_load_balancing": channel.get("use_load_balancing", "0"),
                    "disable_ad": channel.get("disable_ad", "0"),
                }
                glob.live_link_metadata[str(stream_id)] = link_metadata
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
                21 = link metadata used by create_link
                """

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
                    None,
                    link_metadata
                ])

        if self.firstlist:
            glob.originalChannelList2 = self.list2[:]
            self.firstlist = False

        self.buildLists()

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

            if not data:
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
        if debugs:
            print("*** _updateUrlPage ***")
        if "p=" in url:
            return re.sub(r"p=\d+", "p=" + str(page), url)
        else:
            sep = "&" if "?" in url else "?"
            return url + sep + "p=" + str(page)

    def createLink(self, url, params):
        if debugs:
            print("*** createLink ***", url)

        response = make_request(url, method="GET", headers=self.headers, params=params, response_type="json")

        if debugs:
            print("*** createlink response ***", response)

        if not response:
            self.reauthorize()
            response = make_request(url, method="GET", headers=self.headers, params=params, response_type="json")
            if debugs:
                print("*** createlink response 2 ***", response)

        return response

    def reauthorize(self):
        if debugs:
            print("*** reauthorize ***")

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

        # Persist the refreshed bearer token and token cookie so subsequent
        # screens do not reopen with stale authentication data.
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

    def buildList1(self):
        if debugs:
            print("*** buildList1 ***")

        self["key_epg"].setText("")
        self.hideEPG()
        self.xmltvdownloaded = False

        if self["key_blue"].getText() != _("Reset Search"):
            self.pre_list = [buildCategoryList(x[0], x[1], x[2], x[3], x[4], self._px_more) for x in self.prelist if not x[3]]
        else:
            self.pre_list = []

        if self.list1:
            self.main_list = [buildCategoryList(x[0], x[1], x[2], x[3], x[4], self._px_more) for x in self.list1 if not x[3]]

            self["main_list"].setList(self.pre_list + self.main_list)

            if self["main_list"].getCurrent() and glob.nextlist[-1]["index"] != 0:
                self["main_list"].setIndex(glob.nextlist[-1]["index"])

    def buildList2(self):
        if debugs:
            print("*** buildList2 ***")

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
                self.main_list = [
                    buildLiveStreamList(
                        x[0], x[1], x[2], x[3], x[5], x[7], x[15], x[16], x[17], x[18],
                        x[6], self._px_play, self._px_fav, self._px_watching
                    )
                    for x in self.list2 if x[16] is True]

                self.epglist = [buildEPGListEntry(x[0], x[1], x[9], x[10], x[11], x[12], x[13], x[14], x[18], x[19], x[20]) for x in self.list2 if x[16] is True]
            else:
                self.main_list = [
                    buildLiveStreamList(
                        x[0], x[1], x[2], x[3], x[5], x[7], x[15], x[16], x[17], x[18],
                        x[6], self._px_play, self._px_fav, self._px_watching
                    )
                    for x in self.list2 if x[18] is False]

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
            if not glob.nextlist[-1]["sort"]:
                if self.level == 1:
                    self.sortText = _("Sort: A-Z")
                else:
                    self.sortText = _("Sort: A-Z")

                glob.nextlist[-1]["sort"] = self.sortText

            self["key_yellow"].setText(_(glob.nextlist[-1]["sort"]))

            if self.level == 1:
                if self.chosen_category == "recents":
                    self["key_blue"].setText(_("Delete"))
                else:
                    self["key_blue"].setText(_("Search"))
                    self["key_menu"].setText("+/-")
            else:
                self["key_menu"].setText("")
                self["key_blue"].setText(_("Search All"))

            if self.chosen_category == "favourites" or self.chosen_category == "recent":
                self["key_menu"].setText("")

    def stopStream(self):
        if debugs:
            print("*** stopStream ***")

        current_playing_ref = glob.currentPlayingServiceRefString
        new_playing_ref = glob.newPlayingServiceRefString

        if current_playing_ref:
            if current_playing_ref and new_playing_ref and current_playing_ref != new_playing_ref:
                currently_playing_service = self.session.nav.getCurrentlyPlayingServiceReference()
                if currently_playing_service:
                    self.session.nav.stopService()

                self.session.nav.playService(eServiceReference(current_playing_ref))
                glob.newPlayingServiceRefString = current_playing_ref
        else:
            self.session.nav.stopService()

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

            if self.level == 2 and self["key_blue"].getText() != _("Reset Search") and self.chosen_category != "favourites":
                position_all = int(self.total_items)
                page_all = (position_all + self.itemsperpage - 1) // self.itemsperpage

            self["page"].setText(_("Page: ") + "{}/{}".format(page, page_all))
            self["listposition"].setText("{}/{}".format(position, position_all))

            parts = []

            if self.main_title:
                parts.append(self.main_title)

            if self.group_title:
                parts.append(self.group_title)

            if channel_title:
                parts.append(channel_title)

            self["main_title"].setText(": ".join(parts))

            self.loadBlankImage()

            if self.level == 2:
                if not self.showingshortEPG:
                    self["epg_list"].setIndex(current_index)

                if cfg.channelpicons.value:
                    self._stopTimer("timerImage")
                    self.timerImage.start(250, True)

                if self["key_blue"].getText() != _("Reset Search"):
                    if not hasattr(self, 'current_page') or page != self.current_page:
                        self.current_page = page
                        response = self.downloadApiData(glob.nextlist[-1]["next_url"])
                        self.getLevel2(response)

                self._stopTimer("timerGetEPG")
                self.timerGetEPG.start(260, True)

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

    def getEPG(self):
        if debugs:
            print("*** getEPG ***")

        # get visible channels
        current_index = self["main_list"].getIndex()
        position = current_index + 1
        page = (position - 1) // self.itemsperpage + 1
        start = (page - 1) * self.itemsperpage
        end = start + self.itemsperpage

        channel_list = self.main_list if hasattr(self, "main_list") else []
        visible_channels = [
            item[4]
            for item in channel_list[start:end]
            if len(item) > 4
        ]

        channels_to_fetch = [ch_id for ch_id in visible_channels if ch_id not in self.epg_downloaded_channels]

        if not channels_to_fetch:
            self.updateEPGList()
            return

        for ch_id in channels_to_fetch:
            self.epg_downloaded_channels.add(ch_id)

        EStalker_EPG_Short(channels_to_fetch, done_callback=self.handle_epg_done)

    def handle_epg_done(self, epg_data):
        if debugs:
            print("*** handle_epg_done ***")
        if not epg_data or "js" not in epg_data:
            return

        for entry in epg_data["js"]:
            ch_id = str(entry.get("ch_id"))
            if not ch_id:
                continue
            if ch_id not in self.short_epg_results:
                self.short_epg_results[ch_id] = []
            self.short_epg_results[ch_id].append(entry)

        if debugs:
            print("*** self.short_epg_results ***", self.short_epg_results)
        self.updateEPGList()

    def updateEPGList(self):

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
            buildEPGListEntry(
                x[0], x[1], x[9], x[10], x[11],
                x[12], x[13], x[14], x[18], x[19], x[20]
            )
            for x in self.list2 if x[18] is False
        ]

        self["epg_list"].updateList(self.epglist)

        instance = self["epg_list"].master.master.instance
        instance.setSelectionEnable(0)

        self.displayEPGDescription()

    def displayEPGDescription(self):
        if debugs:
            print("*** displayEPGDescription ***", self["main_list"].getCurrent()[0])

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

        percent = 0

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

    def downloadImage(self):
        if debugs:
            print("*** downloadImage ***")

        if not self["main_list"].getCurrent():
            self.loadDefaultImage()
            return

        # Clear immediately so previous image doesn't remain if new fails
        self.loadBlankImage()

        # bump request id so stale callbacks can be ignored (zap protection)
        try:
            self._picon_req_id += 1
        except:
            self._picon_req_id = 1

        req_id = self._picon_req_id

        desc_image = ""
        try:
            desc_image = self["main_list"].getCurrent()[5]
        except:
            desc_image = ""

        # Category rows use this position for their numeric sort value. A
        # delayed image timer can fire just after returning from the player.
        desc_image = str(desc_image or "")

        if not desc_image or str(desc_image).lower() == "n/a":
            self.loadDefaultImage()
            return

        if not desc_image.startswith(("http://", "https://")):
            self.loadDefaultImage()
            return

        fd = None
        temp = None

        try:
            fd, temp = tempfile.mkstemp(prefix="xst_live_picon_", suffix=".png", dir=dir_tmp)
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
                # ignore stale callback if user moved again
                if getattr(self, "_picon_req_id", 0) != req_id:
                    _cleanup_temp()
                    return

                self.resizeImage(temp, req_id=req_id)

            def _err(_failure=None):
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

        except Exception:
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

    def loadBlankImage(self, data=None):
        if debugs:
            print("*** loadBlankImage ***")

        if self["picon"].instance:
            self["picon"].instance.setPixmapFromFile(os.path.join(common_path, "picon_blank.png"))

    def loadDefaultImage(self, data=None):
        if debugs:
            print("*** loadDefaultImage ***")

        if self["picon"].instance:
            self["picon"].instance.setPixmapFromFile(os.path.join(common_path, "picon.png"))

    def resizeImage(self, original, req_id=None):
        if debugs:
            print("*** resizeImage ***", original, req_id)

        if req_id is not None and getattr(self, "_picon_req_id", 0) != req_id:
            try:
                if original and os.path.exists(original):
                    os.remove(original)
            except:
                pass
            return

        size = self.picon_size
        if os.path.exists(original):
            im = None
            try:
                im = Image.open(original)
                if im.mode != "RGBA":
                    im = im.convert("RGBA")

                if im.size[0] == 0 or im.size[1] == 0:
                    raise ValueError("Image has zero dimension")
                ratio = min(size[0] / float(im.size[0]), size[1] / float(im.size[1]))
                new_size = (int(im.size[0] * ratio), int(im.size[1] * ratio))
                try:
                    im = im.resize(new_size, Image.Resampling.LANCZOS)
                except:
                    im = im.resize(new_size, Image.ANTIALIAS)

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

    def goUp(self):
        if debugs:
            print("*** goUp ***")

        instance = self.selectedlist.master.master.instance
        instance.moveSelection(instance.moveUp)
        self.selectionChanged()

    def goDown(self):
        if debugs:
            print("*** goDown ***")

        instance = self.selectedlist.master.master.instance
        instance.moveSelection(instance.moveDown)
        self.selectionChanged()

    def pageUp(self):
        if debugs:
            print("*** pageUp ***")

        instance = self.selectedlist.master.master.instance
        instance.moveSelection(instance.pageUp)
        self.selectionChanged()

    def pageDown(self):
        if debugs:
            print("*** pageDown ***")

        instance = self.selectedlist.master.master.instance
        instance.moveSelection(instance.pageDown)
        self.selectionChanged()

    # button 0
    def reset(self):
        if debugs:
            print("*** reset ***")

        self.selectedlist.setIndex(0)
        self.selectionChanged()

    def applyPreviousSort(self):
        if debugs:
            print("*** applyPreviousSort ***")

        if self.level == 1 and self.list1:
            sortlist = [_("Sort: A-Z"), _("Sort: Z-A"), _("Sort: Original")]

            # Determine the previous sort in the cycle
            prev_sort = sortlist[0]  # default
            for index, item in enumerate(sortlist):
                if str(item) == str(self.sortText):
                    prev_sort = sortlist[index - 1]  # previous in cycle (wraps around automatically)
                    break

            # Apply sort to list1
            activelist = self.list1[:]

            if prev_sort == _("Sort: A-Z"):
                activelist.sort(key=lambda x: x[1].lower(), reverse=False)
            elif prev_sort == _("Sort: Z-A"):
                activelist.sort(key=lambda x: x[1].lower(), reverse=True)
            elif prev_sort == _("Sort: Original"):
                activelist.sort(key=lambda x: x[4], reverse=False)

            # Always move "All" category to first position if present
            for i, item in enumerate(activelist):
                if item[1].lower() == _("all").lower():
                    activelist.insert(0, activelist.pop(i))
                    break

            self.list1 = activelist

        elif self.level == 2:
            sortlist = [_("Sort: Original"), _("Sort: A-Z"), _("Sort: Added")]

            prev_sort = sortlist[0]
            for index, item in enumerate(sortlist):
                if str(item) == str(self.sortText):
                    prev_sort = sortlist[index - 1]
                    break

            if prev_sort == _("Sort: A-Z"):
                self.sortby = "name"
            elif prev_sort == _("Sort: Original"):
                self.sortby = "number"
            elif prev_sort == _("Sort: Added"):
                self.sortby = "added"

            # reset pagination and data
            self.pages_downloaded = set()
            self.current_page = 1
            self.all_data = []

            if self["main_list"].getCurrent():
                self["main_list"].setIndex(0)

            glob.nextlist[-1]["index"] = 0
            glob.nextlist[-1]["sort"] = self["key_yellow"].getText()

            self.selectionChanged()
            self.current_page = 1

            if self.list2:
                glob.nextlist[-1]["next_url"] = "{0}?type=itv&action=get_ordered_list&genre={1}&sortby={2}&p=1&force_ch_link_check={3}&JsHttpRequest=1-xml".format(
                    self.portal, self.current_category, self.sortby, self.force_ch_link_check
                )
                response = self.downloadApiData(glob.nextlist[-1]["next_url"])
                self.getLevel2(response)

        self.buildLists()

        # Keep previous selection if possible
        if self["main_list"].getCurrent() and glob.nextlist[-1]["index"] != 0:
            self["main_list"].setIndex(glob.nextlist[-1]["index"])

    def sort(self):
        if debugs:
            print("*** sort ***")

        current_sort = self["key_yellow"].getText()
        if not current_sort:
            return

        if self.level == 1:
            activelist = self.list1

            sortlist = [_("Sort: A-Z"), _("Sort: Z-A"), _("Sort: Original")]

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

            for i, item in enumerate(activelist):
                if item[1].lower() == "all":
                    activelist.insert(0, activelist.pop(i))
                    break

            self.buildLists()

        elif self.level == 2:
            # activelist = self.list2
            sortlist = [_("Sort: Original"), _("Sort: A-Z"), _("Sort: Added")]

            for index, item in enumerate(sortlist):
                if str(item) == str(self.sortText):
                    self.sortindex = index
                    break

            if current_sort == _("Sort: A-Z"):
                self.sortby = "name"
            elif current_sort == _("Sort: Original"):
                self.sortby = "number"
            elif current_sort == _("Sort: Added"):
                self.sortby = "added"

            self.pages_downloaded = set()
            self.current_page = 1
            self.all_data = []

            if self["main_list"].getCurrent():
                self["main_list"].setIndex(0)

            glob.nextlist[-1]["index"] = 0

            next_sort_type = next(islice(cycle(sortlist), self.sortindex + 1, None))
            self.sortText = str(next_sort_type)

            self["key_yellow"].setText(self.sortText)
            glob.nextlist[-1]["sort"] = self["key_yellow"].getText()

            self.selectionChanged()

            self.current_page = 1

            if self.list2:
                glob.nextlist[-1]["next_url"] = "{0}?type=itv&action=get_ordered_list&genre={1}&sortby={2}&p=1&force_ch_link_check={3}&JsHttpRequest=1-xml".format(self.portal, self.current_category, self.sortby, self.force_ch_link_check)
                response = self.downloadApiData(glob.nextlist[-1]["next_url"])
                self.getLevel2(response)

    def search(self, result=None):
        if debugs:
            print("*** search ***")

        if not self["key_blue"].getText():
            return

        current_filter = self["key_blue"].getText()

        if current_filter == _("Reset Search"):
            self.resetSearch()

        elif current_filter == _("Delete"):
            self.deleteRecent()

        else:
            self.session.openWithCallback(self.filterChannels, VirtualKeyBoard, title=_("Filter this category..."), text=self.searchString)

    def deleteRecent(self):
        if debugs:
            print("*** deleteRecent ***")

        current_item = self["main_list"].getCurrent()
        if current_item:
            current_index = self["main_list"].getIndex()

            if not os.path.exists(self.playlists_json):
                self.playlists_all = []
            else:
                with open(self.playlists_json, "r") as f:
                    try:
                        self.playlists_all = json.load(f)
                    except Exception:
                        os.remove(self.playlists_json)
                        self.playlists_all = []

            # safer: delete by stream id
            stream_id = current_item[4]

            glob.active_playlist["player_info"]['liverecents'] = [
                x for x in glob.active_playlist["player_info"]['liverecents']
                if str(x.get("id")) != str(stream_id)
            ]

            self.hideEPG()

            if self.playlists_all:
                for idx, playlists in enumerate(self.playlists_all):
                    if playlists["playlist_info"]["domain"] == glob.active_playlist["playlist_info"]["domain"] and playlists["playlist_info"]["mac"] == glob.active_playlist["playlist_info"]["mac"]:
                        self.playlists_all[idx] = glob.active_playlist
                        break

            with open(self.playlists_json, "w") as f:
                json.dump(self.playlists_all, f, indent=4)

            del self.list2[current_index]
            self.buildLists()

    def filterChannels(self, result=None):
        if debugs:
            print("*** filterChannels ***")

        activelist = []

        if result:
            self.filterresult = result
            glob.nextlist[-1]["filter"] = self.filterresult

            self.searchString = result

            if self.level == 1:
                activelist = self.list1

                activelist = [channel for channel in activelist if str(result).lower() in str(channel[1]).lower()]

                if not activelist:
                    self.searchString = ""
                    self.session.openWithCallback(self.search, MessageBox, _("No results found."), type=MessageBox.TYPE_ERROR, timeout=5)

                else:
                    self.list1 = activelist

                    self["key_blue"].setText(_("Reset Search"))
                    self["key_yellow"].setText("")
                    self.buildLists()

            if self.level == 2 and self.list2:
                self.all_data = []

                if self["main_list"].getCurrent():
                    self["main_list"].setIndex(0)

                glob.nextlist[-1]["index"] = 0

                paged_url = "{0}?type=itv&action=get_all_channels&sortby=name&JsHttpRequest=1-xml".format(self.portal)

                response = self.downloadApiData(paged_url)

                if response and isinstance(response, list):
                    filtered_response = [ch for ch in response if result.lower() in ch.get('name', '').lower()]
                    response = filtered_response

                self.getLevel2(response)

                if not self.list2:
                    self.searchString = ""
                    self.session.openWithCallback(self.search, MessageBox, _("No results found."), type=MessageBox.TYPE_ERROR, timeout=5)

                else:
                    self["key_blue"].setText(_("Reset Search"))
                    self["key_yellow"].setText("")

    def resetSearch(self):
        if debugs:
            print("*** resetSearch ***")

        self["key_yellow"].setText(self.sortText)
        self.do_sort = True

        if self.level == 1:
            self["key_blue"].setText(_("Search"))
            activelist = glob.originalChannelList1[:]
            self.list1 = activelist
        else:
            self["key_blue"].setText(_("Search All"))
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

            current_title = str(self["main_list"].getCurrent()[0])

            if current_title == "ALL" or current_title == _("ALL") or current_title == "All" or current_title == _("All"):
                glob.adultChannel = True

            elif "sport" in current_title.lower():
                glob.adultChannel = False

            elif any(keyword in current_title.lower() for keyword in self.adult_keywords):
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

        self._stopTimer("timerImage")
        self._stopTimer("timerGetEPG")
        # self._stopTimer("timerEPGUpdate")

        if self["main_list"].getCurrent():
            current_index = self["main_list"].getIndex()
            glob.nextlist[-1]["index"] = current_index

            if glob.currentchannellist is not self.main_list:
                glob.currentchannellist = self.main_list[:]

            glob.currentchannellistindex = current_index
            self.group_title = self["main_list"].getCurrent()[0]

            if self.level == 1:
                if self.list1:
                    category_id = self["main_list"].getCurrent()[3]
                    self.sortby = "number"
                    self.current_category = category_id

                    next_url = "{0}?type=itv&action=get_ordered_list&genre={1}&sortby={2}&p=1&force_ch_link_check={3}&JsHttpRequest=1-xml".format(self.portal, category_id, self.sortby, self.force_ch_link_check)
                    self.chosen_category = ""

                    if self.showfav:
                        self.chosen_category = "favourites"

                    if category_id == "-1":
                        self.chosen_category = "favourites"

                    elif category_id == "-2":
                        self.chosen_category = "recents"

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
                        link_metadata = {}
                        for channel in self.list2:
                            if str(channel[2]) == str(stream_id):
                                if len(channel) > 21 and isinstance(channel[21], dict):
                                    link_metadata = channel[21]
                                break

                        use_http_tmp_link = str(link_metadata.get("use_http_tmp_link", "0")).lower() in ("1", "true", "yes")
                        use_load_balancing = str(link_metadata.get("use_load_balancing", "0")).lower() in ("1", "true", "yes")
                        disable_ad = str(link_metadata.get("disable_ad", "0")).lower() in ("1", "true", "yes")
                        force_ch_link_check = str(self.force_ch_link_check).lower() in ("1", "true", "yes")

                        # Old saved favourites do not contain the channel link
                        # flags. Keep their previous command-based behaviour as
                        # a compatibility fallback only.
                        if link_metadata.get("available"):
                            create_link_required = use_http_tmp_link or use_load_balancing or force_ch_link_check
                        else:
                            create_link_required = (
                                force_ch_link_check
                                or "localhost" in command
                                or "///" in command
                                or "/ch/" in command
                                or "http" not in command
                            )

                        if create_link_required:
                            params = {
                                "type": "itv",
                                "action": "create_link",
                                "cmd": command,
                                "series": "0",
                                "forced_storage": "0",
                                "disable_ad": "1" if disable_ad else "0",
                                "download": "0",
                                "force_ch_link_check": "1" if force_ch_link_check else "0",
                                "JsHttpRequest": "1-xml",
                            }
                            response = self.createLink(self.portal, params)
                            next_url = ""
                            link_error = ""

                            if isinstance(response, dict):
                                link_data = response.get("js", {})
                                if isinstance(link_data, dict):
                                    next_url = str(link_data.get("cmd", ""))
                                    link_error = str(link_data.get("error", ""))

                            if not next_url:
                                error_messages = {
                                    "limit": _("Maximum number of connections reached."),
                                    "nothing_to_play": _("Nothing to play."),
                                    "link_fault": _("Server error or invalid link."),
                                }
                                message = error_messages.get(link_error, _("Server error or invalid link."))
                                self.session.open(MessageBox, message, MessageBox.TYPE_ERROR, timeout=3)
                                return
                        else:
                            next_url = command

                    if isinstance(next_url, str):
                        next_url = re.sub(r"%mac%", self.mac, next_url, flags=re.IGNORECASE)
                        parts = next_url.split(None, 1)
                        if len(parts) == 2:
                            next_url = parts[1].lstrip()

                        parsed = urlparse(next_url)
                        if parsed.scheme in ["http", "https"]:
                            next_url = parsed.geturl()

                        if str(os.path.splitext(next_url)[-1]) == ".m3u8":
                            if streamtype == "1":
                                streamtype = "4097"
                    else:
                        next_url = ""

                    self.reference = eServiceReference(int(streamtype), 0, str(next_url))
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

                    def update_channel_icons_and_list():
                        for channel in self.list2:
                            channel[17] = (channel[2] == stream_id)

                        if self.chosen_category == "favourites":
                            self.main_list = [
                                buildLiveStreamList(
                                    x[0], x[1], x[2], x[3], x[5], x[7], x[15], x[16], x[17], x[18],
                                    x[6], self._px_play, self._px_fav, self._px_watching
                                )
                                for x in self.list2 if x[16] is True]
                        else:
                            self.main_list = [
                                buildLiveStreamList(
                                    x[0], x[1], x[2], x[3], x[5], x[7], x[15], x[16], x[17], x[18],
                                    x[6], self._px_play, self._px_fav, self._px_watching
                                )
                                for x in self.list2 if x[18] is False]

                        self["main_list"].setList(self.main_list)
                        self.setIndex()
                    # ============================================================

                    playing = self.session.nav.getCurrentlyPlayingServiceReference()

                    if playing:
                        current_ref = strip_query_from_ref(playing)
                        new_ref = strip_query_from_ref(self.reference)

                        if current_ref != new_ref and cfg.livepreview.value is True:
                            try:
                                self.session.nav.playService(self.reference)
                            except Exception as e:
                                print(e)

                            nowref = self.session.nav.getCurrentlyPlayingServiceReference()
                            if nowref:
                                glob.newPlayingServiceRef = nowref
                                glob.newPlayingServiceRefString = nowref.toString()

                            update_channel_icons_and_list()
                        else:
                            update_channel_icons_and_list()
                            self.session.openWithCallback(self.reload, liveplayer.EStalker_StreamPlayer, str(next_url), str(streamtype))
                    else:
                        if cfg.livepreview.value is True:
                            try:
                                self.session.nav.playService(self.reference)
                            except Exception as e:
                                print(e)

                            nowref = self.session.nav.getCurrentlyPlayingServiceReference()
                            if nowref:
                                glob.newPlayingServiceRef = nowref
                                glob.newPlayingServiceRefString = nowref.toString()

                            update_channel_icons_and_list()
                        else:
                            update_channel_icons_and_list()
                            self.session.openWithCallback(self.reload, liveplayer.EStalker_StreamPlayer, str(next_url), str(streamtype))

                    self["category_actions"].setEnabled(False)

                else:
                    self.createSetup()

    def reload(self):
        if debugs:
            print("*** reload ***")
        self.setIndex()
        self.selectionChanged()
        self.setWatchingIcon(glob.currentchannellistindex)

    def setWatchingIcon(self, idx):
        if debugs:
            print("*** setWatchingIcon ***")

        if not self["main_list"].getCurrent() or not self.list2:
            return

        # Get the stream_id of the channel the player was on
        try:
            watching_stream_id = glob.currentchannellist[idx][4]
        except (IndexError, TypeError):
            return

        # Clear all watching flags
        for channel in self.list2:
            channel[17] = False

        # Set watching for currently active channel index
        try:
            self.list2[idx][17] = True
        except:
            pass

        # Set watching flag by stream_id match, not raw index
        for channel in self.list2:
            if str(channel[2]) == str(watching_stream_id):
                channel[17] = True
                break

        # Rebuild main_list with updated watching flags
        if self.chosen_category == "favourites":
            self.main_list = [
                buildLiveStreamList(
                    x[0], x[1], x[2], x[3], x[5], x[7], x[15], x[16], x[17], x[18],
                    x[6], self._px_play, self._px_fav, self._px_watching
                )
                for x in self.list2 if x[16] is True
            ]
        else:
            self.main_list = [
                buildLiveStreamList(
                    x[0], x[1], x[2], x[3], x[5], x[7], x[15], x[16], x[17], x[18],
                    x[6], self._px_play, self._px_fav, self._px_watching
                )
                for x in self.list2 if x[18] is False
            ]

        self["main_list"].setList(self.main_list)

    def setIndex(self, data=None):
        if debugs:
            print("*** setIndex ***")

        if self["main_list"].getCurrent():
            self["main_list"].setIndex(glob.currentchannellistindex)
            self["epg_list"].setIndex(glob.currentchannellistindex)
            self.xmltvdownloaded = False

    def back(self, data=None):
        if debugs:
            print("*** back ***")

        self.showfav = False
        self.chosen_category = ""
        self.group_title = ""

        if self.selectedlist == self["epg_short_list"]:
            self.shortEPG()
            return

        if glob.nextlist:
            glob.nextlist.pop()

        if not glob.nextlist:
            self.stopStream()
            self._cleanupTimer("timerImage")
            self._cleanupTimer("timerGetEPG")
            # self._cleanupTimer("timerEPGUpdate")
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

            if self.level == 1 or (self.level == 2 and self.chosen_category != "favourites" and self.chosen_category != "recents"):
                self.xmltvdownloaded = False
                self.do_sort = True
                self.session.openWithCallback(self.createSetup, hidden.EStalker_HiddenCategories, "live", current_list, self.level)

    def showfavourites(self):
        if debugs:
            print("*** showfavourites ***")

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
                "cmd": self.list2[current_index][7],
                "use_http_tmp_link": self.list2[current_index][21].get("use_http_tmp_link", "0") if len(self.list2[current_index]) > 21 else "0",
                "use_load_balancing": self.list2[current_index][21].get("use_load_balancing", "0") if len(self.list2[current_index]) > 21 else "0",
                "disable_ad": self.list2[current_index][21].get("disable_ad", "0") if len(self.list2[current_index]) > 21 else "0",
            }

            glob.active_playlist["player_info"]["livefavourites"].insert(0, newfavourite)

        with open(self.playlists_json, "r") as f:
            try:
                self.playlists_all = json.load(f)
            except Exception as e:
                print("Error loading playlists JSON:", e)
                os.remove(self.playlists_json)
                self.playlists_all = []

        if self.playlists_all:
            for playlists in self.playlists_all:
                if (playlists["playlist_info"]["host"] == glob.active_playlist["playlist_info"]["host"]
                        and playlists["playlist_info"]["mac"] == glob.active_playlist["playlist_info"]["mac"]):
                    playlists.update(glob.active_playlist)
                    break

        with open(self.playlists_json, "w") as f:
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
                        url = self.portal + "?type=itv&action=get_short_epg&ch_id={}&size=10&JsHttpRequest=1-xml".format(stream_id)
                        response = make_request(url, method="GET", headers=self.headers, params=None, response_type="json")

                        if not response:
                            self.reauthorize()
                            response = make_request(url, method="GET", headers=self.headers, params=None, response_type="json")

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
            print("*** displayShortEPG ***")

        if self["epg_short_list"].getCurrent():
            title = str(self["epg_short_list"].getCurrent()[0])
            description = str(self["epg_short_list"].getCurrent()[3])
            timeall = str(self["epg_short_list"].getCurrent()[2])
            self["x_title"].setText(timeall + " " + title)
            self["x_description"].setText(description)


def buildEPGListEntry(index, title, epgNowTime, epgNowTitle, epgNowDesc, epgNextTime, epgNextTitle, epgNextDesc, hidden, epgNowUnixTime, epgNextUnixTime):
    return (title, index, epgNowTime, epgNowTitle, epgNowDesc, epgNextTime, epgNextTitle, epgNextDesc, hidden, epgNowUnixTime, epgNextUnixTime)


def buildShortEPGListEntry(date_all, time_all, title, description, index, start_datetime, end_datetime, start_timestamp, stop_timestamp):
    return (title, date_all, time_all, description, index, start_datetime, end_datetime, start_timestamp, stop_timestamp)


def buildCategoryList(index, title, category_id, hidden, number, px_more=None):
    return (title, px_more, index, category_id, hidden, number)


def buildLiveStreamList(index, name, stream_id, stream_icon, number, command, next_url, favourite, watching, hidden, category_id, px_play=None, px_fav=None, px_watching=None):
    png = px_play

    if favourite:
        png = px_fav

    if watching:
        png = px_watching

    return (name, png, index, next_url, stream_id, stream_icon, number, command, hidden, category_id)
