#!/usr/bin/python
# -*- coding: utf-8 -*-

from __future__ import division

# Standard library imports
import base64
import codecs
import json
import os
import re
import shutil
import subprocess
import time
from datetime import datetime, timedelta
from itertools import cycle, islice
import zlib
import hashlib

try:
    from http.client import HTTPConnection
    HTTPConnection.debuglevel = 0
except ImportError:
    from httplib import HTTPConnection
    HTTPConnection.debuglevel = 0

try:
    from urllib import quote
except ImportError:
    from urllib.parse import quote

try:
    from urlparse import urlparse
except ImportError:
    from urllib.parse import urlparse


# Third-party imports
import requests

from PIL import Image
# from requests.adapters import HTTPAdapter, Retry
from twisted.internet import reactor
from twisted.web.client import Agent, downloadPage, readBody
from twisted.web.http_headers import Headers


# Enigma2 components
from Components.ActionMap import ActionMap
from Components.Pixmap import Pixmap
from Components.Sources.List import List
from Screens.MessageBox import MessageBox
from Screens.Screen import Screen
from Screens.VirtualKeyBoard import VirtualKeyBoard
from Tools.LoadPixmap import LoadPixmap
from collections import OrderedDict
from enigma import ePicLoad, eServiceReference, eTimer

# Local imports
from . import _
from . import estalker_globals as glob
from .plugin import cfg, common_path, dir_tmp, pythonVer, screenwidth, skin_directory, debugs, isDreambox, isVTI
from .eStaticText import StaticText
from .utils import get_local_timezone, make_request,  perform_handshake, get_profile_data

try:
    from twisted.web.client import BrowserLikePolicyForHTTPS
    contextFactory = BrowserLikePolicyForHTTPS()
except ImportError:
    from twisted.web.client import WebClientContextFactory
    contextFactory = WebClientContextFactory()

try:
    from urllib import quote_plus
except ImportError:
    from urllib.parse import quote_plus


playlists_json = cfg.playlists_json.value


TMDB_installed = False

try:
    from Plugins.Extensions.TMDBCockpit.ScreenMain import ScreenMain
    TMDB_installed = True
except ImportError:
    pass

try:
    from Plugins.Extensions.tmdb.plugin import tmdb
    TMDB_installed = True
except ImportError:
    pass


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
    """Clean only 'name' fields inside response['js']."""
    if "js" in response and "data" in response["js"]:
        data_block = response["js"]["data"]

        if isinstance(data_block, list):
            for item in data_block:
                if isinstance(item, dict):
                    if "name" in item and isinstance(item["name"], str):
                        item["name"] = normalize_superscripts(item["name"])
    return response


class EStalker_Vod_Categories(Screen):
    ALLOW_SUSPEND = True

    def __init__(self, session):
        if debugs:
            print("*** vod init ***")

        Screen.__init__(self, session)
        self.session = session
        glob.categoryname = "vod"

        self.agent = Agent(reactor, contextFactory=contextFactory)
        self.cover_download_deferred = None
        self.logo_download_deferred = None
        self.backdrop_download_deferred = None

        self.skin_path = os.path.join(skin_directory, cfg.skin.value)
        skin = os.path.join(self.skin_path, "vod_categories.xml")
        if isDreambox:
            skin = os.path.join(self.skin_path, "DreamOS/vod_categories.xml")

        with codecs.open(skin, "r", encoding="utf-8") as f:
            self.skin = f.read()

        self.setup_title = _("Vod Categories")
        self.main_title = _("Movies")

        self["main_title"] = StaticText(self.main_title)
        self.main_list = []
        self["main_list"] = List(self.main_list, enableWrapAround=True)

        self["x_title"] = StaticText()
        self["x_description"] = StaticText()

        self["overview"] = StaticText()
        self["tagline"] = StaticText()
        self["facts"] = StaticText()

        # skin vod variables
        self["vod_cover"] = Pixmap()
        self["vod_cover"].hide()
        self["vod_backdrop"] = Pixmap()
        self["vod_backdrop"].hide()
        self["vod_logo"] = Pixmap()
        self["vod_logo"].hide()
        self["vod_director_label"] = StaticText()
        self["vod_country_label"] = StaticText()
        self["vod_cast_label"] = StaticText()
        self["vod_director"] = StaticText()
        self["vod_country"] = StaticText()
        self["vod_cast"] = StaticText()

        self["rating_text"] = StaticText()
        self["rating_percent"] = StaticText()

        # pagination variables
        self["page"] = StaticText("")
        self["listposition"] = StaticText("")
        self.itemsperpage = 14

        self.searchString = ""
        self.filterresult = ""
        self.chosen_category = ""

        self.pin = False
        self.sort_check = False
        self.showfav = False
        self.firstlist = True

        self.sortindex = 0
        self.sortText = _("Sort: A-Z")
        self.tmdbresults = ""

        self.level = 1

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

        self.retry = False

        self.apitoken = "ZUp6enk4cko4ZzBKTlBMTFNxN3djd25MOHEzeU5Zak1Bdkd6S3lPTmdqSjhxeUxMSTBNOFRhUGNBMjBCVmxBTzlBPT0K"

        next_url = ""
        self.sortby = "number"

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
        }, -2)

        self["channel_actions"] = ActionMap(["EStalkerActions"], {
            "cancel": self.back,
            "red": self.back,
            "OK": self.parentalCheck,
            "green": self.parentalCheck,
            "yellow": self.sort,
            "blue": self.search,
            "epg": self.imdb,
            "info": self.imdb,
            "text": self.imdb,
            "left": self.pageUp,
            "right": self.pageDown,
            "up": self.goUp,
            "down": self.goDown,
            "channelUp": self.pageUp,
            "channelDown": self.pageDown,
            "tv": self.favourite,
            "stop": self.favourite,
            "0": self.reset,
            # "menu": self.showHiddenList,
            "1": self.clearWatched,
            "OKLong": self.trailer
        }, -2)

        self["channel_actions"].setEnabled(False)

        glob.nextlist = []
        glob.nextlist.append({"next_url": next_url, "index": 0, "level": self.level, "sort": self.sortText, "filter": ""})

        self.coverLoad = ePicLoad()
        try:
            self.coverLoad.PictureData.get().append(self.DecodeCover)
        except:
            self.coverLoad_conn = self.coverLoad.PictureData.connect(self.DecodeCover)

        self.backdropLoad = ePicLoad()
        try:
            self.backdropLoad.PictureData.get().append(self.DecodeBackdrop)
        except:
            self.backdropLoad_conn = self.backdropLoad.PictureData.connect(self.DecodeBackdrop)

        self.logoLoad = ePicLoad()
        try:
            self.logoLoad.PictureData.get().append(self.DecodeLogo)
        except:
            self.logoLoad_conn = self.logoLoad.PictureData.connect(self.DecodeLogo)

        self.onFirstExecBegin.append(self.createSetup)
        self.onLayoutFinish.append(self.__layoutFinished)

    def __layoutFinished(self):
        if debugs:
            print("*** __layoutFinished ***")

        self.setTitle(self.setup_title)

    def createSetup(self, data=None):
        if debugs:
            print("*** createSetup ***")

        self["x_title"].setText("")
        self["x_description"].setText("")

        if self.level == 1:
            self.sortby = "number"
            self.getCategories()

        if self.level == 2:
            self.all_data = []
            self.pages_downloaded = set()
            self.current_page = 1

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

        self.resetButtons()
        self.selectionChanged()

    def getCategories(self):
        if debugs:
            print("*** getCategories **")

        self.list1 = []
        self.prelist = []

        self["key_epg"].setText("")

        currentPlaylist = glob.active_playlist

        currentCategoryList = currentPlaylist.get("data", {}).get("vod_categories", {}).get("js", [])
        currentHidden = set(currentPlaylist.get("player_info", {}).get("vodhidden", []))

        hidden = "0" in currentHidden

        for index, item in enumerate(currentCategoryList, start=len(self.prelist)):
            if not isinstance(item, dict):
                continue

            category_name = item.get("title", "No category")
            category_id = item.get("id", "999999")
            hidden = category_id in currentHidden
            self.list1.append([index, str(category_name), str(category_id), hidden])

        glob.originalChannelList1 = self.list1[:]
        self.buildLists()

    def getLevel2(self, response):
        if debugs:
            print("*** getLevel2 ***")

        # added tmdb plugin instead of imdb for dreamos
        if TMDB_installed:
            self["key_epg"].setText("TMDB")
        else:
            self["key_epg"].setText("IMDB")

        if self.chosen_category == "favourites":
            response = glob.active_playlist["player_info"].get("vodfavourites", [])

        self.list2 = []

        if response:
            for index, channel in enumerate(response):

                if not isinstance(channel, dict) or not channel:
                    self.list2.append([index, "", "", "", "", "", "", False, "", "", False, "", "", "", ""])
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

                cmd = str(channel.get("cmd", ""))
                hidden = False
                cover = str(channel.get("pic", ""))

                if cover and cover.startswith("http"):
                    try:
                        cover = cover.replace(r"\/", "/")
                    except:
                        pass

                    if cover == "https://image.tmdb.org/t/p/w600_and_h900_bestv2" or cover == "https://image.tmdb.org/t/p/w500":
                        cover = ""

                    if cover.startswith("https://image.tmdb.org/t/p/") or cover.startswith("http://image.tmdb.org/t/p/"):
                        dimensions = cover.partition("/p/")[2].partition("/")[0]

                        if screenwidth.width() <= 1280:
                            cover = cover.replace(dimensions, "w200")
                        elif screenwidth.width() <= 1920:
                            cover = cover.replace(dimensions, "w300")
                        else:
                            cover = cover.replace(dimensions, "w400")
                else:
                    cover = ""

                added = str(channel.get("added", ""))
                category_id = str(channel.get("category_id", ""))
                container_extension = "mp4"
                rating = str(channel.get("rating", ""))
                year = str(channel.get("year", "")).strip()

                # Try to extract 4-digit year from the 'year' field itself
                pattern = r'\b\d{4}\b'
                matches = re.findall(pattern, year)

                if matches:
                    year = matches[0]  # use the first 4-digit number found
                else:
                    # fallback to extracting from 'name'
                    matches = re.findall(pattern, name)
                    if matches:
                        year = matches[-1]  # use the last 4-digit number from name

                tmdb = ""
                trailer = ""
                next_url = ""

                favourite = False

                if "vodfavourites" in glob.active_playlist["player_info"]:
                    for fav in glob.active_playlist["player_info"]["vodfavourites"]:
                        if str(stream_id) == str(fav["id"]):
                            favourite = True
                            break
                else:
                    glob.active_playlist["player_info"]["vodfavourites"] = []

                """
                0 = index
                1 = name
                2 = stream_id
                3 = cover
                4 = added
                5 = rating
                6 = next_url
                7 = favourite
                8 = extensions
                9 = year
                10 = hidden
                11 = tmdb
                12 = trailer
                13 = category_id
                14 = cmd
                """

                self.list2.append([
                    index,
                    str(name),
                    str(stream_id),
                    str(cover),
                    str(added),
                    str(rating),
                    str(next_url),
                    favourite,
                    str(container_extension),
                    year,
                    hidden,
                    tmdb,
                    str(trailer),
                    str(category_id),
                    str(cmd)
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

        paged_url = self._updateUrlPage(url, self.current_page)

        if paged_url in self.pages_downloaded:
            return self.all_data

        try:
            data = make_request(paged_url, method="POST", headers=self.headers, params=None, response_type="json")

            if not data and self.retry is False:
                self.retry = True
                self.reauthorize()
                data = make_request(paged_url, method="POST", headers=self.headers, params=None, response_type="json")

            if data:

                if pythonVer == 3 and glob.hassuperscript:
                    data = clean_names(data)

                js = data.get("js", {})
                try:
                    self.total_items = int(js.get("total_items", 0))
                except (ValueError, TypeError):
                    self.total_items = 0
                current_page_data = js.get("data", [])

                if not hasattr(self, 'all_data') or not isinstance(self.all_data, list) or not self.all_data:
                    self.all_data = [{} for _ in range(self.total_items)]

                self.sort_check = False

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

    def downloadSearchData(self, url, page=1):
        if debugs:
            print("*** downloadApiData ***", url)

        if not hasattr(self, 'all_data') or not isinstance(self.all_data, list):
            self.all_data = []

        paged_url = self._updateUrlPage(url, self.current_page)

        if paged_url in self.pages_downloaded:
            return self.all_data

        try:
            data = make_request(paged_url, method="POST", headers=self.headers, params=None, response_type="json")

            if not data and self.retry is False:
                self.retry = True
                self.reauthorize()
                data = make_request(paged_url, method="POST", headers=self.headers, params=None, response_type="json")

            if data:

                if pythonVer == 3 and glob.hassuperscript:
                    data = clean_names(data)

                js = data.get("js", {})
                try:
                    self.total_items = int(js.get("total_items", 0))
                except (ValueError, TypeError):
                    self.total_items = 0
                current_page_data = js.get("data", [])

                if not hasattr(self, 'all_data') or not isinstance(self.all_data, list) or not self.all_data:
                    self.all_data = [{} for _ in range(self.total_items)]

                self.sort_check = False

                start_index = (self.current_page - 1) * 14

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
        """
        if debugs:
            print("*** _updateUrlPage ***", url, page)
            """

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

        self.hideVod()

        if self["key_blue"].getText() != _("Reset Search"):
            self.pre_list = [buildCategoryList(x[0], x[1], x[2], x[3]) for x in self.prelist if not x[3]]
        else:
            self.pre_list = []

        if self.list1:
            self.main_list = [buildCategoryList(x[0], x[1], x[2], x[3]) for x in self.list1 if not x[3]]

            self["main_list"].setList(self.pre_list + self.main_list)

            if self["main_list"].getCurrent():
                self["main_list"].setIndex(glob.nextlist[-1]["index"])

    def buildList2(self):
        if debugs:
            print("*** buildList2 ***")

        self.main_list = []

        if self.chosen_category == "favourites":
            self.main_list = [buildVodStreamList(x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], x[8], x[9], x[10], x[11], x[12], x[13], x[14]) for x in self.list2 if x[7] is True]
        else:
            self.main_list = [buildVodStreamList(x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], x[8], x[9], x[10], x[11], x[12], x[13], x[14]) for x in self.list2 if x[10] is False]
        self["main_list"].setList(self.main_list)

        if self["main_list"].getCurrent():
            self.showVod()
            self["main_list"].setIndex(glob.nextlist[-1]["index"])

    def updateList2(self):
        if debugs:
            print("*** updateList2 ***")

        self.main_list = []

        if self.chosen_category == "favourites":
            self.main_list = [buildVodStreamList(x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], x[8], x[9], x[10], x[11], x[12], x[13], x[14]) for x in self.list2 if x[7] is True]
        else:
            self.main_list = [buildVodStreamList(x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], x[8], x[9], x[10], x[11], x[12], x[13], x[14]) for x in self.list2 if x[10] is False]
        self["main_list"].setList(self.main_list)

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
                self["key_blue"].setText(_("Search"))
                self["key_menu"].setText("+/-")
            else:
                self["key_menu"].setText("")
                self["key_blue"].setText(_("Search All"))

            if self.chosen_category == "favourites":
                self["key_blue"].setText("")
                self["key_menu"].setText("")

    def selectionChanged(self):
        if debugs:
            print("*** selectionChanged ***")

        self.tmdbresults = ""

        if self.cover_download_deferred:
            self.cover_download_deferred.cancel()

        if self.logo_download_deferred:
            self.logo_download_deferred.cancel()

        if self.backdrop_download_deferred:
            self.backdrop_download_deferred.cancel()

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
            self["main_title"].setText("{}: {}".format(self.main_title, channel_title))

            if self.level == 2:
                self.timerVOD = eTimer()

                try:
                    self.timerVOD.callback.append(self.downloadVodInfo)
                except:
                    self.timerVOD_conn = self.timerVOD.timeout.connect(self.downloadVodInfo)
                self.timerVOD.start(300, True)

                if not hasattr(self, 'current_page') or page != self.current_page:
                    self.current_page = page

                    if self["key_blue"].getText() == _("Reset Search"):
                        search_url = "{0}?type=vod&action=get_ordered_list&search={1}&genre=*&sortby=number&JsHttpRequest=1-xml".format(self.portal, self.query)
                        response = self.downloadApiData(search_url)
                    else:
                        response = self.downloadApiData(glob.nextlist[-1]["next_url"])
                    self.getLevel2(response)

        else:
            position = 0
            position_all = 0
            page = 0
            page_all = 0

            self["page"].setText(_("Page: ") + "{}/{}".format(page, page_all))
            self["listposition"].setText("{}/{}".format(position, position_all))
            self["key_yellow"].setText("")
            self["key_blue"].setText("")
            self.hideVod()

    def downloadCover(self):
        if debugs:
            print("*** downloadCover ***")

        if cfg.channelcovers.value is False:
            return

        if self["main_list"].getCurrent():
            try:
                os.remove(os.path.join(dir_tmp, "cover.jpg"))
            except:
                pass

            desc_image = ""
            try:
                desc_image = self["main_list"].getCurrent()[5]
            except:
                pass

            if self.cover_download_deferred and not self.cover_download_deferred.called:
                self.cover_download_deferred.cancel()

            if self.tmdbresults:
                desc_image = (str(self.tmdbresults.get("cover_big") or "").strip() or str(self.tmdbresults.get("movie_image") or "").strip())

            # add new image into level 2 list.
            current_index = self["main_list"].getIndex()
            if current_index != -1:
                item = list(self.main_list[current_index])   # Convert tuple to list
                item[5] = desc_image                         # Update the desired value (e.g., cover image)
                self.main_list[current_index] = tuple(item)  # Convert back to tuple
                self["main_list"].setList(self.main_list)    # Refresh the list display
                self["main_list"].setIndex(current_index)

            if "http" in desc_image:
                self.cover_download_deferred = self.agent.request(b'GET', desc_image.encode(), Headers({'User-Agent': [b"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"]}))
                self.cover_download_deferred.addCallback(self.handleCoverResponse)
                self.cover_download_deferred.addErrback(self.handleCoverError)
            else:
                self.loadDefaultCover()

    def downloadLogo(self):
        """
        if debugs:
            print("*** downloadLogo ***")
            """

        if cfg.channelcovers.value is False:
            return

        if self["main_list"].getCurrent():
            try:
                os.remove(os.path.join(dir_tmp, "logo.png"))
            except:
                pass

            logo_image = ""

            if self.logo_download_deferred and not self.logo_download_deferred.called:
                self.logo_download_deferred.cancel()

            if self.tmdbresults:
                logo_image = str(self.tmdbresults.get("logo") or "").strip()

            if "http" in logo_image:
                self.logo_download_deferred = self.agent.request(b'GET', logo_image.encode(), Headers({'User-Agent': [b"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"]}))
                self.logo_download_deferred.addCallback(self.handleLogoResponse)
                self.logo_download_deferred.addErrback(self.handleLogoError)
            else:
                self.loadDefaultLogo()

    def downloadBackdrop(self):
        """
        if debugs:
            print("*** downloadBackdrop ***")
            """

        if cfg.channelcovers.value is False:
            return

        if self["main_list"].getCurrent():
            try:
                os.remove(os.path.join(dir_tmp, "backdrop.jpg"))
            except:
                pass

            backdrop_image = ""

            if self.backdrop_download_deferred and not self.backdrop_download_deferred.called:
                self.backdrop_download_deferred.cancel()

            if self.tmdbresults:
                backdrop_image = str(self.tmdbresults.get("backdrop_path") or "").strip()

                if "http" in backdrop_image:
                    self.redirect_count = 0
                    self.backdrop_download_deferred = self.agent.request(b'GET', backdrop_image.encode(), Headers({'User-Agent': [b"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"]}))
                    self.backdrop_download_deferred.addCallback(self.handleBackdropResponse)
                    self.backdrop_download_deferred.addErrback(self.handleBackdropError)
                else:
                    self.loadDefaultBackdrop()
            else:
                self.loadDefaultBackdrop()

    def downloadCoverFromUrl(self, url):
        """
        if debugs:
            print("*** downloadCoverFromUrl ***")
            """

        self.cover_download_deferred = self.agent.request(
            b'GET',
            url.encode(),
            Headers({'User-Agent': [b"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"]})
        )
        self.cover_download_deferred.addCallback(self.handleCoverResponse)
        self.cover_download_deferred.addErrback(self.handleCoverError)

    def handleCoverResponse(self, response):
        """
        if debugs:
            print("*** handlecoverresponse ***")
            """

        if response.code == 200:
            d = readBody(response)
            d.addCallback(self.handleCoverBody)
            return d
        elif response.code in (301, 302):
            if self.redirect_count < 2:
                self.redirect_count += 1
                location = response.headers.getRawHeaders('location')[0]
                self.downloadCoverFromUrl(location)
        else:
            self.handleCoverError("HTTP error code: %s" % response.code)

    def handleLogoResponse(self, response):
        """
        if debugs:
            print("*** handlelogoresponse ***")
            """

        if response.code == 200:
            d = readBody(response)
            d.addCallback(self.handleLogoBody)
            return d

    def handleBackdropResponse(self, response):
        """
        if debugs:
            print("*** handlebackdropresponse ***")
            """

        if response.code == 200:
            d = readBody(response)
            d.addCallback(self.handleBackdropBody)
            return d

    def handleCoverBody(self, body):
        """
        if debugs:
            print("*** handlecoverbody ***")
            """

        temp = os.path.join(dir_tmp, "cover.jpg")
        with open(temp, 'wb') as f:
            f.write(body)
        self.resizeCover(temp)

    def handleLogoBody(self, body):
        """
        if debugs:
            print("*** handlelogobody ***")
            """

        temp = os.path.join(dir_tmp, "logo.png")
        with open(temp, 'wb') as f:
            f.write(body)
        self.resizeLogo(temp)

    def handleBackdropBody(self, body):
        """
        if debugs:
            print("*** handlebackdropbody ***")
            """

        temp = os.path.join(dir_tmp, "backdrop.jpg")
        with open(temp, 'wb') as f:
            f.write(body)
        self.resizeBackdrop(temp)

    def handleCoverError(self, error):
        """
        if debugs:
            print("*** handle error ***")
            """

        print(error)
        self.loadDefaultCover()

    def handleLogoError(self, error):
        """
        if debugs:
            print("*** handle error ***")
            """

        print(error)
        self.loadDefaultLogo()

    def handleBackdropError(self, error):
        """
        if debugs:
            print("*** handle error ***")
            """

        print(error)
        self.loadDefaultBackdrop()

    def loadDefaultCover(self, data=None):
        """
        if debugs:
            print("*** loadDefaultCover ***")
            """

        if self["vod_cover"].instance:
            self["vod_cover"].instance.setPixmapFromFile(os.path.join(skin_directory, "common/blank.png"))

    def loadDefaultLogo(self, data=None):
        """
        if debugs:
            print("*** loadDefaultLogo ***")
            """

        if self["vod_logo"].instance:
            self["vod_logo"].instance.setPixmapFromFile(os.path.join(skin_directory, "common/blank.png"))

    def loadDefaultBackdrop(self, data=None):
        """
        if debugs:
            print("*** loadDefaultBackdrop ***")
            """

        if self["vod_backdrop"].instance:
            self["vod_backdrop"].instance.setPixmapFromFile(os.path.join(skin_directory, "common/blank.png"))

    def resizeCover(self, data=None):
        """
        if debugs:
            print("*** resizeCover ***")
            """

        if self["main_list"].getCurrent() and self["vod_cover"].instance:
            preview = os.path.join(dir_tmp, "cover.jpg")
            if os.path.isfile(preview):
                try:
                    self.coverLoad.setPara([self["vod_cover"].instance.size().width(), self["vod_cover"].instance.size().height(), 1, 1, 0, 1, "FF000000"])
                    self.coverLoad.startDecode(preview)
                except Exception as e:
                    print(e)

    def resizeLogo(self, data=None):
        """
        if debugs:
            print("*** resizeLogo ***")
            """

        if self["main_list"].getCurrent() and self["vod_logo"].instance:
            preview = os.path.join(dir_tmp, "logo.png")
            if os.path.isfile(preview):
                width = self["vod_logo"].instance.size().width()
                height = self["vod_logo"].instance.size().height()
                size = [width, height]

                try:
                    im = Image.open(preview)
                    if im.mode != "RGBA":
                        im = im.convert("RGBA")

                    try:
                        im.thumbnail(size, Image.Resampling.LANCZOS)
                    except:
                        im.thumbnail(size, Image.ANTIALIAS)

                    bg = Image.new("RGBA", size, (255, 255, 255, 0))

                    left = (size[0] - im.size[0])

                    bg.paste(im, (left, 0), mask=im)

                    bg.save(preview, "PNG", compress_level=0)

                    if self["vod_logo"].instance:
                        self["vod_logo"].instance.setPixmapFromFile(preview)
                        self["vod_logo"].show()
                except Exception as e:
                    print("Error resizing logo:", e)
                    self["vod_logo"].hide()

    def resizeBackdrop(self, data=None):
        if debugs:
            print("*** resizeBackdrop ***")

        if not (self["main_list"].getCurrent() and self["vod_backdrop"].instance):
            return

        preview = os.path.join(dir_tmp, "backdrop.jpg")
        if not os.path.isfile(preview):
            return

        try:
            # Get final size from vod_backdrop instance
            bd_width, bd_height = self["vod_backdrop"].instance.size().width(), self["vod_backdrop"].instance.size().height()
            bd_size = (bd_width, bd_height)

            # Load and process the source image
            im = Image.open(preview)
            if im.mode != "RGBA":
                im = im.convert("RGBA")

            # Backward-compatible resampling method selection
            try:
                # New versions (Pillow >= 9.1.0)
                resample_method = Image.Resampling.LANCZOS
            except AttributeError:
                try:
                    # Older versions (Pillow 2.0+)
                    resample_method = Image.LANCZOS
                except AttributeError:
                    # Very old versions (pre-2.0)
                    resample_method = Image.ANTIALIAS

            # Resize image
            im.thumbnail(bd_size, resample_method)

            # Load and resize mask with same resampling method
            mask = Image.open(os.path.join(skin_directory, "common/mask2.png"))
            if mask.mode != "RGBA":
                mask = mask.convert("RGBA")
            mask = mask.resize(im.size, resample_method)

            # Create transparent background
            background = Image.new('RGBA', bd_size, (0, 0, 0, 0))

            # Calculate position (center horizontally)

            # Get actual resized image dimensions (fallback for older Pillow)
            try:
                im_w, im_h = im.width, im.height
            except AttributeError:
                im_w, im_h = im.size

            # Calculate position (center horizontally)
            x_offset = (bd_width - im_w) // 2
            y_offset = 0

            # Paste with mask for gradient transparency
            background.paste(im, (x_offset, y_offset), mask)

            # Save result
            output = os.path.join(dir_tmp, "background.png")
            background.save(output, "PNG")

            # Update backdrop
            if self["vod_backdrop"].instance:
                self["vod_backdrop"].instance.setPixmapFromFile(output)
                self["vod_backdrop"].show()

        except Exception as e:
            print("Error resizing backdrop:", e)
            self["vod_backdrop"].hide()

    def DecodeCover(self, PicInfo=None):
        """
        if debugs:
            print("*** decodecover ***")
            """

        ptr = self.coverLoad.getData()
        if ptr is not None and self.level == 2:
            self["vod_cover"].instance.setPixmap(ptr)
            self["vod_cover"].show()
        else:
            self["vod_cover"].hide()

    def DecodeLogo(self, PicInfo=None):
        """
        if debugs:
            print("*** decodelogo ***")
            """

        ptr = self.logoLoad.getData()
        if ptr is not None and self.level == 2:
            self["vod_logo"].instance.setPixmap(ptr)
            self["vod_logo"].show()
        else:
            self["vod_logo"].hide()

    def DecodeBackdrop(self, PicInfo=None):
        """
        if debugs:
            print("*** decodebackdrop ***")
            """

        ptr = self.backdropLoad.getData()
        if ptr is not None and self.level == 2:
            self["vod_backdrop"].instance.setPixmap(ptr)
            self["vod_backdrop"].show()
        else:
            self["vod_backdrop"].hide()

    def goUp(self):
        instance = self["main_list"].master.master.instance
        instance.moveSelection(instance.moveUp)
        self.selectionChanged()

    def goDown(self):
        instance = self["main_list"].master.master.instance
        instance.moveSelection(instance.moveDown)
        self.selectionChanged()

    def pageUp(self):
        instance = self["main_list"].master.master.instance
        instance.moveSelection(instance.pageUp)
        self.selectionChanged()

    def pageDown(self):
        instance = self["main_list"].master.master.instance
        instance.moveSelection(instance.pageDown)
        self.selectionChanged()

    def reset(self):
        if debugs:
            print("*** reset ***")

        self["main_list"].setIndex(0)
        self.selectionChanged()

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
                activelist.sort(key=lambda x: x[0], reverse=False)

            next_sort_type = next(islice(cycle(sortlist), self.sortindex + 1, None))
            self.sortText = str(next_sort_type)

            self["key_yellow"].setText(self.sortText)
            glob.nextlist[-1]["sort"] = self["key_yellow"].getText()

            self.list1 = activelist

            self.buildLists()

        if self.level == 2:

            sortlist = [_("Sort: A-Z"), _("Sort: Added")]

            for index, item in enumerate(sortlist):
                if str(item) == str(self.sortText):
                    self.sortindex = index
                    break

            if current_sort == _("Sort: A-Z"):
                self.sortby = "name"
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
                category_id = self.list2[0][13]
                glob.nextlist[-1]["next_url"] = "{0}?type=vod&action=get_ordered_list&movie_id=0&season_id=0&episode_id=0&category={1}&fav=0&sortby={2}&hd=0&not_ended=0&p=1&JsHttpRequest=1-xml".format(self.portal, category_id, self.sortby)
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
        else:
            self.session.openWithCallback(self.filterChannels, VirtualKeyBoard, title=_("Filter this category..."), text=self.searchString)

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

                self.query = quote_plus(result.encode('utf-8'))

                paged_url = "{0}?type=vod&action=get_ordered_list&search={1}&genre=*&sortby=name&JsHttpRequest=1-xml".format(self.portal, self.query)

                response = self.downloadSearchData(paged_url)

                self.getLevel2(response)

                if not self.list2:
                    self.searchString = ""
                    self.session.openWithCallback(self.search, MessageBox, _("No results found."), type=MessageBox.TYPE_ERROR, timeout=5)

                else:
                    self["key_blue"].setText(_("Reset Search"))
                    self["key_yellow"].setText("")

    def resetSearch(self):
        if debugs:
            print("*** resetsearch ***")

        self["key_yellow"].setText(self.sortText)

        if self.level == 1:
            self["key_blue"].setText(_("Search"))
            activelist = glob.originalChannelList1[:]
            self.list1 = activelist
            self.filterresult = ""
            glob.nextlist[-1]["filter"] = self.filterresult
            self.buildLists()
        else:
            self["key_blue"].setText(_("Search All"))
            activelist = glob.originalChannelList2[:]
            self.pages_downloaded = set()
            self.current_page = 1
            self.all_data = []
            self.sort_check = True

            if self["main_list"].getCurrent():
                self["main_list"].setIndex(0)

            glob.nextlist[-1]["index"] = 0

            self.current_page = 1
            if self.level == 2:
                category_id = self.list2[0][13]
                glob.nextlist[-1]["next_url"] = "{0}?type=vod&action=get_ordered_list&movie_id=0&season_id=0&episode_id=0&category={1}&fav=0&sortby={2}&hd=0&not_ended=0&p=1&JsHttpRequest=1-xml".format(self.portal, category_id, self.sortby)

                response = self.downloadApiData(glob.nextlist[-1]["next_url"])
                self.getLevel2(response)

                self.filterresult = ""
                glob.nextlist[-1]["filter"] = self.filterresult

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
                    next_url = "{0}?type=vod&action=get_ordered_list&movie_id=0&season_id=0&episode_id=0&category={1}&fav=0&sortby={2}&hd=0&not_ended=0&p=1&JsHttpRequest=1-xml".format(self.portal, category_id, self.sortby)
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
                    from . import vodplayer

                    stream_id = self["main_list"].getCurrent()[4]
                    streamtype = glob.active_playlist["player_info"]["vodtype"]
                    command = self["main_list"].getCurrent()[14]
                    next_url = command

                    if debugs:
                        print("*** original command **", command)

                    if str(command).startswith("/media/"):
                        pre_vod_url = (str(self.portal) + "?type=vod&action=get_ordered_list&movie_id={}&season_id=0&episode_id=0&category=1&fav=0&sortby=&hd=0&not_ended=0&p=1&JsHttpRequest=1-xml").format(stream_id)

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
                            url = "{0}?type=vod&action=create_link&cmd={1}&series=&forced_storage=&disable_ad=0&download=0&force_ch_link_check=0&JsHttpRequest=1-xml".format(self.portal, command)
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
                            if streamtype == "1":
                                streamtype = "4097"
                    else:
                        next_url = ""

                    self.reference = eServiceReference(int(streamtype), 0, str(next_url))
                    self.reference.setName(glob.currentchannellist[glob.currentchannellistindex][0])
                    self.session.openWithCallback(self.setIndex, vodplayer.EStalker_VodPlayer, str(next_url), str(streamtype), stream_id)

                else:
                    self.createSetup()

    def setIndex(self, data=None):
        """
        if debugs:
            print("*** setIndex ***")
            """

        if self["main_list"].getCurrent():
            self["main_list"].setIndex(glob.currentchannellistindex)

    def back(self, data=None):
        if debugs:
            print("*** back ***")

        self.showfav = False
        self.chosen_category = ""
        if self.level == 2:
            try:
                self.timerVOD.stop()
            except:
                pass

            if self.cover_download_deferred:
                self.cover_download_deferred.cancel()

            if self.logo_download_deferred:
                self.logo_download_deferred.cancel()

            if self.backdrop_download_deferred:
                self.backdrop_download_deferred.cancel()

        del glob.nextlist[-1]

        if not glob.nextlist:
            self.close()
        else:
            self["x_title"].setText("")
            self["x_description"].setText("")

            if cfg.stopstream.value:
                self.stopStream()

            self.level -= 1

            self["category_actions"].setEnabled(True)
            self["channel_actions"].setEnabled(False)
            self["key_epg"].setText("")
            self.sortText = _("Sort: A-Z")

            self.buildLists()

            self.loadDefaultCover()
            self.loadDefaultLogo()
            self.loadDefaultBackdrop()

    def showHiddenList(self):
        if debugs:
            print("*** showHiddenList ***")

        if self["key_menu"].getText() and self["main_list"].getCurrent():
            from . import hidden
            current_list = self.prelist + self.list1 if self.level == 1 else self.list2
            if self.level == 1 or (self.level == 2 and self.chosen_category != "favourites"):
                self.session.openWithCallback(self.createSetup, hidden.EStalker_HiddenCategories, "vod", current_list, self.level)

    def showfavourites(self):
        if debugs:
            print("*** show favourites ***")

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

        for fav in glob.active_playlist["player_info"]["vodfavourites"]:
            if self["main_list"].getCurrent()[4] == fav["id"]:
                favExists = True
                favStream_id = fav["id"]
                break

        try:
            self.list2[current_index][7] = not self.list2[current_index][7]
        except:
            pass

        if favExists:
            glob.active_playlist["player_info"]["vodfavourites"] = [x for x in glob.active_playlist["player_info"]["vodfavourites"] if str(x["id"]) != str(favStream_id)]
        else:
            # index = 0
            # name = 1
            # stream_id = 2
            # stream_icon = 3
            # added = 4
            # rating = 5
            # next_url = 6
            # favourite = 7
            # container_extension = 8
            # year = 9

            newfavourite = {
                "name": self.list2[current_index][1],
                "id": self.list2[current_index][2],
                "stream_icon": self.list2[current_index][3],
                "added": self.list2[current_index][4],
                "rating": self.list2[current_index][5],
                "container_extension": self.list2[current_index][8],
                "year": self.list2[current_index][9],
                "cmd": self.list2[current_index][14]
            }

            glob.active_playlist["player_info"]["vodfavourites"].insert(0, newfavourite)

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
            json.dump(self.playlists_all, f)

        if self.chosen_category == "favourites":
            del self.list2[current_index]

        self.buildLists()

    def hideVod(self):
        """
        if debugs:
            print("*** hideVod ***")
            """

        self["vod_cover"].hide()
        self["vod_logo"].hide()
        self["vod_backdrop"].hide()
        self["main_title"].setText("")
        self["x_title"].setText("")
        self["x_description"].setText("")
        self["tagline"].setText("")
        self["facts"].setText("")
        self["vod_director_label"].setText("")
        self["vod_country_label"].setText("")
        self["vod_cast_label"].setText("")
        self["vod_director"].setText("")
        self["vod_country"].setText("")
        self["vod_cast"].setText("")
        self["rating_text"].setText("")
        self["rating_percent"].setText("")
        self["overview"].setText("")

    def clearVod(self):
        """
        if debugs:
            print("*** clearVod ***")
            """
        self["vod_cover"].hide()
        self["vod_logo"].hide()
        self["vod_backdrop"].hide()
        self["main_title"].setText("")
        self["x_title"].setText("")
        self["x_description"].setText("")
        self["tagline"].setText("")
        self["facts"].setText("")
        self["vod_director"].setText("")
        self["vod_country"].setText("")
        self["vod_cast"].setText("")
        self["rating_text"].setText("0.0")
        self["rating_percent"].setText("")

    def showVod(self):
        """
        if debugs:
            print("*** showVod ***")
            """
        if self["main_list"].getCurrent():
            self["vod_cover"].show()
            self["vod_logo"].show()
            self["vod_backdrop"].show()

    def downloadVodInfo(self):
        if debugs:
            print("*** downloadVodInfo ***")

        self.clearVod()

        if self["main_list"].getCurrent():
            self.tmdbresults = {}
            self.getTMDB()

    def strip_foreign_mixed(self, text):
        has_ascii = bool(re.search(r'[\x00-\x7F]', text))
        has_non_ascii = bool(re.search(r'[^\x00-\x7F]', text))

        if has_ascii and has_non_ascii:
            # Remove only non-ASCII characters
            text = re.sub(r'[^\x00-\x7F]+', '', text)

        return text

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
        # searchtitle = re.sub(r'^.{2}\+? ?- ?', '', searchtitle, flags=re.IGNORECASE)

        # remove all leading content between and including || or |
        searchtitle = re.sub(r'^\|\|.*?\|\|', '', searchtitle)
        searchtitle = re.sub(r'^\|.*?\|', '', searchtitle)
        searchtitle = re.sub(r'\|.*?\|', '', searchtitle)

        # remove all leading content between and including ┃┃ or ┃
        searchtitle = re.sub(r'^┃┃.*?┃┃', '', searchtitle)
        searchtitle = re.sub(r'^┃.*?┃', '', searchtitle)
        searchtitle = re.sub(r'^┃.*?┃', '', searchtitle)
        searchtitle = re.sub(r'┃.*?┃', '', searchtitle)

        # remove all content between and including () unless it's all digits
        # searchtitle = re.sub(r'\((?!\d+\))[^()]*\)', '', searchtitle)
        searchtitle = re.sub(r'\(\(.*?\)\)|\([^()]*\)', '', searchtitle)

        # remove all content between and including []
        searchtitle = re.sub(r'\[\[.*?\]\]|\[.*?\]', '', searchtitle)

        # remove trailing year (but not if the whole title *is* a year)
        if not re.match(r'^\d{4}$', searchtitle.strip()):
            searchtitle = re.sub(r'[\s\-]*(?:[\(\[\"]?\d{4}[\)\]\"]?)$', '', searchtitle)

        # remove up to 6 characters followed by space and dash at start (e.g. "EN -", "BE-NL -")
        searchtitle = re.sub(r'^[A-Za-z0-9\-]{1,7}\s*-\s*', '', searchtitle, flags=re.IGNORECASE)

        # Strip foreign / non-ASCII characters
        searchtitle = self.strip_foreign_mixed(searchtitle)

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
            "multi-sub", "multi-subs", "multisub", "ozlem", "sd", "top250", "u-", "uhd", "vod", "x264",
            "amz", "dolby", "audio", "8k", "3840p", "50fps", "60fps", "hevc", "raw ", "vip ", "NF", "d+", "a+", "vp", "prmt", "mrvl"
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

    def getTMDB(self):
        if debugs:
            print("**** getTMDB ***")

        current_item = self["main_list"].getCurrent()

        if current_item:
            title = ""
            searchtitle = ""
            self.searchtitle = ""
            self.isIMDB = False
            self.tmdb_id_exists = False
            title = self["main_list"].getCurrent()[0]
            year = self["main_list"].getCurrent()[9]

            try:
                os.remove(os.path.join(dir_tmp, "search.txt"))
            except:
                pass

            searchtitle = self.stripjunk(title)
            searchtitle = quote(searchtitle, safe="")

            if not self.isIMDB:
                searchurl = 'http://api.themoviedb.org/3/search/movie?api_key={}&query={}'.format(self.check(self.apitoken), searchtitle)
                if year:
                    searchurl = 'http://api.themoviedb.org/3/search/movie?api_key={}&primary_release_year={}&query={}'.format(self.check(self.apitoken), year, searchtitle)
            else:
                searchurl = 'http://api.themoviedb.org/3/find/{}?api_key={}&external_source=imdb_id'.format(self.tmdbresults["tmdb_id"], self.check(self.apitoken))

            if pythonVer == 3:
                searchurl = searchurl.encode()

            filepath = os.path.join(dir_tmp, "search.txt")

            try:
                downloadPage(searchurl, filepath, timeout=10).addCallback(self.processTMDB).addErrback(self.failed)
            except Exception as e:
                print("download TMDB error {}".format(e))

    def failed(self, data=None):
        if debugs:
            print("*** failed ***")

        if data:
            print(data)
        return

    def processTMDB(self, result=None):
        if debugs:
            print("***processTMDB ***")

        IMDB = self.isIMDB
        resultid = ""
        search_file_path = os.path.join(dir_tmp, "search.txt")

        try:
            with codecs.open(search_file_path, "r", encoding="utf-8") as f:
                response = f.read()

            if response:
                self.searchresult = json.loads(response)
                if IMDB is False:
                    results = self.searchresult.get("results", [])
                else:
                    results = self.searchresult.get("movie_results", [])

                if results:
                    resultid = results[0].get("id", "")

                if not resultid:
                    self.displayTMDB()
                    return

                self.getTMDBDetails(resultid)
        except Exception as e:
            print("Error processing TMDB response:", e)

    def getTMDBDetails(self, resultid=None):
        self.resultid = resultid
        if debugs:
            print(" *** getTMDBDetails ***")

        detailsurl = ""
        languagestr = ""

        try:
            os.remove(os.path.join(dir_tmp, "search.txt"))
        except:
            pass

        language = cfg.TMDBLanguage2.value
        if language:
            languagestr = "&language=" + str(language)

        detailsurl = "http://api.themoviedb.org/3/movie/{}?api_key={}&append_to_response=credits,images,release_dates,videos{}&include_image_language=en".format(
            resultid, self.check(self.apitoken), languagestr)

        if pythonVer == 3:
            detailsurl = detailsurl.encode()

        filepath = os.path.join(dir_tmp, "search.txt")

        try:
            downloadPage(detailsurl, filepath, timeout=10).addCallback(self.processTMDBDetails).addErrback(self.failed)
        except Exception as e:
            print("download TMDB details error:", e)

    def processTMDBDetails(self, result=None):
        if debugs:
            print("*** processTMDBDetails ***")

        response = ""
        self.tmdbdetails = []
        director = []
        country = []
        poster_path = ""
        backdrop_path = ""
        logo_path = ""
        logos = []

        try:
            with codecs.open(os.path.join(dir_tmp, "search.txt"), "r", encoding="utf-8") as f:
                response = f.read()
        except Exception as e:
            print("Error reading TMDB response:", e)

        if response:
            try:
                self.tmdbdetails = json.loads(response, object_pairs_hook=OrderedDict)
            except Exception as e:
                print("Error parsing TMDB response:", e)
            else:
                if self.tmdbdetails:

                    if "title" in self.tmdbdetails and self.tmdbdetails["title"]:
                        self.tmdbresults["name"] = str(self.tmdbdetails["title"].strip())

                    if "original_title" in self.tmdbdetails and self.tmdbdetails["original_title"]:
                        self.tmdbresults["o_name"] = str(self.tmdbdetails["original_title"]).strip()

                    if "runtime" in self.tmdbdetails:
                        runtime = self.tmdbdetails["runtime"]
                        if runtime and runtime != 0:
                            self.tmdbresults["originalduration"] = runtime
                            duration_timedelta = timedelta(minutes=runtime)
                            formatted_time = "{:0d}h {:02d}m".format(duration_timedelta.seconds // 3600, (duration_timedelta.seconds % 3600) // 60)
                            self.tmdbresults["duration"] = str(formatted_time)

                    if "origin_country" in self.tmdbdetails and self.tmdbdetails["origin_country"]:
                        try:
                            country = self.tmdbdetails["origin_country"][0]
                            self.tmdbresults["country"] = country
                        except:
                            pass

                    if not country and "production_countries" in self.tmdbdetails and self.tmdbdetails["production_countries"]:
                        country = ", ".join(str(pcountry["name"]) for pcountry in self.tmdbdetails["production_countries"])
                        self.tmdbresults["country"] = country

                    if "release_date" in self.tmdbdetails and self.tmdbdetails["release_date"]:
                        self.tmdbresults["releaseDate"] = str(self.tmdbdetails["release_date"]).strip()

                    if "poster_path" in self.tmdbdetails and self.tmdbdetails["poster_path"]:
                        poster_path = str(self.tmdbdetails["poster_path"]).strip()

                    if "backdrop_path" in self.tmdbdetails and self.tmdbdetails["backdrop_path"]:
                        backdrop_path = str(self.tmdbdetails["backdrop_path"]).strip()

                    if "images" in self.tmdbdetails and "logos" in self.tmdbdetails["images"]:
                        logos = self.tmdbdetails["images"]["logos"]

                    if logos:
                        logo_path = logos[0].get("file_path", "")
                    else:
                        logo_path = ""

                    coversize = "w200"
                    backdropsize = "w1280"
                    logosize = "w200"

                    if screenwidth.width() <= 1280:
                        coversize = "w200"
                        backdropsize = "w1280"
                        logosize = "w300"

                    elif screenwidth.width() <= 1920:
                        coversize = "w300"
                        backdropsize = "w1280"
                        logosize = "w300"
                    else:
                        coversize = "w400"
                        backdropsize = "w1280"
                        logosize = "w500"

                    if poster_path:
                        self.tmdbresults["cover_big"] = "http://image.tmdb.org/t/p/{}{}".format(coversize, poster_path)

                    if backdrop_path:
                        self.tmdbresults["backdrop_path"] = "http://image.tmdb.org/t/p/{}{}".format(backdropsize, backdrop_path)

                    if logo_path:
                        self.tmdbresults["logo"] = "http://image.tmdb.org/t/p/{}{}".format(logosize, logo_path)

                    if "overview" in self.tmdbdetails and self.tmdbdetails["overview"]:
                        self.tmdbresults["description"] = str(self.tmdbdetails["overview"]).strip()

                    if "tagline" in self.tmdbdetails and self.tmdbdetails["tagline"]:
                        self.tmdbresults["tagline"] = str(self.tmdbdetails["tagline"]).strip()

                    if "vote_average" in self.tmdbdetails:
                        rating_str = self.tmdbdetails["vote_average"]
                        if rating_str not in [None, 0, 0.0, "0", "0.0"]:
                            try:
                                rating = float(rating_str)
                                rounded_rating = round(rating, 1)
                                self.tmdbresults["rating"] = "{:.1f}".format(rounded_rating)
                            except ValueError:
                                self.tmdbresults["rating"] = 0
                        else:
                            self.tmdbresults["rating"] = 0

                    if "genres" in self.tmdbdetails and self.tmdbdetails["genres"]:
                        genre = " / ".join(str(genreitem["name"]) for genreitem in self.tmdbdetails["genres"][:4])
                        self.tmdbresults["genre"] = genre

                    if "credits" in self.tmdbdetails:
                        if "cast" in self.tmdbdetails["credits"] and self.tmdbdetails["credits"]["cast"]:
                            cast = ", ".join(actor["name"] for actor in self.tmdbdetails["credits"]["cast"][:10])
                            self.tmdbresults["cast"] = cast

                        if "crew" in self.tmdbdetails["credits"] and self.tmdbdetails["credits"]["crew"]:
                            director = ", ".join(actor["name"] for actor in self.tmdbdetails["credits"]["crew"] if actor.get("job") == "Director")
                            self.tmdbresults["director"] = director

                    if pythonVer == 3 and "videos" in self.tmdbdetails and "results" in self.tmdbdetails["videos"]:
                        current_index = self["main_list"].getIndex()
                        for video in self.tmdbdetails["videos"]["results"]:
                            if video.get("site") == "YouTube" and video.get("type") == "Trailer" and "key" in video:
                                try:
                                    self.list2[current_index][12] = str(video["key"])
                                except:
                                    pass

                                self.updateList2()
                                break  # Stop after first match

                            elif video.get("site") == "YouTube" and video.get("type") == "Clip" and "key" in video:
                                try:
                                    self.list2[current_index][12] = str(video["key"])
                                except:
                                    pass

                                self.updateList2()
                                break  # Stop after first match

                    def get_certification(data, language_code):
                        fallback_codes = ["GB", "US"]

                        # First attempt to find the certification with the specified language code
                        if "release_dates" in data and "results" in data["release_dates"]:
                            for release in data["release_dates"]["results"]:
                                if "iso_3166_1" in release and "release_dates" in release:
                                    if release["iso_3166_1"] == language_code:
                                        return release["release_dates"][0].get("certification")

                            # If no match found or language_code is blank, try the fallback codes
                            for fallback_code in fallback_codes:
                                for release in data["release_dates"]["results"]:
                                    if "iso_3166_1" in release and "release_dates" in release:
                                        if release["iso_3166_1"] == fallback_code:
                                            return release["release_dates"][0].get("certification")

                        # If no match found in fallback codes, return None or an appropriate default value
                        return None

                    language = cfg.TMDBLanguage2.value
                    if not language:
                        language = "en-GB"

                    language = language.split("-")[1]

                    certification = get_certification(self.tmdbdetails, language)

                    if certification:
                        self.tmdbresults["certification"] = str(certification)

                    language2 = cfg.TMDBLanguage2.value or "en-GB"
                    current_overview = self.tmdbdetails.get("overview", "").strip()

                    if not current_overview and not language2.startswith("en"):
                        fallback_url = "http://api.themoviedb.org/3/movie/{}?api_key={}&language=en".format(self.resultid, self.check(self.apitoken))

                        filepath = os.path.join(dir_tmp, "search2.txt")

                        def handleFallback(result=None):
                            try:
                                with codecs.open(filepath, "r", encoding="utf-8") as f:
                                    fallback_response = f.read()
                                fallback_data = json.loads(fallback_response)
                                english_overview = fallback_data.get("overview", "").strip()
                                if english_overview:
                                    self.tmdbresults["description"] = english_overview
                                if not self.tmdbresults.get("tagline") and fallback_data.get("tagline"):
                                    self.tmdbresults["tagline"] = fallback_data["tagline"].strip()
                            except Exception as e:
                                print("Error processing fallback TMDB data:", e)
                            self.displayTMDB()

                        try:
                            downloadPage(fallback_url, filepath, timeout=10).addCallback(handleFallback).addErrback(self.failed)
                            return  # Delay display until fallback completes
                        except Exception as e:
                            print("Fallback TMDB download error:", e)

                    self.displayTMDB()

    def displayTMDB(self):
        if debugs:
            print("*** displayTMDB ***")

        current_item = self["main_list"].getCurrent()

        if current_item and self.level == 2:
            stream_url = current_item[3]

            if self.tmdbresults:
                info = self.tmdbresults

                # Initialize all optional fields
                duration = ""
                genre = ""
                release_date = ""
                director = ""
                country = ""
                cast = ""
                certification = ""
                rating = 0
                text = ""

                # Rating
                try:
                    rating = float(info.get("rating", 0) or 0)
                except Exception:
                    rating = 0

                rating_texts = {
                    (0.0, 0.0): "",
                    (0.1, 0.5): "",
                    (0.6, 1.0): "",
                    (1.1, 1.5): "",
                    (1.6, 2.0): "",
                    (2.1, 2.5): "",
                    (2.6, 3.0): "",
                    (3.1, 3.5): "",
                    (3.6, 4.0): "",
                    (4.1, 4.5): "",
                    (4.6, 5.0): "",
                    (5.1, 5.5): "",
                    (5.6, 6.0): "",
                    (6.1, 6.5): "",
                    (6.6, 7.0): "",
                    (7.1, 7.5): "",
                    (7.6, 8.0): "",
                    (8.1, 8.5): "",
                    (8.6, 9.0): "",
                    (9.1, 9.5): "",
                    (9.6, 10.0): "",
                }

                for rating_range, rating_text in rating_texts.items():
                    if rating_range[0] <= rating <= rating_range[1]:
                        text = rating_text
                        break

                # percent dial
                self["rating_percent"].setText(str(text))

                try:
                    rounded_rating = round(rating, 1)
                    rating_str = "{:.1f}".format(rounded_rating)
                except Exception:
                    rating_str = str(rating)

                self["rating_text"].setText(rating_str)

                # Titles
                self["x_title"].setText(str(info.get("name") or info.get("o_name") or "").strip())

                # Description / overview
                self["x_description"].setText(str(info.get("description") or info.get("plot") or "").strip())
                self["overview"].setText(_("Overview") if self["x_description"].getText() else "")

                # Duration
                duration = str(info.get("duration") or "").strip()

                # Genre
                genre = str(info.get("genre") or "").strip()

                # Release date
                for key in ["releaseDate", "release_date", "releasedate"]:
                    if key in info and info[key]:
                        try:
                            release_date = datetime.strptime(info[key], "%Y-%m-%d").strftime("%d-%m-%Y")
                            break
                        except Exception:
                            release_date = str(info[key]).strip()

                # Director
                director = str(info.get("director") or "").strip()
                self["vod_director"].setText(director)
                self["vod_director_label"].setText(_("Director:") if director else "")

                # Country
                country = str(info.get("country") or "").strip()
                self["vod_country"].setText(country)
                self["vod_country_label"].setText(_("Country:") if country else "")

                # Cast
                cast = str(info.get("cast") or info.get("actors") or "").strip()
                self["vod_cast"].setText(cast)
                self["vod_cast_label"].setText(_("Cast:") if cast else "")

                # Tagline
                self["tagline"].setText(str(info.get("tagline") or "").strip())

                # Certification
                certification = str(info.get("certification") or "").strip().upper()
                if certification:
                    certification = _("Rating: ") + certification

                # Stream format
                try:
                    stream_format = stream_url.split(".")[-1]
                except Exception:
                    stream_format = ""

                # Facts
                facts = self.buildFacts(str(certification), str(release_date), str(genre), str(duration), str(stream_format))
                self["facts"].setText(str(facts))

                if self.level == 2 and cfg.channelcovers.value:
                    self.downloadCover()
                    self.downloadLogo()
                    self.downloadBackdrop()

    def clearWatched(self):
        if debugs:
            print("*** clearWatched ***")

        if self.level == 2:
            current_id = str(self["main_list"].getCurrent()[4])
            watched_list = glob.active_playlist["player_info"].get("vodwatched", [])
            if current_id in watched_list:
                watched_list.remove(current_id)

        with open(playlists_json, "r") as f:
            try:
                self.playlists_all = json.load(f)
            except:
                os.remove(playlists_json)
                return

            for i, playlist in enumerate(self.playlists_all):
                playlist_info = playlist.get("playlist_info", {})
                current_playlist_info = glob.active_playlist.get("playlist_info", {})
                if (playlist_info.get("domain") == current_playlist_info.get("domain") and
                        playlist_info.get("mac") == current_playlist_info.get("mac")):
                    self.playlists_all[i] = glob.active_playlist
                    break

        with open(playlists_json, "w") as f:
            json.dump(self.playlists_all, f)

        self.buildLists()

    def imdb(self):
        if debugs:
            print("*** imdb ***")

        if self["main_list"].getCurrent():
            if self.level == 2:
                self.openIMDb()

    def openIMDb(self):
        if debugs:
            print("*** openIMDb ***")

        if (isDreambox or isVTI) and TMDB_installed:
            try:
                name = str(self["main_list"].getCurrent()[0])
                name = self.stripjunk(name)
                if isDreambox:
                    self.session.open(ScreenMain, name, 2)
                elif isVTI:
                    self.session.open(tmdb.tmdbScreen, name, 2)
            except:
                self.session.open(MessageBox, _("The TMDB plugin is not installed!\nPlease install it."), type=MessageBox.TYPE_INFO, timeout=10)
        else:
            try:
                from Plugins.Extensions.IMDb.plugin import IMDB
                try:
                    name = str(self["main_list"].getCurrent()[0])
                    name = self.stripjunk(name)
                except:
                    name = ""
                self.session.open(IMDB, name, False)
            except ImportError:
                self.session.open(MessageBox, _("The IMDb plugin is not installed!\nPlease install it."), type=MessageBox.TYPE_INFO, timeout=10)

    def check(self, token):
        """
        if debugs:
            print("*** check ***")
            """

        result = base64.b64decode(token)
        result = zlib.decompress(base64.b64decode(result))
        result = base64.b64decode(result).decode()
        return result

    def buildFacts(self, certification, release_date, genre, duration, stream_format):
        if debugs:
            print("*** buildfacts ***")

        facts = []

        if certification:
            facts.append(certification)
        if release_date:
            facts.append(release_date)
        if genre:
            facts.append(genre)
        if duration:
            facts.append(duration)
        if stream_format:
            facts.append(str(stream_format).upper())

        return " • ".join(facts)

    def trailer(self):
        if debugs:
            print("*** trailer ***")

        if pythonVer == 2:
            return

        ffmpeg_installed = check_and_install_ffmpeg()
        if not ffmpeg_installed:
            return

        pytubefix_installed = check_and_install_pytubefix()
        if not pytubefix_installed:
            return

        current_item = self["main_list"].getCurrent()
        if not current_item:
            return

        trailer_id = str(current_item[12])
        if not trailer_id:
            return

        try:
            from pytubefix import YouTube
            from pytubefix.exceptions import AgeRestrictedError

            yt = YouTube("https://www.youtube.com/watch?v=" + str(trailer_id))

            video_stream = max(
                [s for s in yt.streams.filter(mime_type="video/webm", progressive=False)
                 if s.resolution and int(s.resolution[:-1]) <= 1080],
                key=lambda s: int(s.resolution[:-1]),
                default=None
            )

            # If no WebM stream found, try MP4
            if video_stream is None:
                video_stream = max(
                    [s for s in yt.streams.filter(mime_type="video/mp4", progressive=False)
                     if s.resolution and int(s.resolution[:-1]) <= 1080],
                    key=lambda s: int(s.resolution[:-1]),
                    default=None
                )

            # Get lowest quality audio stream
            audio_stream = yt.streams.filter(mime_type="audio/mp4", progressive=False, only_audio=True).order_by("abr").desc().last()

            if not video_stream or not audio_stream:
                self.session.open(MessageBox, _("No trailer found."), type=MessageBox.TYPE_INFO, timeout=5)
                return

            download_dir = dir_tmp
            video_file = "video_{}.mp4".format(trailer_id)
            audio_file = "audio_{}.mp4".format(trailer_id)
            output_file = "output_{}.mkv".format(trailer_id)

            video_stream.download(output_path=download_dir, filename=video_file, skip_existing=False)
            audio_stream.download(output_path=download_dir, filename=audio_file, skip_existing=False)

            # Merge video and audio with FFmpeg
            ffmpeg_cmd = [
                "ffmpeg",
                "-i", download_dir + video_file,
                "-i", download_dir + audio_file,
                "-c:v", "copy",
                "-c:a", "copy",
                "-y", download_dir + output_file  # Overwrite if exists
            ]

            result = subprocess.run(ffmpeg_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

            if result.returncode != 0:
                print("FFmpeg failed to merge the files!")
                return

            self.trailer_next(download_dir + output_file, yt.title)

        except AgeRestrictedError:
            self.session.open(MessageBox, _("Trailer is age restricted, and can't be accessed without logging in."), type=MessageBox.TYPE_INFO, timeout=5)

        except Exception as e:
            print(e)

    def trailer_next(self, file, title):
        if debugs:
            print("*** trailer_next ***")

        if self["main_list"].getCurrent():
            from . import vodplayer
            current_index = self["main_list"].getIndex()
            glob.nextlist[-1]["index"] = current_index
            glob.currentchannellist = self.main_list[:]
            glob.currentchannellistindex = current_index

            streamtype = glob.active_playlist["player_info"]["vodtype"]
            next_url = file

            self.reference = eServiceReference(int(streamtype), 0, next_url)
            self.reference.setName(title)
            self.session.openWithCallback(self.trailer_cleanup, vodplayer.EStalker_VodPlayer, str(next_url), str(streamtype), None)

    def trailer_cleanup(self, *args):
        if debugs:
            print("*** trailer_cleanup ***")

        for file in os.listdir(dir_tmp):
            if file.startswith("video_") or file.startswith("audio_") or file.startswith("output_"):
                try:
                    os.remove(os.path.join(dir_tmp, file))
                except:
                    pass

        self.setIndex()

    def stopStream(self):
        if debugs:
            print("*** stopStream ***")

        if glob.currentPlayingServiceRefString != glob.newPlayingServiceRefString:
            if glob.newPlayingServiceRefString != "":
                if self.session.nav.getCurrentlyPlayingServiceReference():
                    self.session.nav.stopService()
                self.session.nav.playService(eServiceReference(glob.currentPlayingServiceRefString))
                glob.newPlayingServiceRefString = glob.currentPlayingServiceRefString


def check_and_install_ffmpeg():
    try:
        subprocess.run(["ffmpeg", "-version"], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return True
    except subprocess.CalledProcessError:
        print("FFmpeg is not installed. Installing...")

    # Check if opkg exists to determine the package manager
    if os.path.exists("/etc/opkg/"):
        if install_ffmpeg_opkg():
            return True
    else:
        if install_ffmpeg_apt():
            return True

    return False


def install_ffmpeg_opkg():
    try:
        subprocess.run(["opkg", "update"], check=True)
        subprocess.run(["opkg", "install", "ffmpeg"], check=True)
        print("FFmpeg installed successfully.")
        return True
    except subprocess.CalledProcessError:
        print("Failed to install FFmpeg using opkg.")
        return False


def install_ffmpeg_apt():
    try:
        subprocess.run(["apt-get", "update"], check=True)
        subprocess.run(["apt-get", "-y", "install", "ffmpeg"], check=True)
        print("FFmpeg installed successfully.")
        return True
    except subprocess.CalledProcessError:
        print("Failed to install FFmpeg using apt-get.")
        return False


def get_python_site_packages():
    python_dirs = sorted([d for d in os.listdir("/usr/lib/") if d.startswith("python")], reverse=True)
    for py_dir in python_dirs:
        site_packages = os.path.join("/usr/lib", py_dir, "site-packages")

        if os.path.exists(site_packages):
            return site_packages
    return None


def get_latest_pytubefix_version():
    url = "https://pypi.org/project/pytubefix/#files"
    response = requests.get(url)

    if response.status_code == 200:
        # matches = re.findall(r'href="[^"]+/pytubefix-(\d+\.\d+\.\d+)\.tar\.gz"', response.text)
        matches = re.findall(r'href="[^"]*/pytubefix-([\w\.\-]+)\.tar\.gz"', response.text)

        if matches:
            latest_version = sorted(matches, key=lambda s: list(map(int, s.split('.'))), reverse=True)[0]
            return latest_version
        else:
            print("No .tar.gz versions found on PyPI.")
            return None
    else:
        print("Failed to fetch PyPI page. Status:", response.status_code)
        return None


def check_pytubefix_version():
    try:
        import pytubefix

        if hasattr(pytubefix, '__version__'):
            return pytubefix.__version__
        else:
            try:
                import pkg_resources
                return pkg_resources.get_distribution("pytubefix").version
            except Exception:
                return None
    except Exception:
        return None


def check_and_install_pytubefix():
    site_packages = get_python_site_packages()
    pytubefix_path = os.path.join(site_packages, "pytubefix") if site_packages else None

    # Attempt to get the latest version from PyPI
    expected_version = get_latest_pytubefix_version()

    # Fallback to 8.12.3 if PyPI version retrieval fails
    if not expected_version:
        print("Using fallback version 8.12.3")
        expected_version = "8.12.3"

    # Define static URL for fallback version 8.12.3
    if expected_version == "8.12.3":
        url = "https://files.pythonhosted.org/packages/2f/43/528a5c70382499fdad0af998c8d06bcd0ada1a92ed30623396c144f9b9c0/pytubefix-8.12.3.tar.gz"
    else:
        # Dynamic URL for the latest version fetched from PyPI
        url = "https://files.pythonhosted.org/packages/source/p/pytubefix/pytubefix-%s.tar.gz" % expected_version

    # Check if pytubefix is already installed and verify version
    if pytubefix_path and os.path.exists(pytubefix_path) and os.listdir(pytubefix_path):
        installed_version = check_pytubefix_version()
        if installed_version == expected_version:
            print("pytubefix version %s is already installed" % installed_version)
            return True
        else:
            print("pytubefix version is %s, expected %s. Reinstalling..." % (installed_version, expected_version))

    # Ensure temporary directory exists
    if not os.path.exists(dir_tmp):
        try:
            os.makedirs(dir_tmp)
            print("Created temporary directory:", dir_tmp)
        except Exception as e:
            print("Failed to create temporary directory:", str(e))
            return False

    # Download the correct tarball version
    response = requests.get(url)

    if response.status_code == 200:
        tarball_path = os.path.join(dir_tmp, "pytubefix-%s.tar.gz" % expected_version)
        with open(tarball_path, "wb") as f:
            f.write(response.content)

        print("Tarball downloaded successfully at", tarball_path)

        try:
            import tarfile
            with tarfile.open(tarball_path, "r:gz") as tar:
                tar.extractall(path=dir_tmp)
        except Exception as e:
            print("Failed to extract tarball:", str(e))
            return False

        extracted_path = os.path.join(dir_tmp, "pytubefix-%s" % expected_version, "pytubefix")
        print("Checking if extracted pytubefix folder exists at", extracted_path)

        if os.path.exists(extracted_path):
            print("pytubefix folder found at", extracted_path, ". Copying it to", pytubefix_path)
            try:
                if os.path.exists(pytubefix_path):
                    shutil.rmtree(pytubefix_path)

                shutil.copytree(extracted_path, pytubefix_path)
                print("pytubefix installed successfully at", pytubefix_path)

                # Cleanup temporary files
                try:
                    if os.path.exists(tarball_path):
                        os.remove(tarball_path)
                    extracted_root = os.path.join(dir_tmp, "pytubefix-%s" % expected_version)
                    if os.path.exists(extracted_root):
                        shutil.rmtree(extracted_root)
                    print("Cleaned up temporary files")
                except Exception as e:
                    print("Cleanup failed:", str(e))

                return True
            except Exception as e:
                print("Failed to copy pytubefix:", str(e))
                return False
        else:
            print("Failed to find pytubefix folder at", extracted_path)
            return False
    else:
        print("Failed to download pytubefix tarball. HTTP status code:", response.status_code)
        return False


def buildCategoryList(index, title, category_id, hidden):
    png = LoadPixmap(os.path.join(common_path, "more.png"))
    return (title, png, index, category_id, hidden)


"""
0 = index
1 = name
2 = stream_id
3 = cover
4 = added
5 = rating
6 = next_url
7 = favourite
8 = extensions
9 = year
10 = hidden
11 = tmdb
12 = trailer
13 = category_id
14 = cmd
"""


def buildVodStreamList(index, title, stream_id, cover, added, rating, next_url, favourite, container_extension, year, hidden, tmdb, trailer, category_id, cmd):
    png = LoadPixmap(os.path.join(common_path, "play.png"))
    if trailer and pythonVer == 3:
        png = LoadPixmap(os.path.join(common_path, "play2.png"))

    if favourite:
        png = LoadPixmap(os.path.join(common_path, "favourite.png"))
    for channel in glob.active_playlist["player_info"]["vodwatched"]:
        try:
            if stream_id and channel and (int(stream_id) == int(channel)):
                png = LoadPixmap(os.path.join(common_path, "watched.png"))
        except:
            pass

    return (title, png, index, next_url, stream_id, cover, added, rating, container_extension, year, hidden, tmdb, trailer, category_id, cmd)
