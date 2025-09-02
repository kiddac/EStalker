#!/usr/bin/python
# -*- coding: utf-8 -*-

from __future__ import division

# Standard library imports
import base64
import codecs
import json
import os
import re
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
from .plugin import cfg, common_path, dir_tmp, pythonVer, screenwidth, skin_directory, debugs, isDreambox
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


class EStalker_Series_Categories(Screen):
    ALLOW_SUSPEND = True

    def __init__(self, session):
        if debugs:
            print("*** series init ***")

        Screen.__init__(self, session)
        self.session = session
        glob.categoryname = "series"

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

        self.setup_title = _("Series Categories")
        self.main_title = _("TV Series")

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

        self.tmdbresults = {}

        self.storedtitle = ""
        self.storedseason = ""
        self.storedepisode = ""
        self.storedyear = ""
        self.storedcover = ""
        self.storedtmdb = ""
        self.storedbackdrop = ""
        self.storedlogo = ""
        self.storeddescription = ""
        self.storedcast = ""
        self.storeddirector = ""
        self.storedgenre = ""
        self.storedreleasedate = ""
        self.storedrating = ""

        self.repeatcount = 0

        self.sort_check = False
        self.showfav = False

        self.seriesfirstlist = True
        self.seasonsfirstlist = True
        self.episodesfirstlist = True

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
            "1": self.clearWatched,
            "tv": self.favourite,
            "stop": self.favourite,
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

    def createSetup(self, data=None):
        if debugs:
            print("*** createSetup ***")

        self["x_title"].setText("")
        self["x_description"].setText("")

        if self.level == 1:
            self.sortby = "number"
            self.getCategories()

        elif self.level == 2:
            self.all_series_data = []
            self.series_pages_downloaded = set()
            self.series_current_page = 1

            if self.chosen_category != "favourites":
                response = self.downloadApiData(glob.nextlist[-1]["next_url"])
            else:
                response = ""

            self.sortby = "number"
            self.seriesfirstlist = True
            self.getSeries(response)

        elif self.level == 3:
            self.all_seasons_data = []
            self.seasons_pages_downloaded = set()
            self.seasons_current_page = 1
            response = self.downloadApiData(glob.nextlist[-1]["next_url"])
            self.sortby = "number"
            self.seasonsfirstlist = True
            self.getSeasons(response)

        elif self.level == 4:
            self.all_episodes_data = []
            self.episodes_pages_downloaded = set()
            self.episodes_current_page = 1
            response = self.downloadApiData(glob.nextlist[-1]["next_url"])
            self.sortby = "number"
            self.episodesfirstlist = True
            self.getEpisodes(response)

    def buildLists(self):
        if debugs:
            print("*** buildLists ***")

        if self.level == 1:
            self.buildCategories()

        elif self.level == 2:
            self.buildSeries()

        elif self.level == 3:
            self.buildSeasons()

        elif self.level == 4:
            self.buildEpisodes()

        self.resetButtons()
        self.selectionChanged()

    def getCategories(self):
        if debugs:
            print("*** getCategories **")

        self.list1 = []
        self.prelist = []

        self["key_epg"].setText("")

        currentPlaylist = glob.active_playlist

        currentCategoryList = currentPlaylist.get("data", {}).get("series_categories", {}).get("js", [])
        currentHidden = set(currentPlaylist.get("player_info", {}).get("serieshidden", []))

        hidden = "0" in currentHidden

        for index, item in enumerate(currentCategoryList, start=len(self.prelist)):
            category_name = item.get("title", "No category")
            category_id = item.get("id", "999999")
            hidden = category_id in currentHidden
            self.list1.append([index, str(category_name), str(category_id), hidden])

        glob.originalChannelList1 = self.list1[:]

        self.buildLists()

    def getSeries(self, response):
        if debugs:
            print("*** getSeries ***")

        if self.chosen_category == "favourites":
            response = glob.active_playlist["player_info"].get("seriesfavourites", [])

        # self.series_info = ""
        index = 0
        self.list2 = []

        self.storedtitle = ""
        self.storedseason = ""
        self.storedepisode = ""
        self.storedyear = ""
        self.storedcover = ""
        self.storedtmdb = ""
        self.storedbackdrop = ""
        self.storedlogo = ""
        self.storeddescription = ""
        self.storedcast = ""
        self.storeddirector = ""
        self.storedgenre = ""
        self.storedreleasedate = ""
        self.storedrating = ""
        self.tmdbretry = 0

        if response:
            for index, channel in enumerate(response):

                if not isinstance(channel, dict) or not channel:
                    self.list2.append([index, "", "", "", "", "", "", "", "", "", "", "", "", False, "", "", False, ""])
                    # 0 index, 1 name, 2 series_id, 3 cover, 4 plot, 5 cast, 6 director, 7 genre, 8 releaseDate, 9 rating, 10 last_modified, 11 next_url, 12 tmdb, 13 hidden, 14 year, 15 backdrop, 16 favourite, 17 category_id

                    continue

                series_id = str(channel.get("id", ""))

                if not series_id or series_id == "0" or series_id == "*":
                    continue

                name = str(channel.get("name", ""))

                if not name or name == "None":
                    continue

                if name and '\" ' in name:
                    parts = name.split('\" ', 1)
                    if len(parts) > 1:
                        name = parts[0]

                hidden = False

                cover = str(channel.get("screenshot_uri", ""))

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

                last_modified = str(channel.get("added", ""))
                category_id = str(channel.get("category_id", ""))
                rating = str(channel.get("rating_imdb", ""))
                plot = str(channel.get("description", ""))
                cast = str(channel.get("actors", ""))
                director = str(channel.get("director", ""))
                genre = str(channel.get("genres_str", ""))
                tmdb = ""
                releaseDate = (channel.get("year") or "")
                releaseDate = str(releaseDate) if releaseDate is not None else ""
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

                if year:
                    self.storedyear = year
                else:
                    self.storedyear = ""

                backdrop_path = channel.get("screenshots", "")

                if backdrop_path:
                    try:
                        backdrop_path = channel["screenshots"][0]
                    except:
                        pass

                tmdb = ""
                next_url = ""

                favourite = False

                if "seriesfavourites" in glob.active_playlist["player_info"]:
                    for fav in glob.active_playlist["player_info"]["seriesfavourites"]:
                        if str(series_id) == str(fav["id"]):
                            favourite = True
                            break
                else:
                    glob.active_playlist["player_info"]["seriesfavourites"] = []

                # 0 index, 1 name, 2 series_id, 3 cover, 4 plot, 5 cast, 6 director, 7 genre, 8 releaseDate, 9 rating, 10 last_modified, 11 next_url, 12 tmdb, 13 hidden, 14 year, 15 backdrop, 16 favourite, 17 category_id
                self.list2.append([
                    index,
                    str(name),
                    str(series_id),
                    str(cover),
                    str(plot),
                    str(cast),
                    str(director),
                    str(genre),
                    str(releaseDate),
                    str(rating),
                    str(last_modified),
                    str(next_url),
                    str(tmdb),
                    hidden,
                    str(year),
                    str(backdrop_path),
                    favourite,
                    str(category_id)
                ])

        if self.seriesfirstlist:
            glob.originalChannelList2 = self.list2[:]
            self.seriesfirstlist = False

        self.buildLists()

    def getSeasons(self, response):

        if debugs:
            print("*** getSeasons ***")

        index = 0
        self.list3 = []
        if response:
            for index, channel in enumerate(response):

                if not isinstance(channel, dict) or not channel:
                    self.list3.append([index, "", "", "", "", "", "", "", "", "", "", "", "", False, "", "", False, "", ""])
                    # 0 index, 1 name, 2 series_id, 3 cover, 4 plot, 5 cast, 6 director, 7 genre, 8 releaseDate, 9 rating, 10 last_modified, 11 next_url, 12 tmdb, 13 hidden, 14 year, 15 backdrop, 16 favourite, 17 category_id, 18 season
                    continue

                season_id = str(channel.get("id", ""))
                season_number = season_id.split(":")[1] if ":" in season_id else ""

                if not season_id or season_id == "0" or season_id == "*":
                    continue

                name = str(channel.get("name", self.title2))

                if not name or name == "None":
                    continue

                if name and '\" ' in name:
                    parts = name.split('\" ', 1)
                    if len(parts) > 1:
                        name = parts[0]

                hidden = False

                cover = str(channel.get("screenshot_uri", self.cover2))

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

                last_modified = str(channel.get("added", "0"))
                category_id = str(channel.get("category_id", ""))
                rating = str(channel.get("rating_imdb", self.rating2))
                plot = str(channel.get("description", self.plot2))
                cast = str(channel.get("actors", self.cast2))
                director = str(channel.get("director", self.director2))
                genre = str(channel.get("genres_str", self.genre2))
                tmdb = self.tmdb2
                releaseDate = (channel.get("year") or self.releaseDate2)
                releaseDate = str(releaseDate) if releaseDate is not None else ""
                year = str(channel.get("year", "")).strip()

                # Try to extract 4-digit year from the 'year' field itself
                pattern = r'\b\d{4}\b'
                matches = re.findall(pattern, year)

                if matches:
                    year = matches[0]  # use the first 4-digit number found

                if year:
                    self.storedyear = year
                else:
                    self.storedyear = ""

                backdrop_path = self.backdrop_path2

                tmdb = ""
                next_url = ""

                favourite = False

                # 0 index, 1 name, 2 season_id, 3 cover, 4 plot, 5 cast, 6 director, 7 genre, 8 releaseDate, 9 rating, 10 last_modified, 11 next_url, 12 tmdb, 13 hidden, 14 year, 15 backdrop, 16 favourite, 17 category_id, 18 season_number
                self.list3.append([
                    index,
                    str(name),
                    str(season_id),
                    str(cover),
                    str(plot),
                    str(cast),
                    str(director),
                    str(genre),
                    str(releaseDate),
                    str(rating),
                    str(last_modified),
                    str(next_url),
                    str(tmdb),
                    hidden,
                    str(year),
                    str(backdrop_path),
                    favourite,
                    str(category_id),
                    str(season_number)
                ])

        self.list3.sort(key=lambda x: int(x[18]) if x[18].isdigit() else 0)

        if self.seasonsfirstlist:
            glob.originalChannelList3 = self.list3[:]
            self.seasonsfirstlist = False

        self.buildLists()

    def getEpisodes(self, response):
        if debugs:
            print("*** getEpisodes ***")

        index = 0
        self.list4 = []

        if response:
            for item in response:
                target_season = None
                if item.get("id") == self.storedseasonid:
                    target_season = item
                    break

            if not target_season:
                return

            season_id = str(target_season.get("id", ""))
            season_number = season_id.split(":")[1] if ":" in season_id else ""
            hidden = False

            cover = self.cover2

            last_modified = str(target_season.get("added", "0"))
            category_id = str(target_season.get("category_id", ""))
            rating = str(target_season.get("rating_imdb", self.rating2))
            plot = str(target_season.get("description", self.plot2))
            cast = str(target_season.get("actors", self.cast2))
            director = str(target_season.get("director", self.director2))
            genre = str(target_season.get("genres_str", self.genre2))
            tmdb = self.tmdb2
            releaseDate = (target_season.get("year") or self.releaseDate2)
            releaseDate = str(releaseDate) if releaseDate is not None else ""
            year = str(target_season.get("year", "")).strip()

            # Try to extract 4-digit year from the 'year' field itself
            pattern = r'\b\d{4}\b'
            matches = re.findall(pattern, year)

            if matches:
                year = matches[0]  # use the first 4-digit number found

            if year:
                self.storedyear = year
            else:
                self.storedyear = ""

            backdrop_path = self.backdrop_path2

            tmdb = self.tmdb2

            next_url = ""

            favourite = False

            episode_numbers = target_season.get("series", [])
            cmd = target_season.get("cmd", "")

            for index, episode_num in enumerate(episode_numbers):
                episode_id = episode_num
                name = "Episode %d" % episode_num

                self.list4.append([
                    index,
                    str(name),
                    str(season_id),
                    str(cover),
                    str(plot),
                    str(cast),
                    str(director),
                    str(genre),
                    str(releaseDate),
                    str(rating),
                    str(last_modified),
                    str(next_url),
                    str(tmdb),
                    hidden,
                    str(year),
                    str(backdrop_path),
                    favourite,
                    str(category_id),
                    str(season_number),
                    str(episode_id),
                    str(cmd),

                ])

        if self.episodesfirstlist:
            glob.originalChannelList4 = self.list4[:]
            self.episodesfirstlist = False

        self.buildLists()

    def downloadApiData(self, url, page=1):
        if debugs:
            print("*** downloadApiData ***", url)

        if self.level == 2:
            if not hasattr(self, 'all_series_data') or not isinstance(self.all_series_data, list):
                self.all_series_data = []

            paged_url = self._updateUrlPage(url, self.series_current_page)

            if paged_url in self.series_pages_downloaded:
                return self.all_series_data

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
                        self.series_total_items = int(js.get("total_items", 0))
                    except (ValueError, TypeError):
                        self.series_total_items = 0
                    current_page_data = js.get("data", [])

                    if not hasattr(self, 'all_series_data') or not isinstance(self.all_series_data, list) or not self.all_series_data:
                        self.all_series_data = [{} for _ in range(self.series_total_items)]

                    self.sort_check = False

                    # Calculate the position where this page's data should be stored
                    start_index = (self.series_current_page - 1) * 14

                    # Insert the new data at the correct positions
                    for i, item in enumerate(current_page_data):
                        self.all_series_data[start_index + i] = item
                        self.series_pages_downloaded.add(paged_url)

                    """
                    if debugs:
                        print("*** self.all_series_data ***", json.dumps(self.all_series_data))
                        """

                    return self.all_series_data

            except Exception as e:
                print("Error downloading API data for page {}: {}".format(self.series_current_page, e))
                return self.all_series_data

            self.session.openWithCallback(self.back, MessageBox, _("Server error or invalid link."), MessageBox.TYPE_ERROR, timeout=3)
            return self.all_series_data

        elif self.level == 3:
            self.all_seasons_data = []

            paged_url = self._updateUrlPage(url, self.seasons_current_page)

            if paged_url in self.seasons_pages_downloaded:
                return self.all_seasons_data

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
                        self.seasons_total_items = int(js.get("total_items", 0))
                    except (ValueError, TypeError):
                        self.seasons_total_items = 0
                    current_page_data = js.get("data", [])

                    if not hasattr(self, 'all_seasons_data') or not isinstance(self.all_seasons_data, list) or not self.all_seasons_data:
                        self.all_seasons_data = [{} for _ in range(self.seasons_total_items)]

                    self.sort_check = False

                    # Calculate the position where this page's data should be stored
                    start_index = (self.seasons_current_page - 1) * 14

                    # Insert the new data at the correct positions
                    for i, item in enumerate(current_page_data):
                        self.all_seasons_data[start_index + i] = item
                        self.seasons_pages_downloaded.add(paged_url)

                    """
                    if debugs:
                        print("*** self.all_seasons_data ***", json.dumps(self.all_seasons_data))
                        """

                    return self.all_seasons_data

            except Exception as e:
                print("Error downloading API data for page {}: {}".format(self.seasons_current_page, e))
                return self.all_seasons_data

            self.session.openWithCallback(self.back, MessageBox, _("Server error or invalid link."), MessageBox.TYPE_ERROR, timeout=3)
            return self.all_seasons_data

        elif self.level == 4:
            self.all_episodes_data = []

            paged_url = self._updateUrlPage(url, self.episodes_current_page)

            if paged_url in self.episodes_pages_downloaded:
                return self.all_episodes_data

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
                        self.episodes_total_items = int(js.get("total_items", 0))
                    except (ValueError, TypeError):
                        self.episodes_total_items = 0
                    current_page_data = js.get("data", [])

                    if not hasattr(self, 'all_episodes_data') or not isinstance(self.all_episodes_data, list) or not self.all_episodes_data:
                        self.all_episodes_data = [{} for _ in range(self.episodes_total_items)]

                    self.sort_check = False

                    # Calculate the position where this page's data should be stored
                    start_index = (self.episodes_current_page - 1) * 14

                    # Insert the new data at the correct positions
                    for i, item in enumerate(current_page_data):
                        self.all_episodes_data[start_index + i] = item
                        self.episodes_pages_downloaded.add(paged_url)

                    """
                    if debugs:
                        print("*** self.all_episodes_data ***", json.dumps(self.all_episodes_data))
                        """

                    return self.all_episodes_data

            except Exception as e:
                print("Error downloading API data for page {}: {}".format(self.episodes_current_page, e))
                return self.all_episodes_data

            self.session.openWithCallback(self.back, MessageBox, _("Server error or invalid link."), MessageBox.TYPE_ERROR, timeout=3)
            return self.all_episodes_data

    def downloadSearchData(self, url, page=1):
        if debugs:
            print("*** downloadApiData ***", url)

        if self.level == 2:
            if not hasattr(self, 'all_series_data') or not isinstance(self.all_series_data, list):
                self.all_series_data = []

            paged_url = self._updateUrlPage(url, self.series_current_page)

            if paged_url in self.series_pages_downloaded:
                return self.all_series_data

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
                        self.series_total_items = int(js.get("total_items", 0))
                    except (ValueError, TypeError):
                        self.series_total_items = 0
                    current_page_data = js.get("data", [])

                    if not hasattr(self, 'all_series_data') or not isinstance(self.all_series_data, list) or not self.all_series_data:
                        self.all_series_data = [{} for _ in range(self.series_total_items)]

                    self.sort_check = False

                    start_index = (self.series_current_page - 1) * 14

                    for i, item in enumerate(current_page_data):
                        self.all_series_data[start_index + i] = item
                        self.series_pages_downloaded.add(paged_url)

                    return self.all_series_data

            except Exception as e:
                print("Error downloading API data for page {}: {}".format(self.series_current_page, e))
                return self.all_series_data

            self.session.openWithCallback(self.back, MessageBox, _("Server error or invalid link."), MessageBox.TYPE_ERROR, timeout=3)
            return self.all_series_data

    def _updateUrlPage(self, url, page):
        if debugs:
            print("*** _updateUrlPage ***", url, page)

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

    def buildCategories(self):
        if debugs:
            print("*** buildCategories ***")

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

    def buildSeries(self):
        if debugs:
            print("*** buildSeries ***")

        self.main_list = []

        # 0 index, 1 name, 2 series_id, 3 cover, 4 plot, 5 cast, 6 director, 7 genre, 8 releaseDate, 9 rating, 10 last_modified, 11 next_url, 12 tmdb, 13 hidden, 14 year, 15 backdrop, 16 favourite, 17 category_id
        self.main_list = [buildSeriesTitlesList(x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], x[8], x[9], x[10], x[11], x[12], x[13], x[14], x[15], x[16], x[17]) for x in self.list2 if not x[13]]
        self["main_list"].setList(self.main_list)

        self.showVod()

        if self["main_list"].getCurrent():
            self["main_list"].setIndex(glob.nextlist[-1]["index"])

    def buildSeasons(self):
        if debugs:
            print("*** buildSeasons ***")

        self.main_list = []

        # 0 index, 1 name, 2 series_id, 3 cover, 4 plot, 5 cast, 6 director, 7 genre, 8 releaseDate, 9 rating, 10 last_modified, 11 next_url, 12 tmdb, 13 hidden, 14 year, 15 backdrop, 16 favourite, 17 category_id, 18 season_number
        self.main_list = [buildSeriesSeasonsList(x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], x[8], x[9], x[10], x[11], x[12], x[13], x[14], x[15], x[16], x[17], x[18]) for x in self.list3 if not x[13]]
        self["main_list"].setList(self.main_list)

        self.showVod()

        if self["main_list"].getCurrent():
            self["main_list"].setIndex(glob.nextlist[-1]["index"])

    def buildEpisodes(self):
        if debugs:
            print("*** buildEpsiodes ***")

        self.main_list = []

        # 0 index, 1 name, 2 series_id, 3 cover, 4 plot, 5 cast, 6 director, 7 genre, 8 releaseDate, 9 rating, 10 last_modified, 11 next_url, 12 tmdb, 13 hidden, 14 year, 15 backdrop, 16 favourite, 17 category_id, 18 season_number, 19 epsiode_id, 20 cmd
        self.main_list = [buildSeriesEpisodesList(x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], x[8], x[9], x[10], x[11], x[12], x[13], x[14], x[15], x[16], x[17], x[18], x[19], x[20]) for x in self.list4 if not x[13]]
        self["main_list"].setList(self.main_list)

        self.showVod()

        if self["main_list"].getCurrent():
            self["main_list"].setIndex(glob.nextlist[-1]["index"])

    def displaySeriesData(self):
        if debugs:
            print("*** displaySeriesData ***")

        if self["main_list"].getCurrent():
            if self.level != 1:
                self.tmdbValid = True
                self.tmdbfailedcount = 0
                self.getTMDB()

    def selectionChanged(self):
        if debugs:
            print("*** selectionChanged ***")

        self.tmdbresults = ""
        self.tmdbretry = 0

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
                position_all = int(self.series_total_items)
                page_all = (position_all + self.itemsperpage - 1) // self.itemsperpage

            self["page"].setText(_("Page: ") + "{}/{}".format(page, page_all))
            self["listposition"].setText("{}/{}".format(position, position_all))
            self["main_title"].setText("{}: {}".format(self.main_title, channel_title))

            if self.level == 2:
                self.loadDefaultCover()
                self.loadDefaultBackdrop()

                self["vod_cover"].hide()
                self["vod_logo"].hide()
                self["vod_backdrop"].hide()

                if not hasattr(self, 'series_current_page') or page != self.series_current_page:
                    self.series_current_page = page

                    if self["key_blue"].getText() == _("Reset Search"):
                        search_url = "{0}?type=series&action=get_ordered_list&search={1}&genre=*&sortby=number&JsHttpRequest=1-xml".format(self.portal, self.query)
                        response = self.downloadApiData(search_url)
                    else:
                        response = self.downloadApiData(glob.nextlist[-1]["next_url"])
                    self.getSeries(response)

            if self.level == 3:
                self.loadDefaultCover()
                self["vod_cover"].hide()
                self["vod_logo"].hide()

            if self.level != 1:
                self.clearVod()
                self.timerSeries = eTimer()
                try:
                    self.timerSeries.callback.append(self.displaySeriesData)
                except:
                    self.timerSeries_conn = self.timerSeries.timeout.connect(self.displaySeriesData)
                self.timerSeries.start(300, True)

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
            print("**** getTMDB level***", self.level)

        current_item = self["main_list"].getCurrent()

        if current_item:
            if self.level == 2:
                title = current_item[0]
                year = current_item[13]
                tmdb = current_item[14]
                cover = current_item[5]
                backdrop = current_item[15]

                if not year:
                    # Get year from release date
                    try:
                        year = current_item[10][:4]
                    except IndexError:
                        year = ""

                if year:
                    self.storedyear = year
                else:
                    self.storedyear = ""
                if title:
                    self.storedtitle = title
                if cover:
                    self.storedcover = cover
                if backdrop:
                    self.storedbackdrop = backdrop

            else:
                title = self.storedtitle
                year = self.storedyear

                if self.level == 3:
                    tmdb = current_item[15]

                if self.level == 4:
                    tmdb = current_item[14]

            if tmdb and self.tmdbValid and tmdb != "0":
                self.getTMDBDetails(tmdb)
                return

            try:
                os.remove(os.path.join(dir_tmp, "search.txt"))
            except:
                pass

            searchtitle = self.stripjunk(title)
            searchtitle = quote(searchtitle, safe="")

            if self.storedyear:
                searchurl = 'http://api.themoviedb.org/3/search/tv?api_key={}&first_air_date_year={}&query={}'.format(self.check(self.apitoken), self.storedyear, searchtitle)
            else:
                searchurl = 'http://api.themoviedb.org/3/search/tv?api_key={}&query={}'.format(self.check(self.apitoken), searchtitle)

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
            print("*** processTMDB ***")

        resultid = ""
        search_file_path = os.path.join(dir_tmp, "search.txt")
        try:
            with codecs.open(search_file_path, "r", encoding="utf-8") as f:
                response = f.read()

            if response:
                self.searchresult = json.loads(response)
                if "results" in self.searchresult and self.searchresult["results"]:
                    resultid = self.searchresult["results"][0].get("id")
                    self.tmdb2 = resultid

                    if not resultid:
                        self.displayTMDB()
                        return

                    self.getTMDBDetails(resultid)
                else:
                    self.storedyear = ""
                    self.tmdbretry += 1
                    if self.tmdbretry < 2:
                        self.getTMDB()
                    else:
                        self.tmdbretry = 0
                        self.displayTMDB()
                        return

        except Exception as e:
            print("Error processing TMDB response:", e)

    def getTMDBDetails(self, resultid=None):
        if debugs:
            print(" *** getTMDBDetails ***")

        detailsurl = ""

        try:
            os.remove(os.path.join(dir_tmp, "search.txt"))
        except OSError:
            pass

        language = cfg.TMDBLanguage2.value
        languagestr = ""

        if language:
            languagestr = "&language=" + str(language)

        if self.level == 2:
            detailsurl = "http://api.themoviedb.org/3/tv/{}?api_key={}&append_to_response=credits,images,content_ratings{}&include_image_language=en".format(
                resultid, self.check(self.apitoken), languagestr
            )

        elif self.level == 3:
            self.storedseason = self["main_list"].getCurrent()[19]
            detailsurl = "http://api.themoviedb.org/3/tv/{}/season/{}?api_key={}&append_to_response=credits,images,content_ratings{}&include_image_language=en".format(
                resultid, self.storedseason, self.check(self.apitoken), languagestr
            )

        elif self.level == 4:
            self.storedepisode = self["main_list"].getCurrent()[20]
            detailsurl = "http://api.themoviedb.org/3/tv/{}/season/{}/episode/{}?api_key={}&append_to_response=credits,images,content_ratings{}&include_image_language=en".format(
                resultid, self.storedseason, self.storedepisode, self.check(self.apitoken), languagestr
            )

        if pythonVer == 3:
            detailsurl = detailsurl.encode()

        filepath = os.path.join(dir_tmp, "search.txt")

        try:
            downloadPage(detailsurl, filepath, timeout=10).addCallback(self.processTMDBDetails).addErrback(self.failed2)
        except Exception as e:
            print("download TMDB details error:", e)

    def failed2(self, data=None):
        if debugs:
            print("*** failed 2 ***")

        if data:
            print(data)
            if self.level == 2:
                self.tmdbValid = False
                if self.repeatcount == 0:
                    self.getTMDB()
                    self.repeatcount += 1

            else:
                self.displayTMDB()
                return

    def processTMDBDetails(self, result=None):
        if debugs:
            print("*** processTMDBDetails ***")

        self.repeatcount = 0
        response = ""

        self.tmdbresults = {}
        self.tmdbdetails = []
        director = []
        country = []

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
                    if "name" in self.tmdbdetails and self.tmdbdetails["name"]:
                        self.tmdbresults["name"] = str(self.tmdbdetails["name"])

                    if "overview" in self.tmdbdetails and self.tmdbdetails["overview"]:
                        self.tmdbresults["description"] = str(self.tmdbdetails["overview"])

                    if "vote_average" in self.tmdbdetails and self.tmdbdetails["vote_average"]:
                        rating_str = str(self.tmdbdetails["vote_average"])

                        if rating_str not in [None, 0, 0.0, "0", "0.0"]:
                            try:
                                rating = float(rating_str)
                                rounded_rating = round(rating, 1)
                                self.tmdbresults["rating"] = "{:.1f}".format(rounded_rating)
                            except ValueError:
                                self.tmdbresults["rating"] = rating_str
                        else:
                            self.tmdbresults["rating"] = 0

                    if self.level == 2:
                        if "original_name" in self.tmdbdetails and self.tmdbdetails["original_name"]:
                            self.tmdbresults["o_name"] = str(self.tmdbdetails["original_name"])

                        if "episode_run_time" in self.tmdbdetails and self.tmdbdetails["episode_run_time"]:
                            runtime = self.tmdbdetails["episode_run_time"][0]
                        elif "runtime" in self.tmdbdetails:
                            runtime = self.tmdbdetails["runtime"]
                        else:
                            runtime = 0

                        if runtime and runtime != 0:
                            duration_timedelta = timedelta(minutes=runtime)
                            formatted_time = "{:0d}h {:02d}m".format(duration_timedelta.seconds // 3600, (duration_timedelta.seconds % 3600) // 60)
                            self.tmdbresults["duration"] = str(formatted_time)

                        if "first_air_date" in self.tmdbdetails and self.tmdbdetails["first_air_date"]:
                            self.tmdbresults["releaseDate"] = str(self.tmdbdetails["first_air_date"])

                        if "genres" in self.tmdbdetails and self.tmdbdetails["genres"]:
                            genre = []
                            for genreitem in self.tmdbdetails["genres"]:
                                genre.append(str(genreitem["name"]))
                            genre = " / ".join(map(str, genre))
                            self.tmdbresults["genre"] = genre

                        if "origin_country" in self.tmdbdetails and self.tmdbdetails["origin_country"]:
                            try:
                                country = self.tmdbdetails["origin_country"][0]
                                self.tmdbresults["country"] = country
                            except:
                                pass

                        if not country and "production_countries" in self.tmdbdetails and self.tmdbdetails["production_countries"]:
                            country = ", ".join(str(pcountry["name"]) for pcountry in self.tmdbdetails["production_countries"])
                            self.tmdbresults["country"] = country

                    if self.level != 4:
                        if "credits" in self.tmdbdetails:
                            if "cast" in self.tmdbdetails["credits"] and self.tmdbdetails["credits"]["cast"]:
                                cast = []
                                for actor in self.tmdbdetails["credits"]["cast"]:
                                    if "character" in actor and "name" in actor:
                                        cast.append(str(actor["name"]))
                                cast = ", ".join(map(str, cast[:10]))
                                self.tmdbresults["cast"] = cast

                            if "crew" in self.tmdbdetails["credits"] and self.tmdbdetails["credits"]["crew"]:
                                directortext = False
                                for actor in self.tmdbdetails["credits"]["crew"]:
                                    if "job" in actor and actor["job"] == "Director":
                                        director.append(str(actor["name"]))
                                        directortext = True
                                if directortext:
                                    director = ", ".join(map(str, director))
                                    self.tmdbresults["director"] = director

                        if "poster_path" in self.tmdbdetails and self.tmdbdetails["poster_path"]:
                            if screenwidth.width() <= 1280:
                                self.tmdbresults["cover_big"] = "http://image.tmdb.org/t/p/w200" + str(self.tmdbdetails["poster_path"])
                            elif screenwidth.width() <= 1920:
                                self.tmdbresults["cover_big"] = "http://image.tmdb.org/t/p/w300" + str(self.tmdbdetails["poster_path"])
                            else:
                                self.tmdbresults["cover_big"] = "http://image.tmdb.org/t/p/w400" + str(self.tmdbdetails["poster_path"])

                        if "backdrop_path" in self.tmdbdetails and self.tmdbdetails["backdrop_path"]:
                            self.tmdbresults["backdrop_path"] = "http://image.tmdb.org/t/p/w1280" + str(self.tmdbdetails["backdrop_path"])

                        if "images" in self.tmdbdetails and "logos" in self.tmdbdetails["images"]:
                            logos = self.tmdbdetails["images"]["logos"]
                            if logos:
                                logo_path = logos[0].get("file_path")

                                if screenwidth.width() <= 1280:
                                    self.tmdbresults["logo"] = "http://image.tmdb.org/t/p/w300" + str(logo_path)
                                elif screenwidth.width() <= 1920:
                                    self.tmdbresults["logo"] = "http://image.tmdb.org/t/p/w300" + str(logo_path)
                                else:
                                    self.tmdbresults["logo"] = "http://image.tmdb.org/t/p/w500" + str(logo_path)

                        if self.tmdbresults["cover_big"]:
                            self.storedcover = self.tmdbresults["cover_big"]

                        if self.tmdbresults["backdrop_path"]:
                            self.storedbackdrop = self.tmdbresults["backdrop_path"]

                        if self.tmdbresults["logo"]:
                            self.storedlogo = self.tmdbresults["logo"]

                    if self.level != 2:
                        if "air_date" in self.tmdbdetails and self.tmdbdetails["air_date"]:
                            self.tmdbresults["releaseDate"] = str(self.tmdbdetails["air_date"])

                    if self.level == 4:
                        if "run_time" in self.tmdbdetails and self.tmdbdetails["run_time"]:
                            runtime = self.tmdbdetails["run_time"][0]
                        elif "runtime" in self.tmdbdetails:
                            runtime = self.tmdbdetails["runtime"]

                        if runtime and runtime != 0:
                            duration_timedelta = timedelta(minutes=runtime)
                            formatted_time = "{:0d}h {:02d}m".format(duration_timedelta.seconds // 3600, (duration_timedelta.seconds % 3600) // 60)
                            self.tmdbresults["duration"] = str(formatted_time)

                    def get_certification(data, language_code):
                        fallback_codes = ["GB", "US"]

                        # First attempt to find the certification with the specified language code
                        if "content_ratings" in data and "results" in data["content_ratings"]:
                            for result in data["content_ratings"]["results"]:
                                if "iso_3166_1" in result and "rating" in result:
                                    if result["iso_3166_1"] == language_code:
                                        return result["rating"]

                            # If no match found or language_code is blank, try the fallback codes
                            for fallback_code in fallback_codes:
                                for result in data["content_ratings"]["results"]:
                                    if "iso_3166_1" in result and "rating" in result:
                                        if result["iso_3166_1"] == fallback_code:
                                            return result["rating"]

                            # If no match found in fallback codes, return None or an appropriate default value
                        return None

                    language = cfg.TMDBLanguage2.value
                    if not language:
                        language = "en-GB"

                    language = language.split("-")[1]

                    certification = get_certification(self.tmdbdetails, language)

                    if certification:
                        self.tmdbresults["certification"] = str(certification)

                    if "tagline" in self.tmdbdetails and self.tmdbdetails["tagline"].strip():
                        self.tmdbresults["tagline"] = str(self.tmdbdetails["tagline"])

                    self.displayTMDB()

    def displayTMDB(self):
        if debugs:
            print("*** displayTMDB (Series) ***")

        current_item = self["main_list"].getCurrent()
        if not current_item or self.level == 1:
            return

        # Initialize all optional fields
        duration = ""
        genre = ""
        release_date = ""
        director = ""
        country = ""
        cast = ""
        certification = ""
        tagline = ""
        rating = 0
        text = ""
        stream_format = ""

        # Level-specific fields
        if self.level == 4:
            duration = current_item[12]
            try:
                time_obj = datetime.strptime(duration, '%H:%M:%S')
                duration = "{:0d}h {:02d}m".format(time_obj.hour, time_obj.minute)
            except Exception:
                pass
            stream_format = current_item[13]

        # Basic metadata from list
        self["x_title"].setText(current_item[0])
        self["x_description"].setText(current_item[6])
        genre = current_item[9]
        try:
            rating = float(current_item[11])
        except:
            rating = 0
        director = current_item[8]
        cast = current_item[7]
        release_date = current_item[10]
        stream_url = current_item[3]

        if self.level == 4 and stream_url:
            try:
                stream_format = stream_url.split(".")[-1]
            except:
                pass

        # Override with TMDB results if available
        if self.tmdbresults:
            info = self.tmdbresults

            # Titles
            self["x_title"].setText(str(info.get("name") or info.get("o_name") or "").strip())
            self["x_description"].setText(str(info.get("description") or info.get("plot") or "").strip())
            tagline = str(info.get("tagline") or "").strip()
            duration = str(info.get("duration") or duration).strip()
            genre = str(info.get("genre") or genre).strip()
            country = str(info.get("country") or country).strip()
            director = str(info.get("director") or director).strip()
            cast = str(info.get("cast") or info.get("actors") or cast).strip()
            certification = str(info.get("certification") or "").strip().upper()
            if certification:
                certification = _("Rating: ") + certification

            # Rating
            try:
                rating = float(info.get("rating", rating) or rating)
            except:
                rating = 0

        # Rating display
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
            else:
                text = ""

        self["rating_percent"].setText(str(text))
        try:
            rounded_rating = round(rating, 1)
            rating = "{:.1f}".format(rounded_rating)
            if self.tmdbresults:
                self.tmdbresults["rating"] = rating
        except:
            if self.tmdbresults:
                self.tmdbresults["rating"] = str(rating)

        self["rating_text"].setText(str(rating).strip())

        # Facts section
        release_date_str = str(release_date).strip()
        try:
            release_date_str = datetime.strptime(release_date_str, "%Y-%m-%d").strftime("%d-%m-%Y")
        except:
            pass

        facts = self.buildFacts(str(certification), str(release_date_str), str(genre), str(duration), str(stream_format))
        self["facts"].setText(str(facts))

        # UI fields
        self["tagline"].setText(str(tagline).strip())
        self["vod_cast"].setText(str(cast).strip())
        self["vod_director"].setText(str(director).strip())
        self["vod_country"].setText(str(country).strip())

        self["vod_cast_label"].setText(_("Cast:") if cast else "")
        self["vod_director_label"].setText(_("Director:") if director else "")
        self["vod_country_label"].setText(_("Country:") if country else "")
        self["overview"].setText(_("Overview") if self["x_description"].getText() else "")

        # Covers and images
        if (self.level in [2, 3, 4]) and cfg.channelcovers.value:
            self.downloadCover()
            self.downloadBackdrop()
            self.downloadLogo()

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
            elif self.level == 2:
                self["key_menu"].setText("")
                self["key_blue"].setText(_("Search All"))
            else:
                self["key_menu"].setText("")
                self["key_yellow"].setText("")
                self["key_blue"].setText("")

            if self.chosen_category == "favourites":
                self["key_blue"].setText("")
                self["key_menu"].setText("")

    def downloadCover(self):
        """
        if debugs:
            print("*** downloadCover ***")
            """

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
                desc_image = (str(self.tmdbresults.get("cover_big") or "").strip() or str(self.tmdbresults.get("movie_image") or "").strip() or self.storedcover or "")

            if "http" in desc_image:
                self.redirect_count = 0
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
                logo_image = str(self.tmdbresults.get("logo") or "").strip() or self.storedlogo or ""

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

            if self.level == 2 or self.level == 3:
                try:
                    backdrop_image = self["main_list"].getCurrent()[15]
                except:
                    pass

            if self.backdrop_download_deferred and not self.backdrop_download_deferred.called:
                self.backdrop_download_deferred.cancel()

            if self.tmdbresults:
                # Check if "backdrop_path" exists and is not None
                backdrop_path = self.tmdbresults.get("backdrop_path")
                if backdrop_path:
                    backdrop_image = str(backdrop_path[0] if isinstance(backdrop_path, list) else backdrop_path).strip() or self.storedbackdrop or ""
                else:
                    backdrop_image = self.storedbackdrop or ""

            if "http" in backdrop_image:
                self.backdrop_download_deferred = self.agent.request(b'GET', backdrop_image.encode(), Headers({'User-Agent': [b"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"]}))
                self.backdrop_download_deferred.addCallback(self.handleBackdropResponse)
                self.backdrop_download_deferred.addErrback(self.handleBackdropError)
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
            print("*** handleCoverResponse ***")
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
            print("*** handleLogoResponse ***")
            """

        if response.code == 200:
            d = readBody(response)
            d.addCallback(self.handleLogoBody)
            return d

    def handleBackdropResponse(self, response):
        """
        if debugs:
            print("*** handleBackdropResponse ***")
            """

        if response.code == 200:
            d = readBody(response)
            d.addCallback(self.handleBackdropBody)
            return d

    def handleCoverBody(self, body):
        """
        if debugs:
            print("*** handleCoverBody ***")
            """

        temp = os.path.join(dir_tmp, "cover.jpg")
        with open(temp, 'wb') as f:
            f.write(body)
        self.resizeCover(temp)

    def handleLogoBody(self, body):
        """
        if debugs:
            print("***  handleLogoBody ***")
            """
        temp = os.path.join(dir_tmp, "logo.png")
        with open(temp, 'wb') as f:
            f.write(body)
        self.resizeLogo(temp)

    def handleBackdropBody(self, body):
        """
        if debugs:
            print("*** handleBackdropBody ***")
            """
        temp = os.path.join(dir_tmp, "backdrop.jpg")
        with open(temp, 'wb') as f:
            f.write(body)
        self.resizeBackdrop(temp)

    def handleCoverError(self, error):
        """
        if debugs:
            print("*** handleCoverError ***")
            """

        print(error)
        self.loadDefaultCover()

    def handleLogoError(self, error):
        """
        if debugs:
            print("*** handleLogoError ***")
            """

        print(error)
        self.loadDefaultLogo()

    def handleBackdropError(self, error):
        """
        if debugs:
            print("*** handleBackdropError ***")
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

                    bg.save(preview, "PNG")

                    if self["vod_logo"].instance:
                        self["vod_logo"].instance.setPixmapFromFile(preview)
                        self["vod_logo"].show()
                except Exception as e:
                    print("Error resizing logo:", e)
                    self["vod_logo"].hide()

    def resizeBackdrop(self, data=None):
        """
        if debugs:
            print("*** resizeBackdrop ***")
            """

        if not (self["main_list"].getCurrent() and self["vod_backdrop"].instance):
            return

        preview = os.path.join(dir_tmp, "backdrop.jpg")
        if not os.path.isfile(preview):
            return

        try:
            bd_width, bd_height = self["vod_backdrop"].instance.size().width(), self["vod_backdrop"].instance.size().height()
            bd_size = [bd_width, bd_height]

            bg_size = [int(bd_width * 1.5), int(bd_height * 1.5)]

            im = Image.open(preview)
            if im.mode != "RGBA":
                im = im.convert("RGBA")

            try:
                im.thumbnail(bd_size, Image.Resampling.LANCZOS)
            except:
                im.thumbnail(bd_size, Image.ANTIALIAS)

            background = Image.open(os.path.join(self.skin_path, "images/background.png")).convert('RGBA')
            bg = background.crop((bg_size[0] - bd_width, 0, bg_size[0], bd_height))
            bg.save(os.path.join(dir_tmp, "backdrop2.png"), compress_level=0)
            mask = Image.open(os.path.join(skin_directory, "common/mask.png")).convert('RGBA')
            offset = (bg.size[0] - im.size[0], 0)
            bg.paste(im, offset, mask)
            bg.save(os.path.join(dir_tmp, "backdrop.png"), compress_level=0)

            output = os.path.join(dir_tmp, "backdrop.png")

            if self["vod_backdrop"].instance:
                self["vod_backdrop"].instance.setPixmapFromFile(output)
                self["vod_backdrop"].show()

        except Exception as e:
            print("Error resizing backdrop:", e)
            self["vod_backdrop"].hide()

    def DecodeCover(self, PicInfo=None):
        """
        if debugs:
            print("*** DecodeCover ***")
            """

        ptr = self.coverLoad.getData()
        if ptr is not None and self.level != 1:
            self["vod_cover"].instance.setPixmap(ptr)
            self["vod_cover"].show()
        else:
            self["vod_cover"].hide()

    def DecodeLogo(self, PicInfo=None):
        """
        if debugs:
            print("*** DecodeLogo ***")
            """

        ptr = self.logoLoad.getData()
        if ptr is not None and self.level != 2:
            self["vod_logo"].instance.setPixmap(ptr)
            self["vod_logo"].show()
        else:
            self["vod_logo"].hide()

    def DecodeBackdrop(self, PicInfo=None):
        """
        if debugs:
            print("*** DecodeBackdrop ***")
            """

        ptr = self.backdropLoad.getData()
        if ptr is not None and self.level != 2:
            self["vod_backdrop"].instance.setPixmap(ptr)
            self["vod_backdrop"].show()
        else:
            self["vod_backdrop"].hide()

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

            self.series_pages_downloaded = set()
            self.series_current_page = 1
            self.all_series_data = []

            if self["main_list"].getCurrent():
                self["main_list"].setIndex(0)

            glob.nextlist[-1]["index"] = 0

            next_sort_type = next(islice(cycle(sortlist), self.sortindex + 1, None))
            self.sortText = str(next_sort_type)

            self["key_yellow"].setText(self.sortText)
            glob.nextlist[-1]["sort"] = self["key_yellow"].getText()

            self.selectionChanged()

            self.series_current_page = 1

            if self.list2:
                category_id = self.list2[0][17]
                glob.nextlist[-1]["next_url"] = "{0}?type=series&action=get_ordered_list&movie_id=0&season_id=0&episode_id=0&category={1}&fav=0&sortby={2}&hd=0&not_ended=0&p=1&JsHttpRequest=1-xml".format(self.portal, category_id, self.sortby)

                response = self.downloadApiData(glob.nextlist[-1]["next_url"])
                self.getSeries(response)

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
                self.all_series_data = []

                if self["main_list"].getCurrent():
                    self["main_list"].setIndex(0)

                glob.nextlist[-1]["index"] = 0

                self.query = quote_plus(result.encode('utf-8'))

                paged_url = "{0}?type=series&action=get_ordered_list&search={1}&genre=*&sortby=name&JsHttpRequest=1-xml".format(self.portal, self.query)

                response = self.downloadSearchData(paged_url)

                self.getSeries(response)

                if not self.list2:
                    self.searchString = ""
                    self.session.openWithCallback(self.search, MessageBox, _("No results found."), type=MessageBox.TYPE_ERROR, timeout=5)

                else:
                    self["key_blue"].setText(_("Reset Search"))
                    self["key_yellow"].setText("")

            if self.level == 3 and self.list3:
                pass

            if self.level == 4 and self.list4:
                pass

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
        elif self.level == 2:
            self["key_blue"].setText(_("Search All"))
            activelist = glob.originalChannelList2[:]
            self.series_pages_downloaded = set()
            self.series_current_page = 1
            self.all_series_data = []
            self.sort_check = True

            if self["main_list"].getCurrent():
                self["main_list"].setIndex(0)

            glob.nextlist[-1]["index"] = 0

            self.series_current_page = 1
            if self.level == 2:
                category_id = self.list2[0][17]
                glob.nextlist[-1]["next_url"] = "{0}?type=series&action=get_ordered_list&movie_id=0&season_id=0&episode_id=0&category={1}&fav=0&sortby={2}&hd=0&not_ended=0&p=1&JsHttpRequest=1-xml".format(self.portal, category_id, self.sortby)

                response = self.downloadApiData(glob.nextlist[-1]["next_url"])
                self.getSeries(response)

                self.filterresult = ""
                glob.nextlist[-1]["filter"] = self.filterresult

        elif self.level == 3:
            pass

        elif self.level == 4:
            pass

        # self.buildLists()

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
                # self.list2 = []
                if self.list1:
                    category_id = self["main_list"].getCurrent()[3]
                    next_url = "{0}?type=series&action=get_ordered_list&movie_id=0&season_id=0&episode_id=0&category={1}&fav=0&sortby={2}&hd=0&not_ended=0&p=1&JsHttpRequest=1-xml".format(self.portal, category_id, self.sortby)
                    self.chosen_category = ""

                    if self.showfav:
                        self.chosen_category = "favourites"

                    self.level += 1
                    self["main_list"].setIndex(0)
                    self["category_actions"].setEnabled(False)
                    self["channel_actions"].setEnabled(True)
                    # self["key_yellow"].setText(_("Sort: A-Z"))
                    # self.sortText = _("Sort: A-Z")

                    glob.nextlist.append({"next_url": next_url, "index": 0, "level": self.level, "sort": self["key_yellow"].getText(), "filter": ""})

                    self.createSetup()
                else:
                    self.createSetup()

            elif self.level == 2:
                if self.list2:
                    self.title2 = self["main_list"].getCurrent()[0]
                    self.cover2 = self["main_list"].getCurrent()[5]
                    self.plot2 = self["main_list"].getCurrent()[6]
                    self.cast2 = self["main_list"].getCurrent()[7]
                    self.director2 = self["main_list"].getCurrent()[8]
                    self.genre2 = self["main_list"].getCurrent()[9]
                    self.releaseDate2 = self["main_list"].getCurrent()[10]
                    self.rating2 = self["main_list"].getCurrent()[11]
                    self.backdrop_path2 = self["main_list"].getCurrent()[15]

                    if self["main_list"].getCurrent()[14] and self["main_list"].getCurrent()[14] != "0":
                        self.tmdb2 = self["main_list"].getCurrent()[14]
                    else:
                        self.tmdb2 = ""

                    series_id = self["main_list"].getCurrent()[4]
                    next_url = "{0}?type=series&action=get_ordered_list&movie_id={1}&season_id=0&episode_id=0&JsHttpRequest=1-xml".format(self.portal, series_id)

                    self.level += 1

                    self["main_list"].setIndex(0)
                    self["category_actions"].setEnabled(False)
                    self["channel_actions"].setEnabled(True)
                    # self["key_yellow"].setText(_("Sort: A-Z"))
                    # self.sortText = _("Sort: A-Z")

                    glob.nextlist.append({"next_url": next_url, "index": 0, "level": self.level, "sort": self["key_yellow"].getText(), "filter": ""})

                    self.createSetup()
                else:
                    self.createSetup()

            elif self.level == 3:
                if self.list3:
                    movie_id = str(self["main_list"].getCurrent()[4]).partition(":")[0]
                    self.storedseasonid = str(self["main_list"].getCurrent()[4])

                    next_url = "{0}?type=series&action=get_ordered_list&movie_id={1}&season_id=0&episode_id=0&JsHttpRequest=1-xml".format(self.portal, movie_id)

                    self.level += 1
                    self["main_list"].setIndex(0)
                    self["category_actions"].setEnabled(False)
                    self["channel_actions"].setEnabled(True)
                    glob.nextlist.append({"next_url": next_url, "index": 0, "level": self.level, "sort": self["key_yellow"].getText(), "filter": ""})
                    self.createSetup()
                else:
                    self.createSetup()

            elif self.level == 4:
                if self.list4:
                    from . import vodplayer

                    stream_id = self["main_list"].getCurrent()[4]
                    streamtype = glob.active_playlist["player_info"]["vodtype"]
                    command = self["main_list"].getCurrent()[21]
                    episode_id = self["main_list"].getCurrent()[20]
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

        if self.level != 1:
            try:
                self.timerSeries.stop()
            except:
                pass

            if self.cover_download_deferred:
                self.cover_download_deferred.cancel()

            if self.logo_download_deferred:
                self.logo_download_deferred.cancel()

            if self.backdrop_download_deferred:
                self.backdrop_download_deferred.cancel()

        try:
            del glob.nextlist[-1]
        except Exception as e:
            print(e)
            self.close()

        if self.level == 3:
            self.series_info = ""

        if not glob.nextlist:
            self.close()
        else:
            self["x_title"].setText("")
            self["x_description"].setText("")
            self["key_epg"].setText("")
            self.level -= 1
            if self.level == 1:
                self["category_actions"].setEnabled(True)
                self["channel_actions"].setEnabled(False)
                self.showfav = False
                self.chosen_category = ""

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
                self.session.openWithCallback(self.createSetup, hidden.EStalker_HiddenCategories, "series", current_list, self.level)

    def clearWatched(self):
        if debugs:
            print("*** clearWatched ***")

        if self.level != 4:
            return

        current_id = str(self["main_list"].getCurrent()[4])
        watched_list = glob.active_playlist["player_info"].get("serieswatched", [])
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
            json.dump(self.playlists_all, f, indent=4)

        self.buildLists()

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

        if self.chosen_category == "favourites" and not self.level == 2:
            return

        current_index = self["main_list"].getIndex()
        favExists = False
        favStream_id = ""

        if self.level == 2:
            series_id = str(self["main_list"].getCurrent()[4])
            current_index = self["main_list"].getIndex()

        try:
            self.list2[current_index][16] = not self.list2[current_index][16]
        except:
            pass

        for fav in glob.active_playlist["player_info"]["seriesfavourites"]:
            if str(series_id) == str(fav["id"]):
                favExists = True
                favStream_id = str(fav["id"])
                break

        if favExists:
            if self.level == 2:
                glob.active_playlist["player_info"]["seriesfavourites"] = [x for x in glob.active_playlist["player_info"]["seriesfavourites"] if str(x["id"]) != str(favStream_id)]
        else:
            newfavourite = {
                "name": self.list2[current_index][1],
                "id": self.list2[current_index][2],
                "cover": self.list2[current_index][3],
                "plot": self.list2[current_index][4],
                "cast": self.list2[current_index][5],
                "director": self.list2[current_index][6],
                "genre": self.list2[current_index][7],
                "releaseDate": self.list2[current_index][8],
                "rating": self.list2[current_index][9],
                "last_modified": self.list2[current_index][10],
                "year": self.list2[current_index][14],
                "backdrop": self.list2[current_index][15],
                "cateogry_id": self.list2[current_index][17]
            }

            glob.active_playlist["player_info"]["seriesfavourites"].insert(0, newfavourite)

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
        # self["vod_cover"].hide()
        # self["vod_logo"].hide()
        # self["vod_backdrop"].hide()
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

    def check(self, token):
        """
        if debugs:
            print("*** check ***", token)
            """

        result = base64.b64decode(token)
        result = zlib.decompress(base64.b64decode(result))
        result = base64.b64decode(result).decode()
        return result

    # code for natural sorting of numbers in string
    def atoi(self, text):
        return int(text) if text.isdigit() else text

    def natural_keys(self, text):
        return [self.atoi(c) for c in re.split(r"(\d+)", text[1])]

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


def buildCategoryList(index, title, category_id, hidden):
    png = LoadPixmap(os.path.join(common_path, "more.png"))
    return (title, png, index, category_id, hidden)


def buildSeriesTitlesList(index, title, series_id, cover, plot, cast, director, genre, releaseDate, rating, lastmodified, next_url, tmdb, hidden, year, backdrop_path, favourite, category_id):
    png = LoadPixmap(os.path.join(common_path, "more.png"))
    if favourite:
        png = LoadPixmap(os.path.join(common_path, "favourite.png"))
    return (title, png, index, next_url, series_id, cover, plot, cast, director, genre, releaseDate, rating, lastmodified, year, tmdb, backdrop_path, hidden, favourite, category_id)


def buildSeriesSeasonsList(index, title, series_id, cover, plot, cast, director, genre, releaseDate, rating, lastmodified, next_url, tmdb, hidden, year, backdrop_path, favourite, category_id, season_number):
    png = LoadPixmap(os.path.join(common_path, "more.png"))
    return (title, png, index, next_url, series_id, cover, plot, cast, director, genre, releaseDate, rating, lastmodified, year, tmdb, backdrop_path, hidden, favourite, category_id, season_number)


def buildSeriesEpisodesList(index, title, series_id, cover, plot, cast, director, genre, releaseDate, rating, lastmodified, next_url, tmdb, hidden, year, backdrop_path, favourite, category_id, season_number, episode_id, cmd):
    png = LoadPixmap(os.path.join(common_path, "play.png"))
    return (title, png, index, next_url, series_id, cover, plot, cast, director, genre, releaseDate, rating, lastmodified, year, tmdb, backdrop_path, hidden, favourite, category_id, season_number, episode_id, cmd)
