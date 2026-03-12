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
import tempfile
import hashlib
import unicodedata

try:
    from http.client import HTTPConnection
    HTTPConnection.debuglevel = 0
except ImportError:
    from httplib import HTTPConnection
    HTTPConnection.debuglevel = 0

try:
    from urllib import quote, quote_plus
except ImportError:
    from urllib.parse import quote, quote_plus

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

try:
    from twisted.web.client import BrowserLikePolicyForHTTPS
    contextFactory = BrowserLikePolicyForHTTPS()
except ImportError:
    from twisted.web.client import WebClientContextFactory
    contextFactory = WebClientContextFactory()

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
from .plugin import (cfg, common_path, dir_tmp, pythonVer, screenwidth, skin_directory, debugs, isDreambox, isVTI)
from .eStaticText import StaticText
from .utils import get_local_timezone, make_request,  perform_handshake, get_profile_data


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

        self.playlists_json = cfg.playlists_json.value

        self.setup_title = _("Vod Categories")

        self.main_title = _("Movies")
        self["main_title"] = StaticText(self.main_title)

        self.group_title = ""

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

        self.sortindex = 0
        self.sortText = _("Sort: A-Z")
        self.do_sort = False

        self.level = 1

        self.showfav = False
        self.firstlist = True

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

        self.retry = False

        self.apitoken = "ZUp6enk4cko4ZzBKTlBMTFNxN3djd25MOHEzeU5Zak1Bdkd6S3lPTmdqSjhxeUxMSTBNOFRhUGNBMjBCVmxBTzlBPT0K"

        next_url = ""
        self.sortby = "number"

        self._vod_req_id = 0

        self._tmp_cover = None
        self._tmp_logo = None
        self._tmp_backdrop = None
        self._tmp_backdrop_src = None
        self._tmp_backdrop_out = None

        self._mask2 = None
        self._mask2_alpha = None
        self._mask2_cache = OrderedDict()
        self._mask2_cache_max = 5
        self._mask2_size = None
        self._backdrop_target_size = None

        try:
            mask_path = os.path.join(skin_directory, "common/mask2.png")
            if os.path.exists(mask_path):
                self._mask2 = Image.open(mask_path)
                self._mask2.load()  # Force load the image data
                self._mask2_size = self._mask2.size

                # Always create a reliable L alpha mask once:
                try:
                    if self._mask2.mode in ("RGBA", "LA"):
                        # For RGBA/LA, extract the alpha channel
                        if hasattr(self._mask2, 'split'):
                            bands = self._mask2.split()
                            if bands:
                                self._mask2_alpha = bands[-1]
                            else:
                                raise ValueError("split() returned empty")
                        else:
                            # Old PIL without proper split
                            self._mask2_alpha = self._mask2.convert("L")
                    else:
                        # Greyscale (or RGB etc) -> treat brightness as alpha
                        self._mask2_alpha = self._mask2.convert("L")
                except Exception as e:
                    print("Error extracting alpha, using greyscale fallback:", e)
                    self._mask2_alpha = self._mask2.convert("L")

        except Exception as e:
            print("Error loading mask2:", e)
            self._mask2 = None
            self._mask2_alpha = None
            self._mask2_size = None

        # tmdb image sizes (set once)
        self._tmdb_coversize = "w200"
        self._tmdb_backdropsize = "w1280"
        self._tmdb_logosize = "w200"
        self._cover_target_size = None
        self._logo_target_size = None

        try:
            width = screenwidth.width()

            if width <= 1280:
                self._tmdb_coversize = "w200"
                self._tmdb_backdropsize = "w1280"
                self._tmdb_logosize = "w300"

            elif width <= 1920:
                self._tmdb_coversize = "w300"
                self._tmdb_backdropsize = "w1280"
                self._tmdb_logosize = "w300"

            else:
                self._tmdb_coversize = "w400"
                self._tmdb_backdropsize = "w1280"
                self._tmdb_logosize = "w500"
        except:
            pass

        self._px_play = LoadPixmap(os.path.join(common_path, "play.png"))
        self._px_play2 = LoadPixmap(os.path.join(common_path, "play2.png"))
        self._px_fav = LoadPixmap(os.path.join(common_path, "favourite.png"))
        self._px_watched = LoadPixmap(os.path.join(common_path, "watched.png"))
        self._px_more = LoadPixmap(os.path.join(common_path, "more.png"))

        # Precompiled regex (stripjunk)
        self._re_has_ascii = re.compile(r'[\x00-\x7F]')
        self._re_has_non_ascii = re.compile(r'[^\x00-\x7F]')

        self._re_remove_non_ascii = re.compile(r'[^\x00-\x7F]+')

        self._re_end_the = re.compile(r'\s*the$', re.IGNORECASE)
        self._re_prefix_xx_colon = re.compile(r'^\w{2}:', re.IGNORECASE)
        self._re_prefix_xx_pipe_xx = re.compile(r'^\w{2}\|\w{2}\s', re.IGNORECASE)

        self._re_leading_doublepipes = re.compile(r'^\|\|.*?\|\|')
        self._re_leading_singlepipe_block = re.compile(r'^\|.*?\|')
        self._re_any_pipe_block = re.compile(r'\|.*?\|')

        self._re_leading_doublebars = re.compile(r'^┃┃.*?┃┃')
        self._re_leading_singlebar_block = re.compile(r'^┃.*?┃')
        self._re_any_bar_block = re.compile(r'┃.*?┃')

        self._re_parens = re.compile(r'\(\(.*?\)\)|\([^()]*\)')
        self._re_brackets = re.compile(r'\[\[.*?\]\]|\[.*?\]')

        self._re_is_year_only = re.compile(r'^\d{4}$')
        self._re_trailing_year = re.compile(r'[\s\-]*(?:[\(\[\"]?\d{4}[\)\]\"]?)$')

        self._re_lang_dash_prefix = re.compile(r'^[A-Za-z0-9\-]{1,7}\s*-\s*', re.IGNORECASE)

        # Bad substrings
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
        self._re_bad_strings = re.compile('|'.join(map(re.escape, bad_strings)), re.IGNORECASE)

        # Bad suffixes
        bad_suffix = [
            " al", " ar", " ba", " da", " de", " en", " es", " eu", " ex-yu", " fi", " fr", " gr", " hr", " mk",
            " nl", " no", " pl", " pt", " ro", " rs", " ru", " si", " swe", " sw", " tr", " uk", " yu"
        ]
        self._re_bad_suffix = re.compile(r'(' + '|'.join(map(re.escape, bad_suffix)) + r')$', re.IGNORECASE)

        self._re_dots_underscores = re.compile(r"[._'\*]")

        self.adult_keywords = set([
            "adult", "+18", "18+", "18 rated", "xxx", "sex", "porn",
            "voksen", "volwassen", "aikuinen", "Erwachsene", "dorosly",
            "взрослый", "vuxen", "£дорослий"
        ])

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

        self.timerVod = eTimer()
        try:
            self.timerVod.callback.append(self.downloadVodInfo)
        except:
            self.timerVod_conn = self.timerVod.timeout.connect(self.downloadVodInfo)

        self.onFirstExecBegin.append(self.createSetup)
        self.onLayoutFinish.append(self.__layoutFinished)

    def __layoutFinished(self):
        self.setTitle(self.setup_title)

        # cache cover target size
        try:
            if self["vod_cover"].instance:
                self._cover_target_size = (
                    self["vod_cover"].instance.size().width(),
                    self["vod_cover"].instance.size().height()
                )
        except:
            self._cover_target_size = None

        # cache logo target size
        try:
            if self["vod_logo"].instance:
                self._logo_target_size = (
                    self["vod_logo"].instance.size().width(),
                    self["vod_logo"].instance.size().height()
                )
        except:
            self._logo_target_size = None

        # cache backdrop target size (your existing code)
        try:
            if self["vod_backdrop"].instance:
                self._backdrop_target_size = (
                    self["vod_backdrop"].instance.size().width(),
                    self["vod_backdrop"].instance.size().height()
                )
        except:
            self._backdrop_target_size = None

        if not self._backdrop_target_size and self._mask2_size:
            self._backdrop_target_size = self._mask2_size

    def _stopTimerVod(self):
        # Stop any scheduled timer fire
        try:
            if self.timerVod:
                self.timerVod.stop()
        except:
            pass

        # Invalidate any in-flight downloadPage callbacks (zap protection)
        try:
            self._vod_req_id += 1
        except:
            self._vod_req_id = 1

    def _new_tmp_file(self, prefix, suffix):
        fd = None
        path = None

        try:
            fd, path = tempfile.mkstemp(prefix=prefix, suffix=suffix, dir=dir_tmp)
        except:
            fd, path = tempfile.mkstemp(prefix=prefix, suffix=suffix)

        try:
            os.close(fd)
        except:
            pass

        return path

    def _safe_unlink(self, path):
        try:
            if path and os.path.exists(path):
                os.remove(path)
        except:
            pass

    def _cleanup_vod_assets(self):
        self._safe_unlink(self._tmp_cover)
        self._safe_unlink(self._tmp_logo)
        self._safe_unlink(self._tmp_backdrop_src)
        self._safe_unlink(self._tmp_backdrop_out)

        self._tmp_cover = None
        self._tmp_logo = None
        self._tmp_backdrop_src = None
        self._tmp_backdrop_out = None

        if self.cover_download_deferred:
            try:
                self.cover_download_deferred.cancel()
            except:
                pass
            self.cover_download_deferred = None

        if self.logo_download_deferred:
            try:
                self.logo_download_deferred.cancel()
            except:
                pass
            self.logo_download_deferred = None

        if self.backdrop_download_deferred:
            try:
                self.backdrop_download_deferred.cancel()
            except:
                pass
            self.backdrop_download_deferred = None

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
            self.getVodCategoryStreams(response)

    def buildLists(self):
        if debugs:
            print("*** buildLists ***")

        if self.level == 1:
            self.buildCategories()
        else:
            self.buildVod()

        if self.do_sort:
            self.do_sort = False
            self.applyPreviousSort()

        else:
            self.resetButtons()
            self.selectionChanged()

    def getCategories(self):
        if debugs:
            print("*** getCategories **")

        index = 0
        self.list1 = []

        self["key_epg"].setText("")

        currentPlaylist = glob.active_playlist
        currentCategoryList = currentPlaylist.get("data", {}).get("vod_categories", {}).get("js", [])
        currentHidden = set(currentPlaylist.get("player_info", {}).get("vodhidden", []))

        hidden = "0" in currentHidden

        for index, item in enumerate(currentCategoryList):
            if not isinstance(item, dict):
                continue

            category_name = item.get("title", "No category")
            category_id = item.get("id", "999999")
            hidden = category_id in currentHidden
            self.list1.append([index, str(category_name), str(category_id), hidden])

        glob.originalChannelList1 = self.list1[:]
        self.buildLists()

    def getVodCategoryStreams(self, response):
        if debugs:
            print("*** getVodCategoryStreams ***")

        # added tmdb plugin instead of imdb for dreamos
        if TMDB_installed:
            self["key_epg"].setText("TMDB")
        else:
            self["key_epg"].setText("IMDB")
        # response = ""

        if self.chosen_category == "favourites":
            response = glob.active_playlist["player_info"].get("vodfavourites", [])

        self.list2 = []

        if response:
            for index, channel in enumerate(response):
                if not isinstance(channel, dict) or not channel:
                    self.list2.append([index, "", "", "", "", "", "", False, "", "", False, "", "", "", "", "", "", "", ""])
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

                added = str(channel.get("added", "0"))
                category_id = str(channel.get("category_id", ""))
                container_extension = "mp4"
                rating = str(channel.get("rating", ""))
                year = str(channel.get("year", "")).strip()

                if year == "":
                    pattern = r'\b\d{4}\b'
                    matches = re.findall(pattern, name)
                    if matches:
                        year = str(matches[-1])

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
                    str(cmd),
                    "",
                    "",
                    "",
                    "",
                    ""
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

    def buildCategories(self):
        if debugs:
            print("*** buildCategories ***")

        self.hideVod()

        if self.list1:
            self.main_list = [
                buildCategoryList(x[0], x[1], x[2], x[3], self._px_more)
                for x in self.list1 if not x[3]
            ]

            self["main_list"].setList(self.main_list)

            if self["main_list"].getCurrent():
                self["main_list"].setIndex(glob.nextlist[-1]["index"])

    def buildVod(self):
        if debugs:
            print("*** buildVod ***")

        watched_set = set(str(x) for x in glob.active_playlist["player_info"].get("vodwatched", []))

        if self.chosen_category == "favourites":
            filtered_list = [x for x in self.list2 if x[7]]
        else:
            filtered_list = [x for x in self.list2 if not x[10]]

        self.main_list = [
            buildVodStreamList(
                x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], x[8], x[9], x[10], x[11], x[12], x[13], x[14],
                watched_set, self._px_play, self._px_play2, self._px_fav, self._px_watched
            )
            for x in filtered_list
        ]

        self["main_list"].setList(self.main_list)

        if self["main_list"].getCurrent():
            # self.showVod()
            self["main_list"].setIndex(glob.nextlist[-1]["index"])

    def downloadVodInfo(self):
        if debugs:
            print("*** downloadVodInfo ***")

        self._cleanup_vod_assets()
        self.clearVod()

        if self["main_list"].getCurrent():
            self.tmdbresults = {}
            self.getTMDB()

    def selectionChanged(self):
        if debugs:
            print("*** selectionChanged ***")

        self.tmdbresults = {}

        current_item = self["main_list"].getCurrent()

        if current_item:
            channel_title = current_item[0]
            current_index = self["main_list"].getIndex()
            glob.currentchannellistindex = current_index
            glob.nextlist[-1]["index"] = current_index

            position = current_index + 1
            position_all = len(self.main_list)
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

            if self.level == 2:
                self._stopTimerVod()
                self.timerVod.start(300, True)

                if not hasattr(self, 'current_page') or page != self.current_page:
                    self.current_page = page

                    if self["key_blue"].getText() == _("Reset Search"):
                        search_url = "{0}?type=vod&action=get_ordered_list&search={1}&genre=*&sortby=number&JsHttpRequest=1-xml".format(self.portal, self.query)
                        response = self.downloadApiData(search_url)
                    else:
                        response = self.downloadApiData(glob.nextlist[-1]["next_url"])
                    self.getVodCategoryStreams(response)

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

    def applyPreviousSort(self):
        if debugs:
            print("*** applyPreviousSort ***")

        if self.level == 1:
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
                activelist.sort(key=lambda x: x[0], reverse=False)

            # Always move "All" category to first position if present
            for i, item in enumerate(activelist):
                if item[1].lower() == _("all").lower():
                    activelist.insert(0, activelist.pop(i))
                    break

            self.list1 = activelist
            self.buildLists()

        elif self.level == 2:
            sortlist = [_("Sort: A-Z"), _("Sort: Added"),  _("Sort: Original")]

            prev_sort = sortlist[0]
            for index, item in enumerate(sortlist):
                if str(item) == str(self.sortText):
                    prev_sort = sortlist[index - 1]
                    break

            # Determine sort type for VOD
            if prev_sort == _("Sort: A-Z"):
                self.sortby = "name"
            elif prev_sort == _("Sort: Added"):
                self.sortby = "added"
            elif prev_sort == _("Sort: Original"):
                self.sortby = "number"

            # Reset pagination and data
            self.pages_downloaded = set()
            self.current_page = 1
            self.all_data = []

            # Reset UI indexes
            if self["main_list"].getCurrent():
                self["main_list"].setIndex(0)

            glob.nextlist[-1]["index"] = 0
            glob.nextlist[-1]["sort"] = self["key_yellow"].getText()

            # Trigger reload of VOD list
            self.selectionChanged()
            self.current_page = 1

            if self.list2:
                glob.nextlist[-1]["next_url"] = ("{0}?type=vod&action=get_ordered_list&category={1}&sortby={2}&p=1&JsHttpRequest=1-xml").format(self.portal, self.current_category, self.sortby)

                response = self.downloadApiData(glob.nextlist[-1]["next_url"])
                self.getVodCategoryStreams(response)

        # Keep previous selection if possible
        if self["main_list"].getCurrent() and glob.nextlist[-1]["index"] != 0:
            self["main_list"].setIndex(glob.nextlist[-1]["index"])

    def normalize_text(self, text):

        has_ascii = bool(self._re_has_ascii.search(text))
        has_non_ascii = bool(self._re_has_non_ascii.search(text))

        if has_ascii and has_non_ascii:

            if pythonVer == 2:
                if isinstance(text, str):
                    text = text.decode("utf-8", "ignore")

                text = unicodedata.normalize("NFKD", text).encode("ascii", "ignore")

            else:
                text = unicodedata.normalize("NFKD", text).encode("ascii", "ignore").decode("ascii")

        return text

    def stripjunk(self, text, database=None):
        searchtitle = text

        # Move "the" from the end to the beginning (case-insensitive)
        if self._re_end_the.search(searchtitle.strip().lower()):
            searchtitle = "The " + searchtitle[:-3].strip()

        # remove xx: at start (case-insensitive)
        searchtitle = self._re_prefix_xx_colon.sub('', searchtitle)

        # remove xx|xx at start (case-insensitive)
        searchtitle = self._re_prefix_xx_pipe_xx.sub('', searchtitle)

        # remove all leading content between and including || or |
        searchtitle = self._re_leading_doublepipes.sub('', searchtitle)
        searchtitle = self._re_leading_singlepipe_block.sub('', searchtitle)
        searchtitle = self._re_any_pipe_block.sub('', searchtitle)

        # remove all leading content between and including ┃┃ or ┃
        searchtitle = self._re_leading_doublebars.sub('', searchtitle)
        searchtitle = self._re_leading_singlebar_block.sub('', searchtitle)
        searchtitle = self._re_any_bar_block.sub('', searchtitle)

        # remove all content between and including () unless it's all digits
        searchtitle = self._re_parens.sub('', searchtitle)

        # remove all content between and including []
        searchtitle = self._re_brackets.sub('', searchtitle)

        # remove trailing year (but not if the whole title *is* a year)
        if not self._re_is_year_only.match(searchtitle.strip()):
            searchtitle = self._re_trailing_year.sub('', searchtitle)

        # remove up to 6 characters followed by space and dash at start (e.g. "EN -", "BE-NL -")
        searchtitle = self._re_lang_dash_prefix.sub('', searchtitle)

        # normalise text
        searchtitle = self.normalize_text(searchtitle)

        # Bad substrings to strip (case-insensitive)
        searchtitle = self._re_bad_strings.sub('', searchtitle)

        # Bad suffixes to remove (case-insensitive, only if at end)
        searchtitle = self._re_bad_suffix.sub('', searchtitle)

        # Replace '.', '_', "'", '*' with space
        searchtitle = self._re_dots_underscores.sub(' ', searchtitle)

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

            searchtitle = self.stripjunk(title, "TMDB")
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

        """
        if data:
            print(data)
            """

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
        # self.resultid = resultid
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
        self.tmdbresults = {}

        try:
            with codecs.open(os.path.join(dir_tmp, "search.txt"), "r", encoding="utf-8") as f:
                response = f.read()
        except Exception as e:
            print("Error reading TMDB response:", e)
            return

        if not response:
            return

        try:
            self.tmdbdetails = json.loads(response, object_pairs_hook=OrderedDict)
        except Exception as e:
            print("Error parsing TMDB response:", e)
            return

        if not self.tmdbdetails:
            return

        title = self.tmdbdetails.get("title", "")
        if title:
            self.tmdbresults["name"] = str(title).strip()

        original_title = self.tmdbdetails.get("original_title", "")
        if original_title:
            self.tmdbresults["o_name"] = str(original_title).strip()

        runtime = self.tmdbdetails.get("runtime")
        if runtime and runtime != 0:
            try:
                self.tmdbresults["originalduration"] = runtime
                duration_timedelta = timedelta(minutes=runtime)
                formatted_time = "{:0d}h {:02d}m".format(
                    duration_timedelta.seconds // 3600,
                    (duration_timedelta.seconds % 3600) // 60
                )
                self.tmdbresults["duration"] = formatted_time
            except (TypeError, ValueError) as e:
                print("Error processing runtime:", e)

        country = None
        origin_country = self.tmdbdetails.get("origin_country")
        if origin_country:
            try:
                country = origin_country[0]
                self.tmdbresults["country"] = country
            except (IndexError, TypeError):
                pass

        if not country:
            production_countries = self.tmdbdetails.get("production_countries")
            if production_countries:
                try:
                    country = ", ".join(str(pc["name"]) for pc in production_countries)
                    self.tmdbresults["country"] = country
                except (KeyError, TypeError):
                    pass

        release_date = self.tmdbdetails.get("release_date")
        if release_date:
            self.tmdbresults["releaseDate"] = str(release_date).strip()

        # Handle images - single lookups
        poster_path = self.tmdbdetails.get("poster_path", "")
        backdrop_path = self.tmdbdetails.get("backdrop_path", "")

        logo_path = ""
        images = self.tmdbdetails.get("images")
        if images:
            logos = images.get("logos")
            if logos:
                logo_path = logos[0].get("file_path", "")

        # Build image URLs only if paths exist
        if poster_path:
            self.tmdbresults["cover_big"] = "http://image.tmdb.org/t/p/{}/{}".format(
                self._tmdb_coversize, poster_path
            )

        if backdrop_path:
            self.tmdbresults["backdrop_path"] = "http://image.tmdb.org/t/p/{}/{}".format(
                self._tmdb_backdropsize, backdrop_path
            )

        if logo_path:
            self.tmdbresults["logo"] = "http://image.tmdb.org/t/p/{}/{}".format(
                self._tmdb_logosize, logo_path
            )

        overview = self.tmdbdetails.get("overview")
        if overview:
            self.tmdbresults["description"] = str(overview).strip()

        tagline = self.tmdbdetails.get("tagline")
        if tagline:
            self.tmdbresults["tagline"] = str(tagline).strip()

        # Handle rating
        vote_average = self.tmdbdetails.get("vote_average")
        if vote_average not in (None, 0, 0.0, "0", "0.0"):
            try:
                rating = float(vote_average)
                self.tmdbresults["rating"] = "{:.1f}".format(round(rating, 1))
            except (ValueError, TypeError) as e:
                print("*** rating error ***", e)
                self.tmdbresults["rating"] = "0.0"
        else:
            self.tmdbresults["rating"] = "0.0"

        # Handle genres
        genres = self.tmdbdetails.get("genres")
        if genres:
            try:
                genre = " / ".join(str(g["name"]) for g in genres[:4])
                self.tmdbresults["genre"] = genre
            except (KeyError, TypeError):
                pass

        # Handle credits
        credits = self.tmdbdetails.get("credits")
        if credits:
            cast_list = credits.get("cast")
            if cast_list:
                try:
                    cast = ", ".join(actor["name"] for actor in cast_list[:10])
                    self.tmdbresults["cast"] = cast
                except (KeyError, TypeError):
                    pass

            crew_list = credits.get("crew")
            if crew_list:
                try:
                    directors = [
                        actor["name"] for actor in crew_list
                        if actor.get("job") == "Director"
                    ]
                    if directors:
                        self.tmdbresults["director"] = ", ".join(directors)
                except (KeyError, TypeError):
                    pass

        # Handle videos (trailers) - only for Python 3
        if pythonVer == 3:
            videos = self.tmdbdetails.get("videos")

            if videos:
                results = videos.get("results")
                if results:
                    current_index = self["main_list"].getIndex()

                    selected_video = None

                    # 1. Prefer official YouTube Trailer
                    for video in results:
                        if video.get("site") == "YouTube" and video.get("type") == "Trailer" and video.get("official") is True and video.get("key"):
                            selected_video = video
                            break

                    # 2. Fallback to any YouTube Trailer
                    if selected_video is None:
                        for video in results:
                            if video.get("site") == "YouTube" and video.get("type") == "Trailer" and video.get("key"):
                                selected_video = video
                                break

                    # 3. Fallback to official Teaser
                    if selected_video is None:
                        for video in results:
                            if video.get("site") == "YouTube" and video.get("type") == "Teaser" and video.get("official") is True and video.get("key"):
                                selected_video = video
                                break

                    if selected_video is not None:
                        try:
                            self.list2[current_index][12] = str(selected_video["key"])
                            self.buildVod()
                        except (IndexError, KeyError):
                            pass

        # Handle certification
        def get_certification(data, language_code):
            fallback_codes = ["GB", "US"]

            release_dates = data.get("release_dates")
            if not release_dates:
                return None

            results = release_dates.get("results")
            if not results:
                return None

            # Try specified language code first
            if language_code:
                for release in results:
                    if release.get("iso_3166_1") == language_code:
                        release_dates_list = release.get("release_dates")
                        if release_dates_list:
                            return release_dates_list[0].get("certification")

            # Try fallback codes
            for fallback_code in fallback_codes:
                for release in results:
                    if release.get("iso_3166_1") == fallback_code:
                        release_dates_list = release.get("release_dates")
                        if release_dates_list:
                            cert = release_dates_list[0].get("certification")
                            if cert:  # Only return if not empty
                                return cert

            return None

        # Get language and certification
        language = cfg.TMDBLanguage2.value or "en-GB"
        language_code = language.split("-")[-1]  # Get country code

        certification = get_certification(self.tmdbdetails, language_code)
        if certification:
            self.tmdbresults["certification"] = str(certification)

        """
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
                """

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
                try:
                    facts = self.buildFacts(str(certification), str(release_date), str(genre), str(duration), str(stream_format))
                    self["facts"].setText(str(facts))
                except Exception as e:
                    print(e)

                if self.level == 2 and cfg.channelcovers.value:
                    self.downloadBackdrop()
                    self.downloadCover()
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
            else:
                self["key_menu"].setText("")
                self["key_blue"].setText(_("Search All"))

            if self.chosen_category == "favourites":
                self["key_blue"].setText("")
                self["key_menu"].setText("")

    def stopStream(self):
        if debugs:
            print("*** stopStream ***")

        if glob.currentPlayingServiceRefString != glob.newPlayingServiceRefString:
            if glob.newPlayingServiceRefString != "":
                if self.session.nav.getCurrentlyPlayingServiceReference():
                    self.session.nav.stopService()
                self.session.nav.playService(eServiceReference(glob.currentPlayingServiceRefString))
                glob.newPlayingServiceRefString = glob.currentPlayingServiceRefString

    def downloadCover(self):
        if debugs:
            print("*** downloadCover ***")

        if cfg.channelcovers.value is False:
            return

        if not self["main_list"].getCurrent():
            return

        self._safe_unlink(self._tmp_cover)
        self._tmp_cover = None

        desc_image = ""

        if self.tmdbresults:
            desc_image = str(self.tmdbresults.get("cover_big") or "").strip()

        if not (desc_image and "http" in desc_image):
            self.loadDefaultCover()
            return

        req_id = self._vod_req_id
        # self.redirect_count = 0

        if self.cover_download_deferred and not self.cover_download_deferred.called:
            self.cover_download_deferred.cancel()

        self.cover_download_deferred = self.agent.request(
            b'GET',
            desc_image.encode(),
            Headers({'User-Agent': [b"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/145.0.0.0 Safari/537.36"]})
        )

        self.cover_download_deferred.addCallback(self.coverResponse, req_id)
        self.cover_download_deferred.addErrback(self.coverError, req_id)

    def downloadCoverFromUrl(self, url):
        if debugs:
            print("*** downloadCoverFromUrl ***")

        req_id = self._vod_req_id

        self.cover_download_deferred = self.agent.request(
            b'GET',
            url.encode(),
            Headers({'User-Agent': [b"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/145.0.0.0 Safari/537.36"]})
        )
        self.cover_download_deferred.addCallback(self.coverFromUrlResponse, req_id)
        self.cover_download_deferred.addErrback(self.coverError, req_id)

    def coverResponse(self, response, req_id):
        if debugs:
            print("*** coverresponse ***")

        if req_id != self._vod_req_id:
            return

        if response.code == 200:
            d = readBody(response)
            d.addCallback(self.coverBody, req_id)
            return d

        elif response.code in (301, 302):
            location = response.headers.getRawHeaders('location')[0]
            self.downloadCoverFromUrl(location)
        else:
            self.coverError("HTTP error code: %s" % response.code)

    def coverFromUrlResponse(self, response, req_id):
        if req_id != self._vod_req_id:
            return

        if response.code == 200:
            d = readBody(response)
            d.addCallback(self.coverBody, req_id)
            return d

        self.coverError("HTTP error code: %s" % response.code)

    def coverBody(self, body, req_id):
        if debugs:
            print("*** coverbody ***")

        if req_id != self._vod_req_id:
            return

        temp = self._new_tmp_file("xst_vod_cover_", ".jpg")
        self._tmp_cover = temp

        try:
            with open(temp, 'wb') as f:
                f.write(body)
        except:
            self._safe_unlink(temp)
            self._tmp_cover = None
            self.loadDefaultCover()
            return

        self.resizeCover(temp)

    def coverError(self, error, req_id=None):
        if debugs:
            print("*** handle error ***")

        print(error)
        self.loadDefaultCover()

    def loadDefaultCover(self, data=None):
        if debugs:
            print("*** loadDefaultCover ***")

        if self["vod_cover"].instance:
            self["vod_cover"].instance.setPixmapFromFile(os.path.join(skin_directory, "common/blank.png"))

    def resizeCover(self, preview):
        if debugs:
            print("*** resizeCover ***")

        if not (self["main_list"].getCurrent() and self["vod_cover"].instance):
            self._safe_unlink(preview)
            return

        if not os.path.isfile(preview):
            return

        try:
            if self._cover_target_size:
                width, height = self._cover_target_size
            else:
                width = self["vod_cover"].instance.size().width()
                height = self["vod_cover"].instance.size().height()

            self.coverLoad.setPara([width, height, 1, 1, 0, 1, "FF000000"])
            self.coverLoad.startDecode(preview)
        except:
            self._safe_unlink(preview)

    def DecodeCover(self, PicInfo=None):
        if debugs:
            print("*** decodecover ***")

        ptr = self.coverLoad.getData()
        if ptr is not None and self.level == 2:
            self["vod_cover"].instance.setPixmap(ptr)
            self["vod_cover"].show()
        else:
            self["vod_cover"].hide()

        self._safe_unlink(self._tmp_cover)
        self._tmp_cover = None

    def downloadLogo(self):
        if debugs:
            print("*** downloadLogo ***")

        if cfg.channelcovers.value is False:
            return

        if not self["main_list"].getCurrent():
            return

        self._safe_unlink(self._tmp_logo)
        self._tmp_logo = None

        logo_image = ""

        if self.tmdbresults:  # tmbdb
            logo_image = str(self.tmdbresults.get("logo") or "").strip()

        if not (logo_image and "http" in logo_image):
            self.loadDefaultLogo()
            return

        req_id = self._vod_req_id

        if self.logo_download_deferred and not self.logo_download_deferred.called:
            self.logo_download_deferred.cancel()

        self.logo_download_deferred = self.agent.request(
            b'GET',
            logo_image.encode(),
            Headers({'User-Agent': [b"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/145.0.0.0 Safari/537.36"]})
        )
        self.logo_download_deferred.addCallback(self.logoResponse, req_id)
        self.logo_download_deferred.addErrback(self.logoError, req_id)

    def logoResponse(self, response, req_id):
        if debugs:
            print("*** logoresponse ***")

        if req_id != self._vod_req_id:
            return

        if response.code == 200:
            d = readBody(response)
            d.addCallback(self.logoBody, req_id)
            return d

    def logoBody(self, body, req_id):
        if debugs:
            print("*** logobody ***")

        if req_id != self._vod_req_id:
            return

        temp = self._new_tmp_file("xst_vod_logo_", ".png")
        self._tmp_logo = temp

        try:
            with open(temp, 'wb') as f:
                f.write(body)
        except:
            self._safe_unlink(temp)
            self._tmp_logo = None
            self.loadDefaultLogo()
            return

        self.resizeLogo(temp)

    def logoError(self, error, req_id=None):
        if debugs:
            print("*** handle error ***")

        print(error)
        self.loadDefaultLogo()

    def loadDefaultLogo(self, data=None):
        if debugs:
            print("*** loadDefaultLogo ***")

        if self["vod_logo"].instance:
            self["vod_logo"].instance.setPixmapFromFile(os.path.join(skin_directory, "common/blank.png"))

    def resizeLogo(self, preview):
        if debugs:
            print("*** resizeLogo ***")

        if not (self["main_list"].getCurrent() and self["vod_logo"].instance):
            self._safe_unlink(preview)
            return

        if self._logo_target_size:
            size = self._logo_target_size
        else:
            size = (
                self["vod_logo"].instance.size().width(),
                self["vod_logo"].instance.size().height()
            )

        try:
            im = Image.open(preview)

            if im.mode != "RGBA":
                im = im.convert("RGBA")

            # Only thumbnail if image is bigger than target
            if im.size[0] > size[0] or im.size[1] > size[1]:
                try:
                    im.thumbnail(size, Image.Resampling.LANCZOS)
                except:
                    im.thumbnail(size, Image.ANTIALIAS)

            bg = Image.new("RGBA", size, (255, 255, 255, 0))

            # right-aligned logo (same as your original)
            left = size[0] - im.size[0]
            top = 0

            bg.paste(im, (left, top), mask=im)

            bg.save(preview, "PNG", compress_level=0)

            self["vod_logo"].instance.setPixmapFromFile(preview)
            self["vod_logo"].show()

        except Exception as e:
            print("Error resizing logo:", e)
            self["vod_logo"].hide()

        # cleanup tempfile
        self._safe_unlink(preview)
        self._tmp_logo = None

    def downloadBackdrop(self):
        if debugs:
            print("*** downloadBackdrop ***")

        if cfg.channelcovers.value is False:
            return

        if not self["main_list"].getCurrent():
            return

        self._safe_unlink(self._tmp_backdrop_src)
        self._tmp_backdrop_src = None

        backdrop_image = ""

        if self.tmdbresults:  # tmbdb
            backdrop_image = str(self.tmdbresults.get("backdrop_path") or "").strip()

        if not (backdrop_image and "http" in backdrop_image):
            self.loadDefaultBackdrop()
            return

        req_id = self._vod_req_id

        if self.backdrop_download_deferred and not self.backdrop_download_deferred.called:
            self.backdrop_download_deferred.cancel()

        self.backdrop_download_deferred = self.agent.request(
            b'GET',
            backdrop_image.encode(),
            Headers({'User-Agent': [b"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/145.0.0.0 Safari/537.36"]})
        )

        self.backdrop_download_deferred.addCallback(self.backdropResponse, req_id)
        self.backdrop_download_deferred.addErrback(self.backdropError, req_id)

    def backdropResponse(self, response, req_id):
        if debugs:
            print("*** backdropresponse ***")

        if req_id != self._vod_req_id:
            return

        if response.code == 200:
            d = readBody(response)
            d.addCallback(self.backdropBody, req_id)
            return d

    def backdropBody(self, body, req_id):
        if debugs:
            print("*** backdropbody ***")

        if req_id != self._vod_req_id:
            return

        temp = self._new_tmp_file("xst_vod_backdrop_", ".jpg")
        self._tmp_backdrop_src = temp

        try:
            with open(temp, 'wb') as f:
                f.write(body)
        except:
            self._safe_unlink(temp)
            self._tmp_backdrop_src = None
            self.loadDefaultBackdrop()
            return

        self.resizeBackdrop(temp)

    def backdropError(self, error, req_id=None):
        if debugs:
            print("*** handle error ***")

        print(error)
        self.loadDefaultBackdrop()

    def loadDefaultBackdrop(self, data=None):
        if debugs:
            print("*** loadDefaultBackdrop ***")

        if self["vod_backdrop"].instance:
            self["vod_backdrop"].instance.setPixmapFromFile(os.path.join(skin_directory, "common/blank.png"))

    def resizeBackdrop(self, preview):
        if debugs:
            print("*** resizeBackdrop ***")

        if not (self["main_list"].getCurrent() and self["vod_backdrop"].instance):
            self._safe_unlink(preview)
            return

        try:
            if not self._mask2_alpha or not self._mask2_size:
                self.loadDefaultBackdrop()
                self._safe_unlink(preview)
                return

            bd_size = self._mask2_size
            bd_width, bd_height = bd_size

            im = Image.open(preview)
            if im.mode != "RGBA":
                im = im.convert("RGBA")

            try:
                resample = Image.Resampling.LANCZOS
            except:
                resample = Image.ANTIALIAS

            # Fit inside mask size (no crop)
            if im.size != bd_size:
                im.thumbnail(bd_size, resample)

            im_w, im_h = im.size
            x_offset = (bd_width - im_w) // 2
            y_offset = 0

            # paste() mask must match im.size
            key = "%dx%d" % (im_w, im_h)
            if key in self._mask2_cache:
                alpha = self._mask2_cache[key]
            else:
                alpha = self._mask2_alpha
                if alpha.size != im.size:
                    alpha = alpha.resize(im.size, resample)

                self._mask2_cache[key] = alpha

                try:
                    while len(self._mask2_cache) > self._mask2_cache_max:
                        self._mask2_cache.popitem(last=False)
                except Exception as e:
                    print(e)

            background = Image.new("RGBA", bd_size, (0, 0, 0, 0))
            background.paste(im, (x_offset, y_offset), alpha)

            output = self._new_tmp_file("xst_vod_backdrop_out_", ".png")
            self._tmp_backdrop_out = output

            background.save(output, "PNG", compress_level=0)
            self["vod_backdrop"].instance.setPixmapFromFile(output)
            self["vod_backdrop"].show()

        except Exception as e:
            print("Error resizing backdrop:", e)
            self["vod_backdrop"].hide()

        self._safe_unlink(preview)
        self._safe_unlink(self._tmp_backdrop_out)
        self._tmp_backdrop_src = None
        self._tmp_backdrop_out = None

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

            for i, item in enumerate(activelist):
                if item[1].lower() == "all":
                    activelist.insert(0, activelist.pop(i))
                    break

            self.buildLists()

        if self.level == 2:

            sortlist = [_("Sort: A-Z"), _("Sort: Added"), _("Sort: Original")]

            for index, item in enumerate(sortlist):
                if str(item) == str(self.sortText):
                    self.sortindex = index
                    break

            if current_sort == _("Sort: A-Z"):
                self.sortby = "name"
            elif current_sort == _("Sort: Added"):
                self.sortby = "added"
            elif current_sort == _("Sort: Original"):
                self.sortby = "number"

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
                # category_id = self.list2[0][13]
                glob.nextlist[-1]["next_url"] = "{0}?type=vod&action=get_ordered_list&category={1}&sortby={2}&p=1&JsHttpRequest=1-xml".format(self.portal, self.current_category, self.sortby)
                response = self.downloadApiData(glob.nextlist[-1]["next_url"])
                self.getVodCategoryStreams(response)

    def search(self, result=None):
        if debugs:
            print("*** search ***")

        if not self["key_blue"].getText():
            return

        current_filter = self["key_blue"].getText()

        if current_filter != _("Reset Search"):
            self.session.openWithCallback(self.filterChannels, VirtualKeyBoard, title=_("Filter this category..."), text=getattr(self, "searchString", "") or "")
        else:
            self.resetSearch()

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
                    self.hideVod()
                    self.buildLists()

            if self.level == 2 and self.list2:
                self.all_data = []

                if self["main_list"].getCurrent():
                    self["main_list"].setIndex(0)

                glob.nextlist[-1]["index"] = 0

                self.query = quote_plus(result.encode('utf-8'))

                paged_url = "{0}?type=vod&action=get_ordered_list&search={1}&genre=*&sortby=name&JsHttpRequest=1-xml".format(self.portal, self.query)

                response = self.downloadApiData(paged_url)

                self.getVodCategoryStreams(response)

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

        if self["main_list"].getCurrent():
            current_index = self["main_list"].getIndex()
            glob.nextlist[-1]["index"] = current_index
            glob.currentchannellist = self.main_list[:]
            glob.currentchannellistindex = current_index

            if self.level == 1:
                if self.list1:
                    category_id = self["main_list"].getCurrent()[3]
                    self.group_title = self["main_list"].getCurrent()[0]
                    self.sortby = "number"
                    self.current_category = category_id

                    next_url = "{0}?type=vod&action=get_ordered_list&category={1}&sortby={2}&p=1&JsHttpRequest=1-xml".format(self.portal, category_id, self.sortby)

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

                    streamtype = glob.active_playlist["player_info"]["vodtype"]
                    stream_id = self["main_list"].getCurrent()[4]
                    command = self["main_list"].getCurrent()[14]
                    next_url = command

                    if debugs:
                        print("*** original command **", command)

                    if str(command).startswith("/media/"):
                        pre_vod_url = (str(self.portal) + "?type=vod&action=get_ordered_list&movie_id={}&category=1&sortby=&p=1&JsHttpRequest=1-xml").format(stream_id)

                        pre_response = make_request(pre_vod_url, method="GET", headers=self.headers, params=None, response_type="json")

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
                        if ("localhost" in command or "///" in command or "/ch/" in command or "http" not in command):
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
        if self["main_list"].getCurrent():
            self["main_list"].setIndex(glob.currentchannellistindex)

    def back(self, data=None):
        if debugs:
            print("*** back ***")

        self.showfav = False
        self.chosen_category = ""
        if self.level == 2:
            self.group_title = ""
            self._stopTimerVod()
            self._cleanup_vod_assets()

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
            current_list = self.list1 if self.level == 1 else self.list2
            if self.level == 1 or (self.level == 2 and self.chosen_category != "favourites"):
                self.do_sort = True
                self.session.openWithCallback(self.setIndex, hidden.EStalker_HiddenCategories, "vod", current_list, self.level)

    def clearWatched(self):
        if debugs:
            print("*** clearWatched ***")

        if self.level == 2:
            current_id = str(self["main_list"].getCurrent()[4])
            watched_list = glob.active_playlist["player_info"].get("vodwatched", [])
            if current_id in watched_list:
                watched_list.remove(current_id)
            else:
                watched_list.append(current_id)

        with open(self.playlists_json, "r") as f:
            try:
                self.playlists_all = json.load(f)
            except:
                os.remove(self.playlists_json)
                return

            for i, playlist in enumerate(self.playlists_all):
                playlist_info = playlist.get("playlist_info", {})
                current_playlist_info = glob.active_playlist.get("playlist_info", {})
                if (playlist_info.get("domain") == current_playlist_info.get("domain") and
                        playlist_info.get("mac") == current_playlist_info.get("mac")):
                    self.playlists_all[i] = glob.active_playlist
                    break

        with open(self.playlists_json, "w") as f:
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

    def hideVod(self):
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
        self["vod_cover"].hide()
        self["vod_logo"].hide()
        self["vod_backdrop"].hide()
        # self["main_title"].setText("")
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
        if self["main_list"].getCurrent():
            self["vod_cover"].show()
            self["vod_logo"].show()
            self["vod_backdrop"].show()

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

            yt = YouTube("https://www.youtube.com/watch?v=" + str(trailer_id))

            streaming_data = yt.vid_info.get("streamingData", {})
            formats = streaming_data.get("formats", [])

            if not formats:
                self.session.open(
                    MessageBox,
                    _("No compatible trailer found."),
                    type=MessageBox.TYPE_INFO,
                    timeout=5
                )
                return

            # choose largest progressive
            best = max(
                formats,
                key=lambda f: int(f.get("height", 0)),
                default=None
            )

            if not best:
                return

            stream_url = best.get("url")

            if not stream_url:
                return

            self.trailer_next(stream_url, yt.title)

        except Exception as e:
            print("Trailer error:", e)

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
            self.session.openWithCallback(
                self.trailer_cleanup,
                vodplayer.EStalker_VodPlayer,
                str(next_url),
                str(streamtype),
                None
            )

    def trailer_cleanup(self, *args):
        if debugs:
            print("*** trailer_cleanup ***")

        self.setIndex()


def check_and_install_ffmpeg():
    try:
        subprocess.run(
            ["ffmpeg", "-version"],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )
        return True
    except (subprocess.CalledProcessError, FileNotFoundError):
        print("FFmpeg is not installed. Installing...")

    # Check if opkg exists to determine the package manager
    if os.path.exists("/etc/opkg/"):
        return install_ffmpeg_opkg()
    else:
        return install_ffmpeg_apt()


def install_ffmpeg_opkg():
    try:
        subprocess.run(["opkg", "update"], check=True)
        subprocess.run(["opkg", "install", "ffmpeg"], check=True)
        print("FFmpeg installed successfully.")
        return True
    except subprocess.CalledProcessError as e:
        print("Failed to install FFmpeg using opkg:", e)
        return False


def install_ffmpeg_apt():
    try:
        subprocess.run(["apt-get", "update"], check=True)
        subprocess.run(["apt-get", "-y", "install", "ffmpeg"], check=True)
        print("FFmpeg installed successfully.")
        return True
    except subprocess.CalledProcessError as e:
        print("Failed to install FFmpeg using apt-get:", e)
        return False


def get_python_site_packages():
    try:
        python_dirs = sorted(
            [d for d in os.listdir("/usr/lib/") if d.startswith("python")],
            reverse=True
        )
        for py_dir in python_dirs:
            site_packages = os.path.join("/usr/lib", py_dir, "site-packages")
            if os.path.exists(site_packages):
                return site_packages
    except Exception as e:
        print("Error finding site-packages:", e)

    return None


def compare_versions(version1, version2):
    try:
        v1_parts = [int(x) for x in version1.split('.')]
        v2_parts = [int(x) for x in version2.split('.')]

        # Pad shorter version with zeros
        max_len = max(len(v1_parts), len(v2_parts))
        v1_parts.extend([0] * (max_len - len(v1_parts)))
        v2_parts.extend([0] * (max_len - len(v2_parts)))

        for v1, v2 in zip(v1_parts, v2_parts):
            if v1 > v2:
                return 1
            elif v1 < v2:
                return -1
        return 0
    except Exception as e:
        print("Error comparing versions:", e)
        return 0


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
    except ImportError:
        return None
    except Exception as e:
        print("Error checking pytubefix version:", e)
        return None


def check_and_install_pytubefix():
    # Maximum supported version
    MAX_VERSION = "9.3.0"
    MAX_VERSION_URL = "https://files.pythonhosted.org/packages/a6/8a/2611bd7297e4b3ee1973c4d78e79f5a416cfebe89d4783f7da6f45c6b5d4/pytubefix-9.3.0.tar.gz"

    site_packages = get_python_site_packages()
    if not site_packages:
        print("Could not find site-packages directory")
        return False

    pytubefix_path = os.path.join(site_packages, "pytubefix")

    # Check if pytubefix is already installed
    if os.path.exists(pytubefix_path) and os.listdir(pytubefix_path):
        installed_version = check_pytubefix_version()

        if installed_version:
            version_comparison = compare_versions(installed_version, MAX_VERSION)

            if version_comparison == 0:
                # Exact version match
                print("pytubefix version {} is already installed".format(installed_version))
                return True
            elif version_comparison > 0:
                # Newer version installed - need to downgrade
                print("pytubefix version {} is newer than maximum supported version {}. Downgrading...".format(
                    installed_version, MAX_VERSION
                ))
                try:
                    shutil.rmtree(pytubefix_path)
                    print("Removed newer version {}".format(installed_version))
                except Exception as e:
                    print("Failed to remove newer version:", e)
                    return False
            else:
                # Older version installed - upgrade to max version
                print("pytubefix version {} is older than maximum supported version {}. Upgrading...".format(
                    installed_version, MAX_VERSION
                ))
                try:
                    shutil.rmtree(pytubefix_path)
                    print("Removed older version {}".format(installed_version))
                except Exception as e:
                    print("Failed to remove older version:", e)
                    return False

    # Ensure temporary directory exists
    if not os.path.exists(dir_tmp):
        try:
            os.makedirs(dir_tmp)
            print("Created temporary directory:", dir_tmp)
        except Exception as e:
            print("Failed to create temporary directory:", e)
            return False

    # Download pytubefix
    print("Downloading pytubefix version {}...".format(MAX_VERSION))
    try:
        response = requests.get(MAX_VERSION_URL, timeout=30)
        response.raise_for_status()
    except Exception as e:
        print("Failed to download pytubefix tarball:", e)
        return False

    tarball_path = os.path.join(dir_tmp, "pytubefix-{}.tar.gz".format(MAX_VERSION))

    try:
        with open(tarball_path, "wb") as f:
            f.write(response.content)
        print("Tarball downloaded successfully at", tarball_path)
    except Exception as e:
        print("Failed to save tarball:", e)
        return False

    # Extract tarball
    try:
        import tarfile
        with tarfile.open(tarball_path, "r:gz") as tar:
            tar.extractall(path=dir_tmp)
        print("Tarball extracted successfully")
    except Exception as e:
        print("Failed to extract tarball:", e)
        # Cleanup
        try:
            os.remove(tarball_path)
        except:
            pass
        return False

    # Copy pytubefix to site-packages
    extracted_path = os.path.join(dir_tmp, "pytubefix-{}".format(MAX_VERSION), "pytubefix")

    if not os.path.exists(extracted_path):
        print("Failed to find pytubefix folder at", extracted_path)
        # Cleanup
        try:
            os.remove(tarball_path)
            extracted_root = os.path.join(dir_tmp, "pytubefix-{}".format(MAX_VERSION))
            if os.path.exists(extracted_root):
                shutil.rmtree(extracted_root)
        except:
            pass
        return False

    print("pytubefix folder found at", extracted_path, ". Copying it to", pytubefix_path)

    try:
        # Remove existing installation if present
        if os.path.exists(pytubefix_path):
            shutil.rmtree(pytubefix_path)

        # Copy new version
        shutil.copytree(extracted_path, pytubefix_path)
        print("pytubefix {} installed successfully at {}".format(MAX_VERSION, pytubefix_path))

        # Cleanup temporary files
        try:
            if os.path.exists(tarball_path):
                os.remove(tarball_path)
            extracted_root = os.path.join(dir_tmp, "pytubefix-{}".format(MAX_VERSION))
            if os.path.exists(extracted_root):
                shutil.rmtree(extracted_root)
            print("Cleaned up temporary files")
        except Exception as e:
            print("Cleanup warning:", e)

        return True

    except Exception as e:
        print("Failed to copy pytubefix:", e)
        # Cleanup
        try:
            if os.path.exists(tarball_path):
                os.remove(tarball_path)
            extracted_root = os.path.join(dir_tmp, "pytubefix-{}".format(MAX_VERSION))
            if os.path.exists(extracted_root):
                shutil.rmtree(extracted_root)
        except:
            pass
        return False


def buildCategoryList(index, title, category_id, hidden, px_more=None):
    return (title, px_more, index, category_id, hidden)


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


def buildVodStreamList(
    index, title, stream_id, cover, added, rating, next_url, favourite, container_extension, year, hidden, tmdb, trailer, category_id, cmd, watched_set,
    px_play=None, px_play2=None, px_fav=None, px_watched=None
):
    is_watched = False
    try:
        is_watched = str(stream_id) in watched_set
    except Exception:
        is_watched = False

    png = px_play

    if trailer and pythonVer == 3:
        png = px_play2

    if favourite:
        png = px_fav

    if is_watched:
        png = px_watched

    return (title, png, index, next_url, stream_id, cover, added, rating, container_extension, year, hidden, tmdb, trailer, category_id, cmd)
