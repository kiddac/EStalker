#!/usr/bin/python
# -*- coding: utf-8 -*-

# Standard library imports
import os
import json
import hashlib

try:
    from http.client import HTTPConnection
    HTTPConnection.debuglevel = 0
except:
    from httplib import HTTPConnection
    HTTPConnection.debuglevel = 0

# Enigma2 components
from Components.ActionMap import ActionMap
from Components.Pixmap import Pixmap
from Components.Sources.List import List
from enigma import eTimer
from Screens.MessageBox import MessageBox
from Screens.Screen import Screen
from Tools.LoadPixmap import LoadPixmap

# Local application/library-specific imports
from . import _
from . import estalker_globals as glob
from .plugin import skin_directory, common_path, version, cfg, debugs, pythonVer, dir_tmp
from .eStaticText import StaticText
from .utils import get_local_timezone, make_request, reauthorize_portal

try:
    from urllib import quote
except ImportError:
    from urllib.parse import quote


if pythonVer == 3:
    superscript_to_normal = str.maketrans(
        '⁰¹²³⁴⁵⁶⁷⁸⁹ᵃᵇᶜᵈᵉᶠᵍʰⁱʲᵏˡᵐⁿᵒᵖʳˢᵗᵘᵛʷˣʸᶻ'
        'ᴬᴮᴰᴱᴳᴴᴵᴶᴷᴸᴹᴺᴼᴾᴿᵀᵁⱽᵂ⁺⁻⁼⁽⁾',
        '0123456789abcdefghijklmnoprstuvwxyz'
        'ABDEGHIJKLMNOPRTUVW+-=()'
    )


SUPPORTED_MODULES = {
    "tv",
    "vclub",
    "sclub",
    "audioclub",
    "tv_archive",
}


def normalize_superscripts(text):
    return text.translate(superscript_to_normal)


def clean_names(response):
    found_superscript = False

    if not isinstance(response, dict):
        glob.hassuperscript = False
        return response

    if "js" in response and isinstance(response["js"], list):
        for item in response["js"]:
            if "title" in item and isinstance(item["title"], str):
                original = item["title"]
                converted = normalize_superscripts(original)

                if converted != original:
                    found_superscript = True

                item["title"] = converted

    glob.hassuperscript = found_superscript
    return response


class EStalker_Menu(Screen):
    ALLOW_SUSPEND = True

    def __init__(self, session):
        Screen.__init__(self, session)
        self.session = session

        skin_path = os.path.join(skin_directory, cfg.skin.value)
        skin = os.path.join(skin_path, "menu.xml")

        with open(skin, "r") as f:
            self.skin = f.read()

        self.list = []
        self.drawList = []
        self["list"] = List(self.drawList, enableWrapAround=True)

        self.playlists_json = cfg.playlists_json.value
        self.setup_title = _("Playlist Menu")

        self["key_red"] = StaticText(_("Back"))
        self["key_green"] = StaticText(_("OK"))
        self["key_blue"] = StaticText("")
        self["version"] = StaticText()

        self["splash"] = Pixmap()
        self["splash"].show()

        self["actions"] = ActionMap(["EStalkerActions"], {
            "red": self.quit,
            "cancel": self.quit,
            "menu": self.settings,
            "green": self.__next__,
            "ok": self.__next__,
        }, -2)

        self["version"].setText(version)

        portal = glob.active_playlist["playlist_info"].get("portal", None)

        self.retry = False

        self.live_categories_url = portal + "?type=itv&action=get_genres&sortby=number&JsHttpRequest=1-xml"
        self.vod_categories_url = portal + "?type=vod&action=get_categories&sortby=number&JsHttpRequest=1-xml"
        self.series_categories_url = portal + "?type=series&action=get_categories&sortby=number&JsHttpRequest=1-xml"
        self.modules_url = portal + "?type=stb&action=get_modules&JsHttpRequest=1-xml"

        glob.active_playlist["data"]["live_streams"] = {}
        glob.active_playlist["data"]["data_downloaded"] = False

        allchannels_path = os.path.join(dir_tmp, "allchannels.json")
        if os.path.exists(allchannels_path):
            os.remove(allchannels_path)

        self.onFirstExecBegin.append(self.start)
        self.onLayoutFinish.append(self.__layoutFinished)

    def __layoutFinished(self):
        self.setTitle(self.setup_title)

    def start(self, data=None):
        if debugs:
            print("*** start ***")

        if glob.active_playlist["data"]["data_downloaded"] is False:
            self.timer = eTimer()
            try:
                self.timer_conn = self.timer.timeout.connect(self.makeUrlList)
            except:
                try:
                    self.timer.callback.append(self.makeUrlList)
                except:
                    self.makeUrlList()
            self.timer.start(10, True)
        else:
            self["splash"].hide()
            self.createSetup()

    def makeUrlList(self):
        if debugs:
            print("*** makeUrlList ***")

        self.url_list = [
            [self.live_categories_url, 0],
            [self.vod_categories_url, 1],
            [self.series_categories_url, 2],
            [self.modules_url, 4]
        ]

        self.process_downloads()

    def download_url(self, url):
        if debugs:
            print("*** download_url ***", url)

        timezone = get_local_timezone()
        token = glob.active_playlist["playlist_info"]["token"]
        token_random = glob.active_playlist["playlist_info"]["token_random"]
        domain = str(glob.active_playlist["playlist_info"].get("domain", ""))
        port = glob.active_playlist["playlist_info"].get("port", "")
        host = str(glob.active_playlist["playlist_info"].get("host", "")).rstrip("/")
        mac = glob.active_playlist["playlist_info"].get("mac", "").upper()
        portal = glob.active_playlist["playlist_info"].get("portal", None)
        portal_version = glob.active_playlist["playlist_info"].get("version", "5.3.1")
        path_prefix = glob.active_playlist["playlist_info"].get("path_prefix", "")

        referer = host + path_prefix + "index.html"

        sn = hashlib.md5(mac.encode()).hexdigest().upper()[:13]
        adid = hashlib.md5((sn + mac).encode()).hexdigest()

        encoded_mac = quote(mac, safe="")
        encoded_timezone = quote(timezone, safe="")

        # Prefer the authenticated headers discovered from xpcom.common.js
        # and saved by the playlist validation screen.
        saved_headers = glob.active_playlist["playlist_info"].get("headers", {})
        headers = saved_headers.copy() if isinstance(saved_headers, dict) else {}

        # Preserve compatibility with JSON created before headers were saved.
        if not headers:
            cookie = "mac={}; stb_lang=en; timezone={}".format(
                encoded_mac,
                encoded_timezone
            )
            if portal and "/stalker_portal/" in portal:
                cookie += "; adid={}".format(adid)

            headers = {
                "Pragma": "no-cache",
                "Accept-Language": "en-US,en;q=0.5",
                "Accept-Encoding": "gzip, deflate",
                "Host": "{}:{}".format(domain, port) if port else domain,
                "User-Agent": (
                    "Mozilla/5.0 (QtEmbedded; U; Linux; C) "
                    "AppleWebKit/533.3 (KHTML, like Gecko) "
                    "MAG200 stbapp ver: 2 rev: 250 Safari/533.3"
                ),
                "X-User-Agent": "Model: MAG250; Link: WiFi",
                "Connection": "Close",
                "Referer": referer,
                "Cookie": cookie,
            }

        # Always use the current token in case this screen was reopened after
        # reauthorisation.
        headers["Authorization"] = "Bearer " + token

        self.timezone = timezone
        self.token = token
        self.token_random = token_random
        self.domain = domain
        self.port = port
        self.host = host
        self.mac = mac
        self.portal = portal
        self.portal_version = portal_version
        self.path_prefix = path_prefix
        self.referer = referer
        self.sn = sn
        self.adid = adid
        self.headers = headers.copy()

        category = url[1]

        response = make_request(url[0], method="GET", headers=headers, params=None, response_type="json")

        """
        if debugs and category == 4:
            print("*** modules ***", response)
            """

        if pythonVer == 3 and category in (0, 1, 2):
            response = clean_names(response)

        return category, response

    def process_downloads(self):
        if debugs:
            print("*** process_downloads2 ***")

        max_retries = 1
        retries = 0
        success = False
        pending_urls = list(self.url_list)

        glob.active_playlist["data"]["live_categories"] = {}
        glob.active_playlist["data"]["vod_categories"] = {}
        glob.active_playlist["data"]["series_categories"] = {}
        glob.active_playlist["data"]["available_modules"] = []

        for url in self.url_list:
            if url[1] == 3:
                glob.active_playlist["data"]["live_streams"] = {}
                break

        while pending_urls and retries <= max_retries:
            if retries > 0:
                if debugs:
                    print("Retry attempt:", retries)

                self.reauthorize()

            results = []

            for url in pending_urls:
                try:
                    result = self.download_url(url)
                    results.append(result)

                except Exception as e:
                    category = url[1]

                    print(
                        "Category download error:",
                        category,
                        type(e).__name__,
                        str(e)
                    )

                    results.append((category, None))

            responses = {}

            for category, response in results:
                responses[category] = response

                if not response:
                    continue

                if category != 4:
                    success = True

                if category == 0:
                    glob.active_playlist["data"][
                        "live_categories"
                    ] = response

                elif category == 1:
                    glob.active_playlist["data"][
                        "vod_categories"
                    ] = response

                elif category == 2:
                    glob.active_playlist["data"][
                        "series_categories"
                    ] = response

                elif category == 3:
                    glob.active_playlist["data"][
                        "live_streams"
                    ] = response

                elif category == 4:
                    module_data = response.get("js", response) if isinstance(response, dict) else {}
                    if isinstance(module_data, dict):
                        all_modules = module_data.get("all_modules") or []
                        disabled_modules = set(module_data.get("disabled_modules") or [])
                        glob.active_playlist["data"]["available_modules"] = [
                            name for name in all_modules
                            if name in SUPPORTED_MODULES
                            and name not in disabled_modules
                        ]

            failed_urls = []

            for url in pending_urls:
                category = url[1]
                response = responses.get(category)

                # Module discovery is optional. A failed modules call should
                # not force reauthorisation when the content calls worked.
                if not response and category != 4:
                    failed_urls.append(url)

                    if debugs:
                        print("Failed category:", category)

            pending_urls = failed_urls
            retries += 1

        self["splash"].hide()

        if success:
            glob.active_playlist["data"]["data_downloaded"] = True
            self.createSetup()

            if pending_urls and debugs:
                print(
                    "Some URLs failed after retry:",
                    pending_urls
                )

        else:
            glob.active_playlist["data"]["data_downloaded"] = False
            self.session.openWithCallback(
                self.close,
                MessageBox,
                _("Access Denied."),
                MessageBox.TYPE_WARNING,
                timeout=5
            )

            if debugs:
                print(
                    "Failed to download all URLs after retries."
                )

    def writeJsonFile(self):
        if debugs:
            print("*** writeJsonFile ***")

        with open(self.playlists_json, "r") as f:
            playlists_all = json.load(f)

        playlists_all[glob.current_selection] = glob.active_playlist

        with open(self.playlists_json, "w") as f:
            json.dump(playlists_all, f, indent=4)

    def createSetup(self):
        if debugs:
            print("*** createSetup ***")

        self.list = []
        self.index = 0

        def add_category_to_list(title, category_type, index):
            if category_type in glob.active_playlist["data"] and glob.active_playlist["data"][category_type]:
                data = glob.active_playlist["data"][category_type]
                if isinstance(data, dict) and "js" in data:
                    data = data["js"]

                if isinstance(data, list) and data and "id" in data[0]:
                    self.index += 1
                    self.list.append([self.index, title, index, ""])

        show_live = glob.active_playlist["player_info"].get("showlive", False)
        show_vod = glob.active_playlist["player_info"].get("showvod", False)
        show_series = glob.active_playlist["player_info"].get("showseries", False)
        available_modules = set(glob.active_playlist["data"].get("available_modules", []))

        glob.active_playlist["data"]["live_streams"] = {}

        if show_live:
            add_category_to_list(_("Live TV"), "live_categories", 0)

        if show_vod:
            add_category_to_list(_("Movies"), "vod_categories", 1)

        if show_series:
            add_category_to_list(_("TV Series"), "series_categories", 2)

        if "tv_archive" in available_modules:
            self.index += 1
            self.list.append([self.index, _("TV Archive"), 5, ""])

        self.index += 1
        self.list.append([self.index, _("Playlist Settings"), 4, ""])
        self.drawList = [buildListEntry(x[0], x[1], x[2], x[3]) for x in self.list]
        self["list"].setList(self.drawList)

        self.writeJsonFile()

        if not self.list:
            self.session.openWithCallback(self.quit, MessageBox, (_("No data, blocked or playlist not compatible with EStalker plugin.")), MessageBox.TYPE_WARNING, timeout=5)

    def quit(self):
        self["splash"].hide()
        self.close()

    def __next__(self):
        if debugs:
            print("*** next ***")

        current_item = self["list"].getCurrent()
        if current_item:
            category = current_item[2]
            if category == 0:
                from . import live
                self.session.openWithCallback(lambda: self.start, live.EStalker_Live_Categories)
            elif category == 1:
                from . import vod
                self.session.openWithCallback(lambda: self.start, vod.EStalker_Vod_Categories)
            elif category == 2:
                from . import series
                self.session.openWithCallback(lambda: self.start, series.EStalker_Series_Categories)
            elif category == 4:
                self.settings()
            elif category == 5:
                from . import catchup
                self.session.openWithCallback(lambda: self.start, catchup.EStalker_Catchup_Categories)

    def settings(self):
        if debugs:
            print("*** settings ***")

        from . import playsettings
        self.session.openWithCallback(self.start, playsettings.EStalker_Settings)

    def reauthorize(self):
        if debugs:
            print("*** reauthorize ***")

        result = reauthorize_portal(self.portal, self.host, self.mac, self.headers)

        if not result:
            return

        self.portal, self.token, self.token_random, self.headers, play_token, status, blocked = result

        glob.active_playlist["playlist_info"].update({
            "token": self.token,
            "token_random": self.token_random,
            "play_token": play_token,
            "status": status,
            "blocked": blocked,
            "headers": self.headers,
        })


def buildListEntry(index, title, category_id, playlisturl):
    icon_mapping = {
        0: "live.png",
        1: "vod.png",
        2: "series.png",
        4: "settings.png",
        5: "catchup.png",
    }

    png = None
    icon_filename = icon_mapping.get(category_id)
    if icon_filename:
        png = LoadPixmap(os.path.join(common_path, icon_filename))

    return (index, str(title), category_id, str(playlisturl), png)
