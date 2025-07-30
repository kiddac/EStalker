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
# from requests.adapters import HTTPAdapter, Retry
from Screens.MessageBox import MessageBox
from Screens.Screen import Screen
from Tools.LoadPixmap import LoadPixmap

# Local application/library-specific imports
from . import _
from . import estalker_globals as glob
from .plugin import skin_directory, common_path, version, hasConcurrent, hasMultiprocessing, cfg, debugs
from .eStaticText import StaticText
from .utils import get_local_timezone, make_request, perform_handshake, get_profile_data


playlists_json = cfg.playlists_json.value


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

        glob.active_playlist["data"]["live_streams"] = {}
        glob.active_playlist["data"]["data_downloaded"] = False

        if os.path.exists("/tmp/allchannels.json"):
            os.remove("/tmp/allchannels.json")

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
            [self.series_categories_url, 2]
        ]

        self.process_downloads()

    def download_url(self, url):
        if debugs:
            print("*** download_url ***", url)

        self.timezone = get_local_timezone()
        self.token = glob.active_playlist["playlist_info"]["token"]
        self.token_random = glob.active_playlist["playlist_info"]["token_random"]
        self.domain = str(glob.active_playlist["playlist_info"].get("domain", ""))
        self.host = str(glob.active_playlist["playlist_info"].get("host", "")).rstrip("/")
        self.mac = glob.active_playlist["playlist_info"].get("mac", "").upper()
        self.portal = glob.active_playlist["playlist_info"].get("portal", None)
        self.portal_version = glob.active_playlist["playlist_info"].get("version", "5.3.1")

        self.sn = hashlib.md5(self.mac.encode()).hexdigest().upper()[:13]
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
            "Cookie": "mac={}; stb_lang=en; timezone={};".format(self.mac, self.timezone),
        }

        self.headers["Authorization"] = "Bearer " + self.token

        category = url[1]
        response = make_request(url[0], method="POST", headers=self.headers, params=None, response_type="json")
        return category, response

    def process_downloads(self):
        if debugs:
            print("*** process_downloads2 ***")

        max_retries = 1
        retries = 0
        success = False

        while retries <= max_retries and not success:
            if retries > 0:
                if debugs:
                    print("Retry attempt:", retries)

                self.reauthorize()

            glob.active_playlist["data"]["live_categories"] = {}
            glob.active_playlist["data"]["vod_categories"] = {}
            glob.active_playlist["data"]["series_categories"] = {}
            if 3 in self.url_list:
                glob.active_playlist["data"]["live_streams"] = {}

            results = []
            threads = len(self.url_list)

            if hasConcurrent or hasMultiprocessing:
                if hasConcurrent:
                    try:
                        from concurrent.futures import ThreadPoolExecutor
                        with ThreadPoolExecutor(max_workers=threads) as executor:
                            results = list(executor.map(self.download_url, self.url_list))
                    except Exception as e:
                        print("Concurrent execution error:", e)

                elif hasMultiprocessing:
                    try:
                        from multiprocessing.pool import ThreadPool
                        pool = ThreadPool(threads)
                        results = pool.imap(self.download_url, self.url_list)
                        pool.close()
                        pool.join()
                    except Exception as e:
                        print("Multiprocessing execution error:", e)

                # If results is an iterator, convert to list
                if not isinstance(results, list):
                    results = list(results)

            else:
                for url in self.url_list:
                    result = self.download_url(url)
                    results.append(result)

            # Check if all URLs downloaded successfully (response is truthy)
            all_success = all(response for category, response in results)

            if all_success:
                success = True
                for category, response in results:
                    # response = sort_categories(response)
                    if category == 0:
                        glob.active_playlist["data"]["live_categories"] = response
                    elif category == 1:
                        glob.active_playlist["data"]["vod_categories"] = response
                    elif category == 2:
                        glob.active_playlist["data"]["series_categories"] = response
                    elif category == 3:
                        glob.active_playlist["data"]["live_streams"] = response
            else:
                retries += 1

        self["splash"].hide()

        if success:
            glob.active_playlist["data"]["data_downloaded"] = True
            self.createSetup()
        else:
            glob.active_playlist["data"]["data_downloaded"] = False
            self.session.openWithCallback(self.close, MessageBox, (_("Access Denied.")), MessageBox.TYPE_WARNING, timeout=5)
            if debugs:
                print("Failed to download all URLs after retries.")

    def writeJsonFile(self):
        if debugs:
            print("*** writeJsonFile ***")

        with open(playlists_json, "r") as f:
            playlists_all = json.load(f)

        playlists_all[glob.current_selection] = glob.active_playlist

        with open(playlists_json, "w") as f:
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
        # show_catchup = glob.active_playlist["player_info"].get("showcatchup", False)

        glob.active_playlist["data"]["live_streams"] = {}

        """
        if has_catchup:
            glob.active_playlist["data"]["catchup"] = True
            """

        if show_live:
            add_category_to_list(_("Live TV"), "live_categories", 0)

        if show_vod:
            add_category_to_list(_("Movies"), "vod_categories", 1)

        if show_series:
            add_category_to_list(_("TV Series"), "series_categories", 2)

        """
        if show_catchup and glob.active_playlist["data"]["catchup"]:
            self.index += 1
            self.list.append([self.index, _("Catch Up TV"), 3, ""])
            """
        """
        if show_catchup:
            self.index += 1
            self.list.append([self.index, _("Catch Up TV"), 3, ""])
            """

        self.index += 1
        self.list.append([self.index, _("Playlist Settings"), 4, ""])
        self.drawList = [buildListEntry(x[0], x[1], x[2], x[3]) for x in self.list]
        self["list"].setList(self.drawList)

        self.writeJsonFile()

        if not self.list:
            self.session.openWithCallback(self.close, MessageBox, (_("No data, blocked or playlist not compatible with EStalker plugin.")), MessageBox.TYPE_WARNING, timeout=5)

    def quit(self):
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
            # elif category == 3:
            #     from . import catchup
            #     self.session.openWithCallback(lambda: self.start, catchup.EStalker_Catchup_Categories)
            elif category == 4:
                self.settings()

    def settings(self):
        if debugs:
            print("*** settings ***")

        from . import playsettings
        self.session.openWithCallback(self.start, playsettings.EStalker_Settings)

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

        if debugs:
            print("*** account_info ***", account_info)

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


def buildListEntry(index, title, category_id, playlisturl):
    icon_mapping = {
        0: "live.png",
        1: "vod.png",
        2: "series.png",
        # 3: "catchup.png",
        4: "settings.png",
        5: "epg_download.png"
    }

    png = None
    icon_filename = icon_mapping.get(category_id)
    if icon_filename:
        png = LoadPixmap(os.path.join(common_path, icon_filename))

    return (index, str(title), category_id, str(playlisturl), png)
