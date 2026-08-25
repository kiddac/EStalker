#!/usr/bin/python
# -*- coding: utf-8 -*-
from __future__ import division

import codecs
import hashlib
import json
import os
import re
import time
from datetime import datetime, timedelta
from itertools import cycle, islice

try:
    from urllib import quote
except ImportError:
    from urllib.parse import quote

try:
    from urlparse import urlparse
except ImportError:
    from urllib.parse import urlparse

from Components.ActionMap import ActionMap
from Components.Pixmap import Pixmap
from Components.ProgressBar import ProgressBar
from Components.Sources.List import List
from Screens.MessageBox import MessageBox
from Screens.Screen import Screen
from Screens.VirtualKeyBoard import VirtualKeyBoard
from Tools.LoadPixmap import LoadPixmap

from . import _
from . import estalker_globals as glob
from .eStaticText import StaticText
from .plugin import cfg, common_path, debugs, isDreambox, skin_directory
from .utils import get_local_timezone, make_request, reauthorize_portal

monotonic_time = getattr(time, "monotonic", time.time)


class EStalker_Catchup_Categories(Screen):
    ALLOW_SUSPEND = True

    def __init__(self, session):
        if debugs:
            print("*** catchup init ***")

        Screen.__init__(self, session)
        self.session = session
        glob.categoryname = "catchup"

        self.skin_path = os.path.join(skin_directory, cfg.skin.value)
        skin = os.path.join(self.skin_path, "live_categories.xml")
        if isDreambox:
            skin = os.path.join(self.skin_path, "DreamOS/live_categories.xml")
        with codecs.open(skin, "r", encoding="utf-8") as f:
            self.skin = f.read()

        self.playlists_json = cfg.playlists_json.value
        self.setup_title = _("TV Archive")
        self.main_title = _("TV Archive")
        self.group_title = ""

        self.main_list = []
        self["main_list"] = List(self.main_list, enableWrapAround=True)
        self["main_list"].onSelectionChanged.append(self.selectionChanged)
        self["main_title"] = StaticText(self.main_title)
        self["x_title"] = StaticText()
        self["x_description"] = StaticText()
        self["picon"] = Pixmap()
        self["progress"] = ProgressBar()
        self["epg_bg"] = Pixmap()
        self["epg_list"] = List([], enableWrapAround=True)
        self.epgshortlist = []
        self["epg_short_list"] = List(self.epgshortlist, enableWrapAround=True)
        self["epg_short_list"].onSelectionChanged.append(self.displayShortEPG)
        self.selectedlist = self["main_list"]
        self["page"] = StaticText("")
        self["listposition"] = StaticText("")

        self["key_red"] = StaticText(_("Back"))
        self["key_green"] = StaticText(_("OK"))
        self["key_yellow"] = StaticText(_("Sort: A-Z"))
        self["key_blue"] = StaticText(_("Search"))
        self["key_epg"] = StaticText("")
        self["key_menu"] = StaticText("")

        self.level = 1
        self.itemsperpage = 14
        self.searchString = ""
        self.filterresult = ""
        self.sortindex = 0
        self.sortText = _("Sort: A-Z")
        self.list1 = []
        self.list2 = []
        self.archive_channels = []
        self.current_category = ""
        self.current_channel = {}
        self.epg_selection_ready_at = 0

        playlist_info = glob.active_playlist["playlist_info"]
        self.token = playlist_info.get("token", "")
        self.domain = str(playlist_info.get("domain", ""))
        self.port = playlist_info.get("port", "")
        self.host = str(playlist_info.get("host", "")).rstrip("/")
        self.mac = playlist_info.get("mac", "").upper()
        self.portal = playlist_info.get("portal")
        self.path_prefix = playlist_info.get("path_prefix", "")
        self.force_ch_link_check = playlist_info.get("force_ch_link_check", "0")
        self.timezone = get_local_timezone()
        self.referer = self.host + self.path_prefix + "index.html"
        self.sn = hashlib.md5(self.mac.encode()).hexdigest().upper()[:13]
        self.adid = hashlib.md5((self.sn + self.mac).encode()).hexdigest()

        encoded_mac = quote(self.mac, safe="")
        encoded_timezone = quote(self.timezone, safe="")
        saved_headers = playlist_info.get("headers", {})
        self.headers = saved_headers.copy() if isinstance(saved_headers, dict) else {}
        if not self.headers:
            cookie = "mac={}; stb_lang=en; timezone={}".format(encoded_mac, encoded_timezone)
            if self.portal and "/stalker_portal/" in self.portal:
                cookie += "; adid={}".format(self.adid)
            self.headers = {
                "Pragma": "no-cache",
                "Accept": "*/*",
                "Accept-Encoding": "gzip, deflate",
                "Host": "{}:{}".format(self.domain, self.port) if self.port else self.domain,
                "User-Agent": "Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 (KHTML, like Gecko) MAG200 stbapp ver: 2 rev: 250 Safari/533.3",
                "X-User-Agent": "Model: MAG250; Link: WiFi",
                "Connection": "keep-alive",
                "Referer": self.referer,
                "Cookie": cookie,
            }
        self.headers["Authorization"] = "Bearer " + self.token

        self._px_more = LoadPixmap(os.path.join(common_path, "more.png"))
        self._px_play = LoadPixmap(os.path.join(common_path, "play.png"))

        self["category_actions"] = ActionMap(["EStalkerActions"], {
            "cancel": self.back, "red": self.back,
            "ok": self.parentalCheck, "OK": self.parentalCheck, "green": self.parentalCheck,
            "yellow": self.sort, "blue": self.search,
            "left": self.pageUp, "right": self.pageDown,
            "up": self.goUp, "down": self.goDown,
            "channelUp": self.pageUp, "channelDown": self.pageDown,
            "0": self.reset,
        }, -2)

        self["channel_actions"] = ActionMap(["EStalkerActions"], {
            "cancel": self.back, "red": self.back,
            "ok": self.parentalCheck, "OK": self.parentalCheck, "green": self.parentalCheck,
            "yellow": self.sort, "blue": self.search,
            "left": self.pageUp, "right": self.pageDown,
            "up": self.goUp, "down": self.goDown,
            "channelUp": self.pageUp, "channelDown": self.pageDown,
            "0": self.reset,
        }, -2)
        self["channel_actions"].setEnabled(False)

        self["epg_actions"] = ActionMap(["EStalkerActions"], {
            "cancel": self.back, "red": self.back,
            "ok": self.playCatchup, "OK": self.playCatchup, "green": self.playCatchup,
            "yellow": self.reverse,
            "left": self.pageUp, "right": self.pageDown,
            "up": self.goUp, "down": self.goDown,
            "channelUp": self.pageUp, "channelDown": self.pageDown,
            "0": self.reset,
        }, -2)
        self["epg_actions"].setEnabled(False)
        glob.nextlist = [{
            "next_url": "",
            "index": 0,
            "level": self.level,
            "sort": self.sortText,
            "filter": "",
        }]

        self.onFirstExecBegin.append(self.createSetup)
        self.onLayoutFinish.append(self.__layoutFinished)

    def __layoutFinished(self):
        self.setTitle(self.setup_title)
        self.hideEPG()

    def goUp(self):
        instance = self.selectedlist.master.master.instance
        instance.moveSelection(instance.moveUp)
        self._selectionChanged()

    def goDown(self):
        instance = self.selectedlist.master.master.instance
        instance.moveSelection(instance.moveDown)
        self._selectionChanged()

    def pageUp(self):
        instance = self.selectedlist.master.master.instance
        instance.moveSelection(instance.pageUp)
        self._selectionChanged()

    def pageDown(self):
        instance = self.selectedlist.master.master.instance
        instance.moveSelection(instance.pageDown)
        self._selectionChanged()

    def reset(self):
        self.selectedlist.setIndex(0)
        self._selectionChanged()

    def _selectionChanged(self):
        if self.selectedlist == self["epg_short_list"]:
            self.displayShortEPG()
        else:
            self.selectionChanged()

    def createSetup(self, data=None):
        if debugs:
            print("*** createSetup ***", self.level)

        self["x_title"].setText("")
        self["x_description"].setText("")

        if self.level == 1:
            if not self.archive_channels:
                self.archive_channels = self.downloadArchiveChannels()
            self.getCategories()
        elif self.level == 2:
            self.getLevel2()

    def buildLists(self):
        if debugs:
            print("*** buildLists ***", self.level)

        if self.level == 1:
            self.buildList1()
        elif self.level == 2:
            self.buildList2()
        else:
            self.buildList2()

        self.resetButtons()
        self.selectionChanged()

    def _request(self, params):
        response = make_request(
            self.portal,
            method="GET",
            headers=self.headers,
            params=params,
            response_type="json",
        )
        if not response:
            self.reauthorize()
            response = make_request(
                self.portal,
                method="GET",
                headers=self.headers,
                params=params,
                response_type="json",
            )
        return response

    def downloadArchiveChannels(self):
        if debugs:
            print("*** downloadArchiveChannels ***")

        params = {
            "type": "itv",
            "action": "get_all_channels",
            "force_ch_link_check": self.force_ch_link_check,
            "JsHttpRequest": "1-xml",
        }
        response = self._request(params)
        payload = response.get("js", {}) if isinstance(response, dict) else {}
        channels = payload.get("data", []) if isinstance(payload, dict) else payload
        if not isinstance(channels, list):
            channels = []

        archive_channels = []
        for channel in channels:
            if not isinstance(channel, dict):
                continue
            archive = str(channel.get("archive", channel.get("tv_archive", "0"))).lower()
            if archive not in ("1", "true", "yes"):
                continue
            if not channel.get("id") or not channel.get("name"):
                continue
            archive_channels.append(channel)
        return archive_channels

    def getCategories(self):
        if debugs:
            print("*** getCategories ***")

        archive_category_ids = set(
            str(channel.get("tv_genre_id", channel.get("category_id", "0")))
            for channel in self.archive_channels
        )
        categories = glob.active_playlist.get("data", {}).get("live_categories", {}).get("js", [])
        if not isinstance(categories, list):
            categories = []
        known_category_ids = set(
            str(category.get("id", ""))
            for category in categories
            if isinstance(category, dict)
        )
        self.list1 = []
        for category in categories:
            if not isinstance(category, dict):
                continue
            category_id = str(category.get("id", ""))
            if category_id not in archive_category_ids:
                continue
            self.list1.append([
                len(self.list1),
                str(category.get("title", _("No category"))),
                category_id,
                False,
                str(category.get("number", "")),
            ])

        uncategorised = [
            channel for channel in self.archive_channels
            if str(channel.get("tv_genre_id", channel.get("category_id", "0"))) not in known_category_ids
        ]
        if uncategorised:
            self.list1.append([len(self.list1), _("Uncategorised"), "__uncategorised__", False, ""])
        if not self.list1 and self.archive_channels:
            self.list1.append([0, _("All"), "*", False, ""])

        self.buildLists()

    def getLevel2(self):
        if debugs:
            print("*** getLevel2 ***")

        if self.current_category == "*":
            channels = self.archive_channels[:]
        elif self.current_category == "__uncategorised__":
            category_ids = set(
                str(category.get("id", ""))
                for category in glob.active_playlist.get("data", {}).get("live_categories", {}).get("js", [])
                if isinstance(category, dict)
            )
            channels = [
                channel for channel in self.archive_channels
                if str(channel.get("tv_genre_id", channel.get("category_id", "0"))) not in category_ids
            ]
        else:
            channels = [
                channel for channel in self.archive_channels
                if str(channel.get("tv_genre_id", channel.get("category_id", "0"))) == self.current_category
            ]
        self.list2 = []
        for channel in channels:
            stream_id = str(channel.get("id", ""))
            name = str(channel.get("name", ""))
            logo = str(channel.get("logo", ""))
            if not logo.startswith(("http://", "https://")):
                logo = ""
            self.list2.append([
                len(self.list2), name, stream_id, logo, stream_id,
                str(channel.get("number", "")), self.current_category,
                str(channel.get("cmd", "")), "", "", "", "", "", "", "", "",
                False, False, False, None, None,
                {
                    "archive": channel.get("archive", channel.get("tv_archive", "1")),
                    "tv_archive_duration": channel.get("tv_archive_duration", ""),
                    "open": str(channel.get("open", "1")).lower() not in ("0", "false", "no"),
                },
            ])
        self.buildLists()

    def downloadApiData(self, params, page=1):
        request_params = dict(params)
        request_params["p"] = page
        request_params["JsHttpRequest"] = "1-xml"
        return self._request(request_params)

    def catchupEPG(self):
        if debugs:
            print("*** catchupEPG ***")

        response = self._request({
            "type": "epg",
            "action": "get_week",
            "JsHttpRequest": "1-xml",
        })
        dates = response.get("js", []) if isinstance(response, dict) else []
        if isinstance(dates, dict):
            dates = dates.get("data", [])
        if not isinstance(dates, list):
            dates = []

        now = datetime.now()
        try:
            archive_hours = int(self.current_channel.get("tv_archive_duration", 0) or 0)
        except (TypeError, ValueError):
            archive_hours = 0
        cutoff_date = (now - timedelta(hours=archive_hours)).date() if archive_hours > 0 else None

        available_dates = []
        for item in dates:
            if not isinstance(item, dict):
                continue
            date_value = str(item.get("f_mysql", item.get("date", "")))
            try:
                date_object = datetime.strptime(date_value, "%Y-%m-%d").date()
            except (TypeError, ValueError):
                continue
            if date_object > now.date():
                continue
            if cutoff_date and date_object < cutoff_date:
                continue
            available_dates.append(date_value)

        self.epgshortlist = []
        for date_value in sorted(set(available_dates), reverse=True):
            programmes = self._downloadProgrammes(date_value)
            for programme in programmes:
                if not isinstance(programme, dict):
                    continue
                mark_archive = str(programme.get("mark_archive", "0")).lower()
                if mark_archive not in ("1", "true", "yes"):
                    continue
                event_id = str(programme.get("id", ""))
                if not event_id:
                    continue

                title = str(programme.get("name") or programme.get("o_name") or _("Unknown programme"))
                description = str(programme.get("descr", programme.get("description", "")) or "")
                time_from = str(programme.get("t_time", "") or "")
                time_to = str(programme.get("t_time_to", "") or "")
                start_timestamp = programme.get("start_timestamp", "")
                stop_timestamp = programme.get("stop_timestamp", "")

                if not time_from:
                    try:
                        time_from = datetime.fromtimestamp(int(start_timestamp)).strftime("%H:%M")
                    except (TypeError, ValueError, OverflowError):
                        pass
                if not time_to:
                    try:
                        time_to = datetime.fromtimestamp(int(stop_timestamp)).strftime("%H:%M")
                    except (TypeError, ValueError, OverflowError):
                        pass

                try:
                    date_all = datetime.strptime(date_value, "%Y-%m-%d").strftime("%a %d/%m")
                except (TypeError, ValueError):
                    date_all = date_value
                time_all = " - ".join(value for value in (time_from, time_to) if value)
                command = "auto /media/{}.mpg".format(event_id)

                self.epgshortlist.append(buildCatchupEPGListEntry(
                    title,
                    date_all,
                    time_all,
                    description,
                    event_id,
                    command,
                    len(self.epgshortlist),
                    date_value,
                    start_timestamp,
                    stop_timestamp,
                ))

        self.epgshortlist.sort(
            key=lambda item: self._programmeSortValue(item[8], item[7], item[2]),
            reverse=True,
        )
        self["epg_short_list"].setList(self.epgshortlist)

        if not self.epgshortlist:
            self.session.open(
                MessageBox,
                _("TV Archive currently not available. Missing EPG data."),
                MessageBox.TYPE_INFO,
                timeout=3,
            )
            return

        main_instance = self["main_list"].master.master.instance
        main_instance.setSelectionEnable(0)
        epg_instance = self["epg_short_list"].master.master.instance
        epg_instance.setSelectionEnable(1)
        self.selectedlist = self["epg_short_list"]
        self["channel_actions"].setEnabled(False)
        self["epg_actions"].setEnabled(True)
        self.epg_selection_ready_at = monotonic_time() + 0.5
        self["epg_bg"].show()
        self["key_yellow"].setText(_("Reverse"))
        self["key_blue"].setText("")
        self["key_green"].setText(_("Play"))
        self.displayShortEPG()

    def _downloadProgrammes(self, date_value):
        params = {
            "type": "epg",
            "action": "get_simple_data_table",
            "ch_id": self.current_channel.get("id", ""),
            "date": date_value,
        }
        response = self.downloadApiData(params, 1)
        payload = response.get("js", {}) if isinstance(response, dict) else {}
        if not isinstance(payload, dict):
            return []
        programmes = payload.get("data", [])
        if not isinstance(programmes, list):
            programmes = []

        try:
            total_items = int(payload.get("total_items", len(programmes)))
            max_page_items = int(payload.get("max_page_items", len(programmes) or 1))
            total_pages = max(1, (total_items + max_page_items - 1) // max_page_items)
        except (TypeError, ValueError, ZeroDivisionError):
            total_pages = 1

        for page in range(2, total_pages + 1):
            page_response = self.downloadApiData(params, page)
            page_payload = page_response.get("js", {}) if isinstance(page_response, dict) else {}
            page_data = page_payload.get("data", []) if isinstance(page_payload, dict) else []
            if isinstance(page_data, list):
                programmes.extend(page_data)
        return programmes

    def _programmeSortValue(self, timestamp, date_value, time_value):
        try:
            return int(timestamp)
        except (TypeError, ValueError):
            pass
        try:
            start_time = str(time_value).split(" - ", 1)[0]
            parsed = datetime.strptime("{} {}".format(date_value, start_time), "%Y-%m-%d %H:%M")
            return int(time.mktime(parsed.timetuple()))
        except (TypeError, ValueError):
            return 0

    def displayShortEPG(self):
        current = self["epg_short_list"].getCurrent()
        if not current:
            return
        self["x_title"].setText("{} {}".format(current[2], current[0]).strip())
        self["x_description"].setText(str(current[3]))
        self["main_title"].setText(": ".join(
            value for value in (self.main_title, self.group_title, str(current[1])) if value
        ))
        position = self["epg_short_list"].getIndex() + 1
        total = len(self.epgshortlist)
        page = (position - 1) // self.itemsperpage + 1
        pages = (total + self.itemsperpage - 1) // self.itemsperpage if total else 0
        self["page"].setText(_("Page: ") + "{}/{}".format(page, pages))
        self["listposition"].setText("{}/{}".format(position, total))

    def reverse(self):
        self.epgshortlist.reverse()
        self["epg_short_list"].setList(self.epgshortlist)
        self.displayShortEPG()

    def createLink(self, url, params):
        if debugs:
            print("*** createLink ***", params)
        return self._request(params)

    def reauthorize(self):
        if debugs:
            print("*** reauthorize ***")

        result = reauthorize_portal(self.portal, self.host, self.mac, self.headers)
        if not result:
            return
        self.portal, self.token, token_random, self.headers, play_token, status, blocked = result
        glob.active_playlist["playlist_info"].update({
            "portal": self.portal,
            "token": self.token,
            "token_random": token_random,
            "headers": self.headers,
            "play_token": play_token,
            "status": status,
            "blocked": blocked,
        })
        try:
            with open(self.playlists_json, "r") as f:
                playlists_all = json.load(f)
            for index, playlist in enumerate(playlists_all):
                info = playlist.get("playlist_info", {})
                if (info.get("domain") == glob.active_playlist["playlist_info"].get("domain")
                        and info.get("mac") == glob.active_playlist["playlist_info"].get("mac")):
                    playlists_all[index] = glob.active_playlist
                    break
            with open(self.playlists_json, "w") as f:
                json.dump(playlists_all, f, indent=4)
        except (IOError, OSError, ValueError, TypeError):
            pass

    def buildList1(self):
        restore_index = glob.nextlist[-1].get("index", 0)
        self.main_list = [
            buildCategoryList(x[0], x[1], x[2], x[3], self._px_more)
            for x in self.list1 if not x[3]
        ]
        self["main_list"].setList(self.main_list)
        self._restoreIndex(restore_index)

    def buildList2(self):
        restore_index = glob.nextlist[-1].get("index", 0)
        self.main_list = [
            buildCatchupStreamList(x[0], x[1], x[2], x[3], x[5], x[18], self._px_more)
            for x in self.list2 if not x[18]
        ]
        self["main_list"].setList(self.main_list)
        self._restoreIndex(restore_index)

    def _restoreIndex(self, restore_index):
        if self["main_list"].getCurrent():
            index = min(restore_index, len(self.main_list) - 1)
            self["main_list"].setIndex(max(0, index))

    def selectionChanged(self):
        current = self["main_list"].getCurrent()
        if not current:
            self["page"].setText("")
            self["listposition"].setText("")
            self["x_title"].setText("")
            self["x_description"].setText("")
            return

        current_index = self["main_list"].getIndex()
        glob.nextlist[-1]["index"] = current_index
        position = current_index + 1
        total = len(self.main_list)
        page = (position - 1) // self.itemsperpage + 1
        pages = (total + self.itemsperpage - 1) // self.itemsperpage if total else 0
        self["page"].setText(_("Page: ") + "{}/{}".format(page, pages))
        self["listposition"].setText("{}/{}".format(position, total))
        self["main_title"].setText(": ".join(x for x in (self.main_title, self.group_title, str(current[0])) if x))
        self["x_title"].setText(str(current[0]))
        self["x_description"].setText("")

    def resetButtons(self):
        if self.selectedlist == self["epg_short_list"]:
            self["key_yellow"].setText(_("Reverse"))
            self["key_blue"].setText("")
            self["key_green"].setText(_("Play"))
            return
        if glob.nextlist[-1].get("filter"):
            self["key_yellow"].setText("")
            self["key_blue"].setText(_("Reset Search"))
        else:
            self["key_yellow"].setText(glob.nextlist[-1].get("sort", self.sortText))
            self["key_blue"].setText(_("Search"))
        self["key_green"].setText(_("OK"))

    def _activeList(self):
        if self.level == 1:
            return self.list1
        return self.list2

    def sort(self):
        if self.selectedlist == self["epg_short_list"]:
            self.reverse()
            return
        current_sort = self["key_yellow"].getText()
        if not current_sort:
            return
        sortlist = [_("Sort: A-Z"), _("Sort: Z-A"), _("Sort: Original")]
        try:
            self.sortindex = sortlist.index(self.sortText)
        except ValueError:
            self.sortindex = 0

        active_list = self._activeList()
        if current_sort == _("Sort: A-Z"):
            active_list.sort(key=lambda x: str(x[1]).lower())
        elif current_sort == _("Sort: Z-A"):
            active_list.sort(key=lambda x: str(x[1]).lower(), reverse=True)
        else:
            active_list.sort(key=lambda x: x[0])

        glob.nextlist[-1]["index"] = 0
        self.sortText = str(next(islice(cycle(sortlist), self.sortindex + 1, None)))
        glob.nextlist[-1]["sort"] = self.sortText
        self.buildLists()

    def search(self, result=None):
        if self.selectedlist == self["epg_short_list"]:
            return
        if self["key_blue"].getText() == _("Reset Search"):
            self.resetSearch()
        else:
            self.session.openWithCallback(
                self.filterChannels,
                VirtualKeyBoard,
                title=_("Search TV Archive..."),
                text=self.searchString,
            )

    def filterChannels(self, result=None):
        if not result:
            return
        self.searchString = str(result)
        active_list = self._activeList()
        filtered = [item for item in active_list if self.searchString.lower() in str(item[1]).lower()]
        if not filtered:
            self.session.openWithCallback(
                self.search,
                MessageBox,
                _("No results found."),
                type=MessageBox.TYPE_ERROR,
                timeout=5,
            )
            return

        glob.nextlist[-1]["filter"] = self.searchString
        glob.nextlist[-1]["index"] = 0
        self["key_blue"].setText(_("Reset Search"))
        self["key_yellow"].setText("")
        if self.level == 1:
            self.list1 = filtered
        else:
            self.list2 = filtered
        self.buildLists()

    def resetSearch(self):
        self.searchString = ""
        glob.nextlist[-1]["filter"] = ""
        glob.nextlist[-1]["index"] = 0
        self.createSetup()

    def parentalCheck(self):
        self.next()

    def next(self):
        if self.selectedlist == self["epg_short_list"]:
            self.playCatchup()
            return

        current = self["main_list"].getCurrent()
        if not current:
            return

        current_index = self["main_list"].getIndex()
        glob.nextlist[-1]["index"] = current_index

        if self.level == 1:
            self.current_category = str(current[3])
            self.group_title = str(current[0])
            self._advanceLevel()
        elif self.level == 2:
            channel_id = str(current[4])
            self.current_channel = next(
                (channel for channel in self.archive_channels if str(channel.get("id", "")) == channel_id),
                {},
            )
            self.group_title = str(current[0])
            if str(self.current_channel.get("open", "1")).lower() in ("0", "false", "no"):
                self.session.open(MessageBox, _("This channel is currently unavailable."), MessageBox.TYPE_ERROR, timeout=3)
                return
            self.catchupEPG()

    def _advanceLevel(self):
        self.level += 1
        self["category_actions"].setEnabled(self.level == 1)
        self["channel_actions"].setEnabled(self.level > 1)
        self.sortText = _("Sort: A-Z")
        glob.nextlist.append({
            "next_url": "",
            "index": 0,
            "level": self.level,
            "sort": self.sortText,
            "filter": "",
        })
        # Reset the new level only after its navigation entry exists. Doing
        # this before append() fires selectionChanged() against the parent
        # entry and overwrites the saved category index with zero.
        self["main_list"].setIndex(0)
        self.createSetup()

    def playCatchup(self):
        if monotonic_time() < self.epg_selection_ready_at:
            return

        current = self["epg_short_list"].getCurrent()
        if not current:
            return

        event_id = str(current[4])
        command = str(current[10])
        params = {
            "type": "tv_archive",
            "action": "create_link",
            "cmd": command,
            "series": "",
            "forced_storage": "",
            "disable_ad": "0",
            "download": "0",
            "force_ch_link_check": "0",
            "JsHttpRequest": "1-xml",
        }
        response = self.createLink(self.portal, params)
        link_data = response.get("js", {}) if isinstance(response, dict) else {}
        if isinstance(link_data, list):
            link_data = next((item for item in link_data if isinstance(item, dict) and item.get("cmd")), {})
        if not isinstance(link_data, dict):
            link_data = {}

        stream_url = str(link_data.get("cmd", ""))
        error = str(link_data.get("error", ""))
        if not stream_url:
            errors = {
                "limit": _("Maximum number of connections reached."),
                "nothing_to_play": _("Nothing to play."),
                "link_fault": _("Server error or invalid link."),
                "access_denied": _("Access denied."),
            }
            self.session.open(MessageBox, errors.get(error, _("Server error or invalid link.")), MessageBox.TYPE_ERROR, timeout=3)
            return

        stream_url = re.sub(r"%mac%", self.mac, stream_url, flags=re.IGNORECASE)
        parts = stream_url.split(None, 1)
        if len(parts) == 2:
            stream_url = parts[1].lstrip()
        parsed = urlparse(stream_url)
        if parsed.scheme in ("http", "https"):
            stream_url = parsed.geturl()

        glob.categoryname = "catchup"
        glob.currentchannellist = self.epgshortlist[:]
        glob.currentchannellistindex = self["epg_short_list"].getIndex()
        glob.catchupdata = [str(current[0]), str(current[3])]

        from . import vodplayer
        streamtype = str(glob.active_playlist["player_info"].get("vodtype", "4097"))
        metadata = {
            "archive_channel_id": str(self.current_channel.get("id", "")),
            "archive_event_id": event_id,
            "archive_date": str(current[7]),
        }
        self.session.openWithCallback(
            self.setIndex,
            vodplayer.EStalker_VodPlayer,
            stream_url,
            streamtype,
            event_id,
            str(link_data.get("storage_id", "")),
            metadata,
        )

    def setIndex(self, data=None):
        if self["epg_short_list"].getCurrent():
            self["epg_short_list"].setIndex(glob.currentchannellistindex)
            self.displayShortEPG()

    def hideEPG(self):
        self["epg_list"].setList([])
        self["epg_short_list"].setList([])
        self["picon"].hide()
        self["epg_bg"].hide()
        self["progress"].hide()

    def back(self, data=None):
        if self.selectedlist == self["epg_short_list"]:
            epg_instance = self["epg_short_list"].master.master.instance
            epg_instance.setSelectionEnable(0)
            self["epg_short_list"].setList([])
            self.epgshortlist = []
            main_instance = self["main_list"].master.master.instance
            main_instance.setSelectionEnable(1)
            self.selectedlist = self["main_list"]
            self["epg_actions"].setEnabled(False)
            self["channel_actions"].setEnabled(True)
            self.epg_selection_ready_at = 0
            self["epg_bg"].hide()
            self["x_title"].setText("")
            self["x_description"].setText("")
            self.resetButtons()
            self.selectionChanged()
            return

        if self.level == 1:
            self.close()
            return

        glob.nextlist.pop()
        self.level -= 1
        self["category_actions"].setEnabled(self.level == 1)
        self["channel_actions"].setEnabled(self.level > 1)
        self.sortText = glob.nextlist[-1].get("sort", _("Sort: A-Z"))
        self.searchString = ""
        if self.level == 1:
            self.group_title = ""
        elif self.level == 2:
            self.current_channel = {}
        self.epg_selection_ready_at = 0
        self.createSetup()


def buildCategoryList(index, title, category_id, hidden, px_more=None):
    return (title, px_more, index, category_id, hidden)


def buildCatchupStreamList(index, title, stream_id, stream_icon, number, hidden, px_more=None):
    return (title, px_more, index, "", stream_id, stream_icon, number, hidden)


def buildCatchupEPGListEntry(title, date_all, time_all, description, event_id, command, index, date_value, start_timestamp, stop_timestamp):
    return (
        title, date_all, time_all, description, event_id, "",
        index, date_value, start_timestamp, stop_timestamp, command
    )
