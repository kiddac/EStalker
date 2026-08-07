#!/usr/bin/python
# -*- coding: utf-8 -*-

# Standard library imports
from __future__ import division

import json
import os
import re
import time
from collections import OrderedDict, deque

try:
    from http.client import HTTPConnection
    HTTPConnection.debuglevel = 0
except ImportError:
    from httplib import HTTPConnection
    HTTPConnection.debuglevel = 0

from datetime import datetime

try:
    from urllib.parse import urlparse
except ImportError:
    from urlparse import urlparse

try:
    from urllib import quote
except ImportError:
    from urllib.parse import quote


# Third-party imports
import requests
from requests.adapters import HTTPAdapter

# Enigma2 components
from Components.ActionMap import ActionMap
from Components.Pixmap import Pixmap
from Components.Sources.List import List
from enigma import eTimer
from Screens.MessageBox import MessageBox
from Screens.Screen import Screen
from Tools.LoadPixmap import LoadPixmap
from Components.Label import Label

# Local application/library-specific imports
from . import _
from . import estalker_globals as glob
from .plugin import skin_directory, cfg, common_path, version, hasConcurrent, hasMultiprocessing
from .eStaticText import StaticText
from .utils import get_local_timezone, make_request, xtream_request, perform_handshake, get_profile_data, get_account_info
from . import processfiles as loadfiles

try:
    basestring
except NameError:
    basestring = str


def parse_date_safe(date_str):
    if not date_str or not isinstance(date_str, basestring):
        return None

    s = date_str.strip()

    # Remove time part: "12:00 am", "12:00am", "1:30 pm", etc.
    s = re.sub(r'\d{1,2}:\d{2}\s?(am|pm)?', '', s, flags=re.IGNORECASE)

    # Remove any trailing comma and whitespace
    s = s.rstrip(', ').strip()

    try:
        # Format: "October 15, 2026"
        return datetime.strptime(s, "%B %d, %Y")
    except Exception:
        return None


def extract_portal_path_from_stream(resp, url):
    try:
        portal_prefix = ""

        for line in resp.iter_lines():
            try:
                if isinstance(line, bytes):  # Python 3
                    line = line.decode("utf-8", "ignore")
                elif not isinstance(line, str):  # Python 2 unicode
                    line = line.encode("utf-8")
            except Exception:
                continue

            line = line.strip()
            if not line or "this.ajax_loader = this" not in line:
                continue

            if "this.portal_path" in line:
                portal_prefix = '/stalker_portal' if '/stalker_portal/' in url else '/c'

            # Pattern 1: this.portal_protocol+'://'+this.portal_ip+'/'+this.portal_path+'/server/load.php'
            match = re.search(
                r'this\.portal_protocol\s*\+\s*[\'"]://[\'"]\s*\+\s*this\.portal_ip\s*\+\s*[\'"]/[\'"]\s*\+\s*this\.portal_path\s*\+\s*[\'"](/[^\'"]+)',
                line
            )

            if not match:
                # Pattern 2: this.portal_protocol+'://'+this.portal_ip+'/server/move.php'
                match = re.search(
                    r'this\.portal_protocol\s*\+\s*[\'"]://[\'"]\s*\+\s*this\.portal_ip\s*\+\s*[\'"](/[^\'"]+)',
                    line
                )

            if not match:
                # Pattern 3: this.portal_ip+'/portal.php'
                match = re.search(r'this\.portal_ip\s*\+\s*[\'"](/[^\'"]+)', line)

            if match:
                path = match.group(1)
                path = portal_prefix + path
                path = re.sub(r'/+', '/', path.strip())
                return path

    except Exception as e:
        print("extract_portal_path_from_stream error:", e)

    return None


class EStalker_Playlists(Screen):
    ALLOW_SUSPEND = True

    def __init__(self, session):
        Screen.__init__(self, session)
        self.session = session

        skin_path = os.path.join(skin_directory, cfg.skin.value)
        skin = os.path.join(skin_path, "playlists.xml")
        with open(skin, "r") as f:
            self.skin = f.read()

        self.playlist_file = cfg.playlist_file.value
        self.playlists_json = cfg.playlists_json.value
        self.playlists_all = []

        self.setup_title = _("Manage Playlists")

        self["key_red"] = StaticText(_("Back"))
        self["key_green"] = StaticText(_("OK"))
        self["key_yellow"] = StaticText(_("Delete"))
        self["key_blue"] = StaticText(_("Auto Delete"))
        self["version"] = StaticText(version)

        self.list = []
        self.drawList = []

        self["playlists"] = List(self.drawList, enableWrapAround=True)
        self["playlists"].onSelectionChanged.append(self.getCurrentEntry)
        self["splash"] = Pixmap()
        self["splash"].show()
        self["scroll_up"] = Pixmap()
        self["scroll_down"] = Pixmap()
        self["scroll_up"].hide()
        self["scroll_down"].hide()

        self["actions"] = ActionMap(["EStalkerActions"], {
            "red": self.quit,
            "green": self.getStreamTypes,
            "cancel": self.quit,
            "ok": self.getStreamTypes,
            "yellow": self.deleteServer,
            "blue": self.autoDeleteInvalid,
            "0": self.goTop,
            "info": self.checkXtream,
        }, -2)

        self.timezone = get_local_timezone()

        self.onFirstExecBegin.append(self.start)
        self.onLayoutFinish.append(self.__layoutFinished)

    def __layoutFinished(self):
        self.setTitle(self.setup_title)

    def start(self, answer=None):
        loadfiles.process_files()

        # check if playlists.json file exists in specified location
        if os.path.isfile(self.playlists_json):
            with open(self.playlists_json, "r") as f:
                try:
                    self.playlists_all = json.load(f)
                    self.playlists_all.sort(key=lambda e: e["playlist_info"]["index"], reverse=False)
                except Exception:
                    os.remove(self.playlists_json)

        if self.playlists_all and os.path.isfile(self.playlist_file) and os.path.getsize(self.playlist_file) > 0:
            self.delayedDownload()
        else:
            self.close()

    def delayedDownload(self):
        self.timer = eTimer()
        try:
            self.timer_conn = self.timer.timeout.connect(self.makeUrlList)
        except Exception:
            try:
                self.timer.callback.append(self.makeUrlList)
            except Exception:
                self.makeUrlList()
        self.timer.start(10, True)

    def makeUrlList(self):
        self.url_list = []

        for index, playlist in enumerate(self.playlists_all):
            domain = str(playlist["playlist_info"].get("domain", ""))
            host = str(playlist["playlist_info"].get("host", "")).rstrip("/")
            mac = playlist["playlist_info"].get("mac", "").upper()

            if host and mac:
                self.url_list.append((index, mac, host, domain, self.timezone))

        if self.url_list:
            self.process_downloads()

    def _build_headers(self, domain, port, mac, timezone, referer):
        encoded_mac = quote(mac, safe='')
        encoded_timezone = quote(timezone, safe='')
        return {
            "Pragma": "no-cache",
            "Accept": "*/*",
            "Accept-Encoding": "gzip, deflate",
            "Host": "{}:{}".format(domain, port) if port else domain,
            "User-Agent": "Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 (KHTML, like Gecko) MAG200 stbapp ver: 2 rev: 250 Safari/533.3",
            "X-User-Agent": "Model: MAG250; Link: WiFi",
            "Connection": "keep-alive",
            "Referer": referer,
            "Cookie": "mac={}; stb_lang=en; timezone={}".format(encoded_mac, encoded_timezone),
        }

    def _get_path_prefix(self, http, host, headers, path_prefix):
        if path_prefix == "/stalker_portal/c/":
            primary_url = host + "/stalker_portal/c/"
            primary_prefix = "/stalker_portal/c/"
            fallback_url = host + "/c/"
            fallback_prefix = "/c/"
        elif path_prefix == "/c/":
            primary_url = host + "/c/"
            primary_prefix = "/c/"
            fallback_url = host + "/stalker_portal/c/"
            fallback_prefix = "/stalker_portal/c/"
        else:
            return path_prefix

        def try_url(url):
            try:
                with http.get(url, headers=headers, timeout=5, verify=False, stream=True, allow_redirects=True) as response:
                    response.raise_for_status()
                    return True
            except Exception:
                return False

        if try_url(primary_url):
            return primary_prefix

        if try_url(fallback_url):
            return fallback_prefix

        return primary_prefix

    def _get_portal_url(self, http, host, headers, path_prefix, portal):
        if portal:
            return portal

        if path_prefix == "/stalker_portal/c/":
            xpcom_urls = [
                host + "/stalker_portal/c/xpcom.common.js",
                host + "/c/xpcom.common.js",
            ]
        else:
            xpcom_urls = [
                host + "/c/xpcom.common.js",
                host + "/stalker_portal/c/xpcom.common.js",
            ]

        for url in xpcom_urls:
            try:
                with http.get(url, headers=headers, timeout=3, verify=False, stream=True, allow_redirects=True) as response:
                    response.raise_for_status()
                    portal_candidate = extract_portal_path_from_stream(response, url)

                    if portal_candidate:
                        if not portal_candidate.startswith("/"):
                            portal_candidate = "/" + portal_candidate

                        return host + portal_candidate

            except Exception as e:
                print("Error checking {}: {}".format(url, e))

        return host + "/portal.php"

    def _get_portal_version(self, http, host, headers, path_prefix):
        url = host + path_prefix + "version.js"

        try:
            with http.get(url, headers=headers, timeout=3, verify=False, allow_redirects=False) as response:
                response.raise_for_status()
                match = re.search(r"ver\s*=\s*['\"]([^'\"]+)['\"]", response.text)

                if match:
                    return match.group(1).strip()

        except Exception as e:
            print("Error getting portal version {}: {}".format(url, e))

        return ""

    def _format_expiry(self, expiry):
        if expiry == "Unlimited":
            return _("Unlimited")

        elif expiry and str(expiry).isdigit():
            return _("Unknown")

        return expiry or ""

    def download_url(self, url_info):
        index = url_info[0]
        mac = str(url_info[1]).strip().upper()
        host = url_info[2].rstrip("/")
        domain = url_info[3]
        timezone = url_info[4]

        playlist_info = self.playlists_all[index]["playlist_info"]
        portal = playlist_info.get("portal", "")
        path_prefix = playlist_info.get("path_prefix", "")
        portal_version = playlist_info.get("version", "")
        original_url = playlist_info.get("url", "")
        port = playlist_info.get("port", "")

        with requests.Session() as http:
            adapter = HTTPAdapter(max_retries=0)
            http.mount("http://", adapter)
            http.mount("https://", adapter)

            referer = os.path.join(original_url, "index.html")
            headers = self._build_headers(domain, port, mac, timezone, referer)

            # Stage 1
            path_prefix = self._get_path_prefix(http, host, headers, path_prefix)

            # Stage 2
            portal = self._get_portal_url(http, host, headers, path_prefix, portal)

            # Stage 3
            portal_version = self._get_portal_version(http, host, headers, path_prefix)

            # Stage 4
            portal, token, token_random, headers = perform_handshake(portal, host, mac, headers, http=http)

            if not token:
                return index, {"valid": False}

            # Stage 5
            play_token, status, blocked, returned_mac, returned_id = get_profile_data(portal, mac, token, token_random, headers, "full", http=http)

            # Stage 6
            expiry, account_valid = get_account_info(portal, headers, http=http, unknown_value=_("Unknown"))

        if not account_valid:
            play_token, status, blocked, returned_mac, returned_id = get_profile_data(portal, mac, token, token_random, headers, "basic")
            expiry, account_valid = get_account_info(portal, headers, http=http, unknown_value=_("Unknown"))

        if not account_valid:
            return index, {"valid": False}
        else:

            valid = True
            if not token:
                valid = False

            if str(blocked) == "1":
                valid = False

        expiry = self._format_expiry(expiry)

        return index, {
            "portal": portal,
            "version": portal_version,
            "token": token or "",
            "token_random": token_random or "",
            "valid": valid,
            "expiry": expiry,
            "play_token": play_token or "",
            "status": status,
            "blocked": blocked,
            "path_prefix": path_prefix,
            "active_connections": "",
            "max_connections": "",
            "headers": headers or ""
        }

    def _get_download_domain(self, url_info):
        domain = str(url_info[3] or "").strip().lower().rstrip(".")
        if domain:
            return domain

        host = str(url_info[2] or "").strip()
        try:
            parsed_host = urlparse(host)
            domain = parsed_host.hostname or parsed_host.netloc
        except Exception:
            domain = host

        # Keep entries without a parsed domain grouped by their complete host.
        return str(domain or host).strip().lower().rstrip("/")

    def _build_domain_rounds(self):
        domain_queues = OrderedDict()

        for position, url_info in enumerate(self.url_list):
            domain = self._get_download_domain(url_info)
            domain_queues.setdefault(domain, deque()).append((position, url_info))

        rounds = []
        while True:
            current_round = []

            # Take no more than one download from each domain per round.
            for domain_queue in domain_queues.values():
                if domain_queue:
                    current_round.append(domain_queue.popleft())

            if not current_round:
                break

            rounds.append(current_round)

        return rounds

    def _download_url_safe(self, download_item):
        position, url_info = download_item
        try:
            return position, self.download_url(url_info)
        except Exception as e:
            print("Error processing URL {}: {}".format(position, e))
            return position, (url_info[0], {"valid": False})

    def _process_rounds_sequentially(self, download_rounds, results):
        for current_round in download_rounds:
            for download_item in current_round:
                position = download_item[0]
                if results[position] is not None:
                    continue

                result_position, result = self._download_url_safe(download_item)
                results[result_position] = result

    def process_downloads(self):
        max_threads = 30
        download_rounds = self._build_domain_rounds()
        domain_count = len(download_rounds[0]) if download_rounds else 0
        threads = min(domain_count, max_threads)
        results = [None] * len(self.url_list)

        if hasConcurrent and threads:
            # print("*** hasConcurrent ***")
            try:
                from concurrent.futures import ThreadPoolExecutor, as_completed

                with ThreadPoolExecutor(max_workers=threads) as executor:
                    for current_round in download_rounds:
                        future_to_item = {
                            executor.submit(self.download_url, url_info): (position, url_info)
                            for position, url_info in current_round
                        }

                        # Finish the whole domain round before reusing any domain.
                        for future in as_completed(future_to_item):
                            position, url_info = future_to_item[future]
                            try:
                                results[position] = future.result()
                            except Exception as e:
                                print("Error processing URL {}: {}".format(position, e))
                                results[position] = (url_info[0], {"valid": False})

            except Exception as e:
                print("Concurrent execution error:", e)
                self._process_rounds_sequentially(download_rounds, results)

        elif hasMultiprocessing and threads:
            # print("*** Multiprocessing ***")
            try:
                from multiprocessing.pool import ThreadPool

                pool = ThreadPool(threads)
                try:
                    for current_round in download_rounds:
                        # imap completes this round before the next domain item.
                        for position, result in pool.imap(self._download_url_safe, current_round):
                            results[position] = result
                finally:
                    pool.close()
                    pool.join()

            except Exception as e:
                print("Multiprocessing execution error:", e)
                self._process_rounds_sequentially(download_rounds, results)
        else:
            # print("*** fallback sequential ***")
            self._process_rounds_sequentially(download_rounds, results)

        self.update_results(results)

    def update_results(self, results):
        for result in results:
            if not result:
                continue

            index, response = result
            try:
                if response:
                    self.playlists_all[index]["playlist_info"].update({
                        "portal": response.get("portal", ""),
                        "version": response.get("version", ""),
                        "token": response.get("token", ""),
                        "token_random": response.get("token_random", ""),
                        "valid": response.get("valid", False),
                        "expiry": response.get("expiry", ""),
                        "play_token": response.get("play_token", ""),
                        "status": response.get("status", 0),
                        "blocked": response.get("blocked", "0"),
                        "path_prefix": response.get("path_prefix", ""),
                        "active_connections": response.get("active_connections", ""),
                        "max_connections": response.get("max_connections", ""),
                        "headers": response.get("headers", ""),
                        "params": response.get("params", ""),

                    })
                else:
                    self.playlists_all[index]["playlist_info"].update({
                        "portal": "",
                        "version": "",
                        "token": "",
                        "token_random": "",
                        "valid": False,
                        "expiry": "",
                        "play_token": "",
                        "status": 0,
                        "blocked": "0",
                        "path_prefix": "",
                        "active_connections": "",
                        "max_connections": "",
                    })
            except Exception as e:
                print(e)

        self.writeJsonFile()
        self.createSetup()

    def writeJsonFile(self):
        with open(self.playlists_json, "w") as f:
            json.dump(self.playlists_all, f, indent=4)

    def createSetup(self):
        self["splash"].hide()
        self.list = []

        for index, playlist in enumerate(self.playlists_all):
            info = playlist["playlist_info"]
            domain = info.get("domain", "")
            url = info.get("host", "")
            mac = info.get("mac", "")
            token = info.get("token", "")
            expiry = info.get("expiry", "")
            status = info.get("status", 0)
            blocked = info.get("blocked", "0")
            valid = info.get("valid", True)
            portal = info.get("portal", "")
            portal_version = info.get("version", "")
            alias = info.get("alias", "").strip()

            display_name = alias if alias else mac
            portalpath = "stalker_portal" if "stalker" in portal else ""
            portal_label = str(_("Portal Version:"))
            status_label = str(_("Status:"))
            expires = str(expiry)

            message = _("Active")
            parsed_date = parse_date_safe(expiry)

            if parsed_date and parsed_date < datetime.now():
                message = _("Expired")
            elif not valid:
                message = _("Not active")
            elif blocked == "1":
                message = _("Blocked")
            elif "stalker" not in portal and str(status) != "0" and expiry:
                message = _("Unknown")

            self.list.append([index, domain, url, expires, message, display_name, token, portal_version, portal_label, valid, status, status_label, portalpath])

        self.drawList = [self.buildListEntry(*x) for x in self.list]
        self["playlists"].setList(self.drawList)

        if len(self.list) == 1 and cfg.skipplaylistsscreen.value:
            self.getStreamTypes()

    def buildListEntry(self, index, domain, url, expires, message, mac, token, portal_version, portal_label, valid, status, status_label, portalpath):
        if message == _("Expired"):
            pixmap_file = "led_blue.png"
        elif not valid or message not in (_("Active"), _("Unknown")):
            pixmap_file = "led_red.png"
        elif message == _("Active"):
            pixmap_file = "led_green.png"
        else:
            pixmap_file = "led_yellow.png"

        pixmap = LoadPixmap(cached=True, path=os.path.join(common_path, pixmap_file))
        return (index, str(domain), str(url), str(expires), str(message), pixmap, str(mac), str(portal_version), str(portal_label), str(status), str(status_label), str(portalpath))

    def quit(self, answer=None):
        try:
            self.timer.stop()
        except Exception:
            pass
        self.close()

    def deleteServer(self, answer=None):
        if not self.list:
            return

        self.currentplaylist = glob.active_playlist.copy()

        if answer is None:
            self.session.openWithCallback(self.deleteServer, MessageBox, _("Delete selected server (MAC) entry?"))
            return

        if not answer:
            return

        url_to_delete = str(self.currentplaylist["playlist_info"]["url"]).strip().rstrip('/')
        mac_to_delete = str(self.currentplaylist["playlist_info"]["mac"]).strip().lower()

        with open(self.playlist_file, "r") as f:
            lines = f.readlines()

        new_lines = []
        inside_block = False

        for line in lines:
            stripped = line.strip()
            if stripped.startswith(("http://", "https://")):
                current_url = stripped.rstrip('/')
                inside_block = (current_url == url_to_delete)
                new_lines.append(line)
                continue

            if inside_block and stripped.lower() == mac_to_delete:
                new_lines.append("#" + line)
            else:
                new_lines.append(line)

        with open(self.playlist_file, "w") as f:
            f.writelines(new_lines)

        for i, playlist in enumerate(self.playlists_all):
            playlist_url = playlist.get("playlist_info", {}).get("url", "").strip().rstrip('/')
            playlist_mac = playlist.get("playlist_info", {}).get("mac", "").strip().lower()
            if playlist_url == url_to_delete and playlist_mac == mac_to_delete:
                del self.playlists_all[i]
                break

        # After the loop, re-index the remaining entries
        for idx, playlist in enumerate(self.playlists_all):
            playlist["playlist_info"]["index"] = idx

        glob.current_selection = min(glob.current_selection, len(self.playlists_all) - 1)
        if glob.current_selection >= 0:
            glob.active_playlist = self.playlists_all[glob.current_selection]
        else:
            glob.current_selection = 0
            glob.active_playlist = {}

        self.writeJsonFile()
        self.createSetup()

    def getCurrentEntry(self):
        if self.list:
            glob.current_selection = self["playlists"].getIndex()
            glob.active_playlist = self.playlists_all[glob.current_selection]

            num_playlists = self["playlists"].count()
            if num_playlists > 5:
                self["scroll_up"].show()
                self["scroll_down"].show()

                if glob.current_selection < 5:
                    self["scroll_up"].hide()
                elif glob.current_selection + 1 > ((num_playlists // 5) * 5):
                    self["scroll_down"].hide()
        else:
            glob.current_selection = 0
            glob.active_playlist = {}

    def getStreamTypes(self):
        if glob.active_playlist["playlist_info"]["valid"] is True:
            glob.current_selection = self["playlists"].getIndex()
            glob.active_playlist = self.playlists_all[glob.current_selection]
            from . import menu
            self.session.openWithCallback(self.checkoneplaylist, menu.EStalker_Menu)

    def checkoneplaylist(self, answer=None):
        if len(self.list) == 1 and cfg.skipplaylistsscreen.value is True:
            self.quit()

    def goTop(self):
        self["playlists"].setIndex(0)

    def autoDeleteInvalid(self, answer=None):
        if answer is None:
            self.session.openWithCallback(
                self.autoDeleteInvalid,
                MessageBox,
                _(
                    "Delete ALL invalid playlists?\n"
                    "(Those marked as Not Active/Blocked/Expired)"
                ),
                MessageBox.TYPE_YESNO
            )
            return

        if not answer:
            return

        with open(self.playlist_file, "r") as f:
            lines = f.readlines()

        macs_to_keep = {
            playlist["playlist_info"]["mac"].strip().lower()
            for playlist in self.playlists_all
            if playlist["playlist_info"].get("valid", False)
        }

        mac_regex = re.compile(
            r"^([0-9A-Fa-f]{2}:){5}[0-9A-Fa-f]{2}$"
        )

        new_lines = []
        current_url = None

        for line in lines:
            stripped = line.strip()

            if stripped.startswith(("http://", "https://")):
                current_url = stripped
                new_lines.append(line)
                continue

            if not stripped or current_url is None:
                new_lines.append(line)
                continue

            was_commented = stripped.startswith("#")
            content = stripped.lstrip("#").strip()

            if "#" in content:
                mac_part, comment_part = content.split("#", 1)
                mac_part = mac_part.strip()
                comment_part = comment_part.strip()
            else:
                mac_part = content.strip()
                comment_part = ""

            if not mac_regex.match(mac_part):
                new_lines.append(line)
                continue

            if mac_part.lower() in macs_to_keep:
                prefix = "# " if was_commented else ""

                if comment_part:
                    new_lines.append(
                        "{}{} #{}\n".format(
                            prefix,
                            mac_part.upper(),
                            comment_part
                        )
                    )
                else:
                    new_lines.append(
                        "{}{}\n".format(
                            prefix,
                            mac_part.upper()
                        )
                    )
            else:
                if comment_part:
                    new_lines.append(
                        "# {} #{}\n".format(
                            mac_part.upper(),
                            comment_part
                        )
                    )
                else:
                    new_lines.append(
                        "# {}\n".format(mac_part.upper())
                    )

        with open(self.playlist_file, "w") as f:
            f.writelines(new_lines)

        self.playlists_all = [
            playlist
            for playlist in self.playlists_all
            if playlist["playlist_info"].get("valid", False)
        ]

        for index, playlist in enumerate(self.playlists_all):
            playlist["playlist_info"]["index"] = index

        self.writeJsonFile()
        self.createSetup()

        self.session.open(
            MessageBox,
            _("Removed all invalid playlists"),
            MessageBox.TYPE_INFO,
            timeout=3
        )

    def checkXtream(self):
        self.session.open(EStalker_UserInfo)


class EStalker_UserInfo(Screen):
    ALLOW_SUSPEND = True

    def __init__(self, session):
        Screen.__init__(self, session)
        self.session = session

        skin_path = os.path.join(skin_directory, cfg.skin.value)
        skin = os.path.join(skin_path, "userinfo.xml")
        with open(skin, "r") as f:
            self.skin = f.read()

        self.setup_title = _("User Information")
        self.playlists_all = []

        self["portalversion"] = Label(_("Unavailable"))
        self["portalurl"] = Label(_("Unavailable"))
        self["portalcalls"] = Label(_("Unavailable"))
        self["status"] = Label("-")
        self["expiry"] = Label("-")
        self["created"] = Label("-")
        self["trial"] = Label("-")
        self["activeconn"] = Label("-")
        self["maxconn"] = Label("-")

        self["t_portalversion"] = StaticText(_("Portal Version:"))
        self["t_portalurl"] = StaticText(_("Portal URL:"))
        self["t_portalcalls"] = StaticText(_("Portal API Calls:"))
        self["t_status"] = StaticText(_("Status:"))
        self["t_expiry"] = StaticText(_("Expiry Date:"))
        self["t_created"] = StaticText(_("Created At:"))
        self["t_trial"] = StaticText(_("Is Trial:"))
        self["t_activeconn"] = StaticText(_("Active Connections:"))
        self["t_maxconn"] = StaticText(_("Max Connections:"))

        self["actions"] = ActionMap(["EStalkerActions"], {
            "ok": self.quit,
            "cancel": self.quit,
            "red": self.quit,
            "menu": self.quit,
        }, -2)

        self["key_red"] = StaticText(_("Close"))

        self.onFirstExecBegin.append(self.createUserSetup)
        self.onLayoutFinish.append(self.__layoutFinished)

    def __layoutFinished(self):
        self.setTitle(self.setup_title)

    def createUserSetup(self):
        playlist_info = glob.active_playlist.get("playlist_info", {})
        self["portalversion"].setText(str(playlist_info.get("version", "Unknown")))
        self["portalurl"].setText(str(playlist_info.get("path_prefix", "Unknown")))
        portaltext = str(playlist_info.get("portal", "")).replace(playlist_info.get("host", ""), "")
        self["portalcalls"].setText(portaltext)
        self["status"].setText(str(playlist_info.get("status", "")))
        self["expiry"].setText(str(playlist_info.get("expiry", "Unknown")))

        self.get_stream_url()

    def _build_mag_headers(self, domain, port, mac, timezone, referer):
        encoded_mac = quote(mac, safe='')
        encoded_timezone = quote(timezone, safe='')
        return {
            "Pragma": "no-cache",
            "Accept-Language": "en-US,en;q=0.5",
            "Accept-Encoding": "gzip, deflate",
            "Host": "{}:{}".format(domain, port) if port else domain,
            "User-Agent": "Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 (KHTML, like Gecko) MAG200 stbapp ver: 2 rev: 250 Safari/533.3",
            "X-User-Agent": "Model: MAG250; Link: WiFi",
            "Connection": "Close",
            "Referer": referer,
            "Cookie": "mac={}; stb_lang=en; timezone={}".format(encoded_mac, encoded_timezone),
        }

    def _fetch_xtream_creds(self, portal, headers, content_type, domain):
        try:
            list_url = "{}?type={}&action=get_ordered_list&genre=*&JsHttpRequest=1-xml".format(portal, content_type)
            data = make_request(list_url, method="GET", headers=headers, params=None, response_type="json")

            if not data:
                return {}

            js_data = data.get("js") or {}
            data_list = js_data.get("data") or []

            first_item = next((v for v in data_list if isinstance(v, dict) and v.get("cmd")), None)
            if not first_item:
                return {}

            cmd_val = first_item.get("cmd", "")
            if str(cmd_val).startswith("/media/"):
                cmd_val = cmd_val.replace("/media/", "/media/file_")

            create_link_url = "{}?type={}&action=create_link&cmd={}&series=&forced_storage=&disable_ad=0&download=0&force_ch_link_check=0&JsHttpRequest=1-xml".format(
                portal, content_type, cmd_val
            )

            link_data = make_request(create_link_url, method="GET", headers=headers, params=None, response_type="json")
            if not link_data:
                return {}

            cmd = (link_data.get("js") or {}).get("cmd")
            if not cmd:
                return {}

            stream_url = str(cmd)
            parsed = urlparse(stream_url)
            if parsed.scheme in ["http", "https"]:
                stream_url = parsed.geturl()

            match = re.search(r'/movie/([^/]+)/([^/]+)/', stream_url)
            if match:
                return {"username": match.group(1), "password": match.group(2)}

        except Exception as e:
            print("Error fetching Xtream creds:", e, domain)

        return {}

    def get_stream_url(self):
        portal = glob.active_playlist["playlist_info"]["portal"]
        domain = glob.active_playlist["playlist_info"]["domain"]
        mac = glob.active_playlist["playlist_info"]["mac"]
        timezone = get_local_timezone()
        port = glob.active_playlist["playlist_info"]["port"]
        original_url = glob.active_playlist["playlist_info"]["url"]
        referer = os.path.join(original_url, "index.html")

        headers = self._build_mag_headers(domain, port, mac, timezone, referer)

        # Try VOD first, then live
        xtream_creds = self._fetch_xtream_creds(portal, headers, "vod", domain)
        if not xtream_creds.get("username") or not xtream_creds.get("password"):
            xtream_creds = self._fetch_xtream_creds(portal, headers, "itv", domain)

        if xtream_creds.get("username") and xtream_creds.get("password"):
            self.fetch_xtream_api(xtream_creds)

    def fetch_xtream_api(self, xtream_creds):
        username = xtream_creds.get("username", "")
        password = xtream_creds.get("password", "")
        host = glob.active_playlist["playlist_info"]["host"]
        index = glob.active_playlist["playlist_info"]["index"]
        expiry = glob.active_playlist["playlist_info"]["expiry"]
        status = glob.active_playlist["playlist_info"]["status"]

        active_cons = ""
        max_cons = ""
        created_at = ""
        is_trial = ""

        if username and password and len(password) != 32:
            time.sleep(3)
            api_url = host.rstrip("/") + "/player_api.php?username={}&password={}".format(username, password)
            api_data = xtream_request(api_url)

            if api_data and 'user_info' in api_data:
                user_info = api_data['user_info']
                active_cons = str(user_info.get('active_cons', ""))
                max_cons = str(user_info.get('max_connections', ""))

                if user_info.get('auth') == 1:
                    status_map = {
                        "Active": _("Active"),
                        "Banned": _("Banned"),
                        "Disabled": _("Disabled"),
                        "Expired": _("Expired"),
                    }
                    status = status_map.get(user_info.get("status"), _("Unknown"))
                    is_trial = user_info.get('is_trial', "")

                created_at = self._format_timestamp(user_info.get('created_at'))
                expiry = self._format_timestamp(user_info.get('exp_date')) or expiry

        self["status"].setText(str(status))
        self["expiry"].setText(str(expiry))
        self["created"].setText(str(created_at))
        self["trial"].setText(str(is_trial))
        self["activeconn"].setText(str(active_cons))
        self["maxconn"].setText(str(max_cons))

        self.update_results(index, expiry, active_cons, max_cons)

    def _format_timestamp(self, timestamp):
        try:
            ts = int(timestamp)
            if ts > 0:
                dt = datetime.fromtimestamp(ts)
                hour = dt.hour % 12 or 12
                ampm = 'am' if dt.hour < 12 else 'pm'
                return dt.strftime('%B %d, %Y, ') + '{:d}:{:02d} {}'.format(hour, dt.minute, ampm)
        except (ValueError, TypeError):
            pass
        return ""

    def update_results(self, index, expiry, active_cons, max_cons):
        with open(self.playlists_json, "r") as f:
            self.playlists_all = json.load(f)

        self.playlists_all[index]["playlist_info"].update({
            "expiry": expiry,
            "active_connections": active_cons,
            "max_connections": max_cons,
        })

        self.writeJsonFile()

    def writeJsonFile(self):
        try:
            with open(self.playlists_json, "w") as f:
                json.dump(self.playlists_all, f, indent=4)
        except Exception as e:
            print("Error writing JSON:", e)

    def quit(self):
        self.close()
