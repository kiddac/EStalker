#!/usr/bin/python
# -*- coding: utf-8 -*-

# Standard library imports
from __future__ import division

import json
import os
import re
import socket
import time

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
from .plugin import skin_directory, cfg, common_path, version, hasConcurrent, hasMultiprocessing, debugs
from .eStaticText import StaticText
from .utils import get_local_timezone, make_request, xtream_request, perform_handshake, get_profile_data
from . import processfiles as loadfiles

try:
    from urllib import quote
except ImportError:
    from urllib.parse import quote


playlist_file = cfg.playlist_file.value
playlists_json = cfg.playlists_json.value

try:
    basestring
except NameError:
    basestring = str


# ########################################################################################
# Module-level helper functions
# ########################################################################################


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


def check_internet():
    for host in ("1.1.1.1", "8.8.8.8"):
        try:
            conn = socket.create_connection((host, 53), 2)
            conn.close()
            return True
        except OSError:
            continue
    return False


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


# ########################################################################################
# EStalker_Playlists Screen
# ########################################################################################


class EStalker_Playlists(Screen):
    ALLOW_SUSPEND = True

    def __init__(self, session):
        Screen.__init__(self, session)
        self.session = session

        skin_path = os.path.join(skin_directory, cfg.skin.value)
        skin = os.path.join(skin_path, "playlists.xml")
        with open(skin, "r") as f:
            self.skin = f.read()

        self.setup_title = _("Manage Playlists")

        self["key_red"] = StaticText(_("Back"))
        self["key_green"] = StaticText(_("OK"))
        self["key_yellow"] = StaticText(_("Delete"))
        self["key_blue"] = StaticText(_("Auto Delete"))
        self["version"] = StaticText(version)

        self.list = []
        self.drawList = []
        self.playlists_all = []

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
        """
        if debugs:
            print("*** start ***")
            print("")
            """

        loadfiles.process_files()

        if not check_internet():
            self.session.openWithCallback(self.quit, MessageBox, _("No internet."), type=MessageBox.TYPE_ERROR, timeout=5)
            return

        # check if playlists.json file exists in specified location
        if os.path.isfile(playlists_json):
            with open(playlists_json, "r") as f:
                try:
                    self.playlists_all = json.load(f)
                    self.playlists_all.sort(key=lambda e: e["playlist_info"]["index"], reverse=False)
                except Exception:
                    os.remove(playlists_json)

        if self.playlists_all and os.path.isfile(playlist_file) and os.path.getsize(playlist_file) > 0:
            self.delayedDownload()
        else:
            self.close()

    def delayedDownload(self):
        """
        if debugs:
            print("*** delayedDownload ***")
            print("")
            """

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
        """
        if debugs:
            print("*** makeUrlList ***")
            print("")
            """

        self.url_list = []

        for index, playlist in enumerate(self.playlists_all):
            domain = str(playlist["playlist_info"].get("domain", ""))
            host = str(playlist["playlist_info"].get("host", "")).rstrip("/")
            mac = playlist["playlist_info"].get("mac", "").upper()

            if host and mac:
                self.url_list.append((index, mac, host, domain, self.timezone))

        if self.url_list:
            """
            if debugs:
                print("*** self.url_list ***", self.url_list)
                """
            self.process_downloads()

    # ########################################################################################
    # Download helpers - broken out from download_url
    # ########################################################################################

    def _build_headers(self, domain, port, mac, timezone, referer):
        """Build standard MAG headers."""

        """
        if debugs:
            print("*** _build_headers ***")
            print("")
            """

        encoded_mac = quote(mac, safe='')
        encoded_timezone = quote(timezone, safe='')
        return {
            "Pragma": "no-cache",
            "Accept": "*/*",
            "Accept-Encoding": "gzip, deflate",
            "Host": "{}:{}".format(domain, port) if port else domain,
            "User-Agent": "Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 (KHTML, like Gecko) MAG200 stbapp ver: 2 rev: 250 Safari/533.3",
            "X-User-Agent": "Model: MAG250; Link: WiFi",
            "Connection": "CLose",
            "Referer": referer,
            "Cookie": "mac={}; stb_lang=en; timezone={}".format(encoded_mac, encoded_timezone),
        }

    def _get_path_prefix(self, http, host, headers, path_prefix):
        """Stage 1: Determine the correct portal path prefix."""
        """
        if debugs:
            print("*** _get_path_prefix ***")
            """

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
            # print("*** trying url ***", url)
            try:
                with http.get(url, headers=headers, timeout=(3, 5), verify=False, allow_redirects=True) as r:
                    r.raise_for_status()
                    #  print("*** success ***", url)
                    return True
            except Exception as e:
                print("Error checking {}: {}".format(url, e))
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
                with http.get(url, headers=headers, timeout=(3, 5), verify=False, stream=True, allow_redirects=True) as r:
                    r.raise_for_status()
                    portal_candidate = extract_portal_path_from_stream(r, url)
                    if portal_candidate:
                        if not portal_candidate.startswith("/"):
                            portal_candidate = "/" + portal_candidate
                        return host + portal_candidate
            except Exception as e:
                print("Error checking {}: {}".format(url, e))
                continue

        return host + "/portal.php"

    def _get_portal_version(self, http, host, headers, path_prefix):
        """Stage 3: Get portal version from version.js."""

        """
        if debugs:
            print("*** _get_portal_version ***")
            print("")
            """

        version_url = host + path_prefix + "version.js"
        # new_referer = host + path_prefix + "index.html"
        # headers["Referer"] = new_referer

        vresponse = make_request(version_url, method="GET", headers=headers, params=None, response_type="text")
        if vresponse:
            match = re.search(r"ver\s*=\s*['\"]([^'\"]+)['\"]", vresponse)
            if match:
                portal_version = match.group(1).strip()
                """
                if debugs:
                    print("*** portal_version ***", portal_version)
                    """
                return portal_version
        return path_prefix

    def _do_handshake(self, portal, host, mac, headers):
        """Stage 4: Perform handshake and return updated portal, token, token_random, headers."""

        """
        if debugs:
            print("*** _do_handshake ***")
            print("")
            """

        return perform_handshake(portal, host, mac, headers)

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

    def _format_expiry(self, expiry):
        """Normalise expiry string."""
        if expiry == "Unlimited":
            return _("Unlimited")

        elif expiry and str(expiry).isdigit():
            return _("Unknown")

        return expiry or ""

    def download_url(self, url_info):
        """Orchestrate all stages to retrieve playlist info for a single entry."""

        """
        if debugs:
            print("*** download_url ***")
            print("")
            """

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

            """
            if path_prefix is None:
                return index, {"valid": False, "expiry": _("Invalid Domain")}

            # Add this — if we got no useful path back, the server is dead
            if not path_prefix:
                return index, {"valid": False, "expiry": _("Invalid Domain")}
                """

            """
            if debugs:
                print("*** path_prefix ***", path_prefix)
                """
            """
            if path_prefix is None:
                return index, {"valid": False, "expiry": _("Invalid Domain")}
                """

            # Stage 2
            portal = self._get_portal_url(http, host, headers, path_prefix, portal)

            if debugs:
                print("*** portal ***", portal)

            # Stage 3
            portal_version = self._get_portal_version(http, host, headers, path_prefix)

            if debugs:
                print("*** portal_version ***", portal_version)

            # Stage 4
            portal, token, token_random, headers = self._do_handshake(portal, host, mac, headers)

            if debugs:
                print("*** portal ***", portal)
                print("*** token ***", token)
                print("*** token_random ***", token_random)
                print("*** headers ***", headers)

            if not token:
                return index, {"valid": False}

            # Stage 5
            play_token, status, blocked, returned_mac, returned_id = self._get_profile(portal, mac, token, token_random, headers, "full")
            # stored_id = returned_id

            if debugs:
                print("*** play_token ***", play_token)
                print("*** status ***", status)
                print("*** blocked ***", blocked)
                print("*** returned_mac ***", returned_mac)
                print("*** returned_id ***", returned_id)

            # Stage 6
            expiry, account_valid = self._get_account_info(portal, mac, token, token_random, headers)

            if not account_valid:
                if debugs:
                    print("*** retrying with no params ***")
                play_token, status, blocked, returned_mac, returned_id = self._get_profile(portal, mac, token, token_random, headers, "basic")
                # stored_id = returned_id
                # print("*** stored_id 2 ***", stored_id)

                if debugs:
                    print("*** play_token2 ***", play_token)
                    print("*** status2 ***", status)
                    print("*** blocked2 ***", blocked)
                    print("*** returned_mac2 ***", returned_mac)
                    print("*** returned_id2 ***", returned_id)

                expiry, account_valid = self._get_account_info(portal, mac, token, token_random, headers)

            if not account_valid:
                return index, {"valid": False}
            else:

                valid = True
                if not token:
                    valid = False

                # if not returned_id:
                    # valid = False

                # if str(returned_id) == "0":
                    # valid = False

                if str(blocked) == "1":
                    valid = False

                # if "stalker" not in portal:
                #   if not expiry and status != 0:
                #       valid = False

            if debugs:
                print("*** valid ***", valid)

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

    # ########################################################################################
    # Processing and results
    # ########################################################################################

    def process_downloads(self):
        """
        if debugs:
            print("*** process_downloads ***")
            """

        threads = min(len(self.url_list), 10)
        results = []

        if hasConcurrent:
            # print("*** hasConcurrent ***")
            try:
                from concurrent.futures import ThreadPoolExecutor, as_completed

                with ThreadPoolExecutor(max_workers=threads) as executor:
                    future_to_index = {
                        executor.submit(self.download_url, url_info): idx
                        for idx, url_info in enumerate(self.url_list)
                    }

                    results = [None] * len(self.url_list)

                    for future in as_completed(future_to_index):
                        idx = future_to_index[future]
                        try:
                            results[idx] = future.result()
                        except Exception as e:
                            print("Error processing URL {}: {}".format(idx, e))
                            results[idx] = (idx, {"valid": False})

            except Exception as e:
                print("Concurrent execution error:", e)
                results = []
                for idx, url_info in enumerate(self.url_list):
                    try:
                        results.append(self.download_url(url_info))
                    except Exception as e:
                        print("Error processing URL {}: {}".format(idx, e))
                        results.append((idx, {"valid": False}))

        elif hasMultiprocessing:
            # print("*** Multiprocessing ***")
            try:
                from multiprocessing.pool import ThreadPool

                pool = ThreadPool(threads)
                try:
                    results = list(pool.imap(self.download_url, self.url_list))
                finally:
                    pool.close()
                    pool.join()

            except Exception as e:
                print("Multiprocessing execution error:", e)
                results = []
                for url_info in self.url_list:
                    try:
                        results.append(self.download_url(url_info))
                    except Exception as e:
                        print("Error processing URL:", e)
                        results.append((0, {"valid": False}))
        else:
            # print("*** fallback sequential ***")
            for url_info in self.url_list:
                try:
                    results.append(self.download_url(url_info))
                except Exception as e:
                    print("Error processing URL:", e)
                    results.append((0, {"valid": False}))

        self.update_results(results)

    def update_results(self, results):

        """
        if debugs:
            print("*** update_results ***")
            print("")
            """

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
        """
        if debugs:
            print("*** writeJsonFile ***")
            """

        with open(playlists_json, "w") as f:
            json.dump(self.playlists_all, f, indent=4)

    # ########################################################################################
    # UI setup
    # ########################################################################################

    def createSetup(self):
        """
        if debugs:
            print("*** createSetup ***")
            """

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

            # if expiry == _("Invalid Domain"):
            #     message = _("Invalid Domain")

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
        if not valid or message not in (_("Active"), _("Unknown"), _("Expired")):
            pixmap_file = "led_red.png"
        elif message == _("Active"):
            pixmap_file = "led_green.png"
        else:
            pixmap_file = "led_yellow.png"

        pixmap = LoadPixmap(cached=True, path=os.path.join(common_path, pixmap_file))
        return (index, str(domain), str(url), str(expires), str(message), pixmap, str(mac), str(portal_version), str(portal_label), str(status), str(status_label), str(portalpath))

    # ########################################################################################
    # Actions
    # ########################################################################################

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

        with open(playlist_file, "r") as f:
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

        with open(playlist_file, "w") as f:
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
            self.session.openWithCallback(self.autoDeleteInvalid, MessageBox, _("Delete ALL invalid playlists?\n(Those marked as Not Active/Blocked/Expired)"), MessageBox.TYPE_YESNO)
            return

        if not answer:
            return

        with open(playlist_file, "r") as f:
            lines = [line.strip() for line in f]

        macs_to_keep = {
            playlist["playlist_info"]["mac"].lower()
            for playlist in self.playlists_all
            if playlist["playlist_info"].get("valid", False)
        }

        new_lines = []
        current_url = None

        for line in lines:
            if line.startswith(("http://", "https://")):
                current_url = line
                new_lines.append(line)
            elif line and current_url:
                if line.lower() in macs_to_keep:
                    new_lines.append(line)
                else:
                    new_lines.append("#" + line)
            else:
                new_lines.append(line)

        with open(playlist_file, "w") as f:
            f.write("\n".join(new_lines) + "\n")

        self.playlists_all = [p for p in self.playlists_all if p["playlist_info"].get("valid", False)]

        for index, playlist in enumerate(self.playlists_all):
            playlist["playlist_info"]["index"] = index

        self.writeJsonFile()
        self.createSetup()

        self.session.open(MessageBox, _("Removed all invalid playlists"), MessageBox.TYPE_INFO, timeout=3)

    def checkXtream(self):
        self.session.open(EStalker_UserInfo)


# ########################################################################################
# EStalker_UserInfo Screen
# ########################################################################################

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
        """Build MAG headers for UserInfo requests."""
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
        """Attempt to extract Xtream credentials from a portal content list."""
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

        """
        if debugs:
            print("*** get_stream_url ***")
            """

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
        """
        if debugs:
            print("*** fetch_xtream_api ***")
            """

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
        """Convert a Unix timestamp to a human-readable date string."""
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
        with open(playlists_json, "r") as f:
            self.playlists_all = json.load(f)

        self.playlists_all[index]["playlist_info"].update({
            "expiry": expiry,
            "active_connections": active_cons,
            "max_connections": max_cons,
        })

        self.writeJsonFile()

    def writeJsonFile(self):
        """
        if debugs:
            print("*** writeJsonFile ***")
            """

        try:
            with open(playlists_json, "w") as f:
                json.dump(self.playlists_all, f, indent=4)
        except Exception as e:
            print("Error writing JSON:", e)

    def quit(self):
        self.close()
