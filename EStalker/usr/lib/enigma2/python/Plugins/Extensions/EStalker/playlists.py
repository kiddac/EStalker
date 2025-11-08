#!/usr/bin/python
# -*- coding: utf-8 -*-

# Standard library imports
from __future__ import division

import json
import os
import re
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
from . import checkinternet
from .utils import get_local_timezone, make_request, xtream_request, perform_handshake, get_profile_data
from . import processfiles as loadfiles

# from twisted.internet import reactor

playlist_file = cfg.playlist_file.value
playlists_json = cfg.playlists_json.value

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

    def clear_caches(self):
        if debugs:
            print("*** clear_caches ***")

        try:
            with open("/proc/sys/vm/drop_caches", "w") as drop_caches:
                drop_caches.write("1\n2\n3\n")
        except IOError:
            pass

    def __layoutFinished(self):
        self.setTitle(self.setup_title)

    def start(self):
        if debugs:
            print("*** start ***")

        loadfiles.process_files()

        self.checkinternet = checkinternet.check_internet()
        if not self.checkinternet:
            self.session.openWithCallback(self.quit, MessageBox, _("No internet."), type=MessageBox.TYPE_ERROR, timeout=5)

        self.playlists_all = []

        # check if playlists.json file exists in specified location
        if os.path.isfile(playlists_json):
            with open(playlists_json, "r") as f:
                try:
                    self.playlists_all = json.load(f)
                    self.playlists_all.sort(key=lambda e: e["playlist_info"]["index"], reverse=False)
                except:
                    os.remove(playlists_json)

        if self.playlists_all and os.path.isfile(playlist_file) and os.path.getsize(playlist_file) > 0:
            self.delayedDownload()
        else:
            self.close()

        self.clear_caches()

    def delayedDownload(self):
        if debugs:
            print("*** delayedDownload ***")

        self.timer = eTimer()
        try:
            self.timer_conn = self.timer.timeout.connect(self.makeUrlList)
        except:
            try:
                self.timer.callback.append(self.makeUrlList)
            except:
                self.makeUrlList()
        self.timer.start(10, True)

    def makeUrlList(self):
        if debugs:
            print("*** makeUrlList ***")

        self.url_list = []

        for index, playlist in enumerate(self.playlists_all):
            domain = str(playlist["playlist_info"].get("domain", ""))
            host = str(playlist["playlist_info"].get("host", "")).rstrip("/")
            mac = playlist["playlist_info"].get("mac", "").upper()

            if host and mac:
                self.url_list.append((None, index, mac, host, domain, self.timezone))

        if self.url_list:
            self.process_downloads()

    def download_url(self, url_info):
        index = url_info[1]
        mac = str(url_info[2]).strip().upper()
        host = url_info[3]
        domain = url_info[4]
        timezone = url_info[5]

        token = None
        play_token = None
        status = 0
        blocked = "0"
        expiry = ""
        portal_version = ""
        # xtream_creds = {}
        active_cons = ""
        max_cons = ""
        token_random = ""
        valid = True

        playlist_info = self.playlists_all[index]["playlist_info"]
        portal = playlist_info.get("portal", None)
        expiry = playlist_info.get("expiry", None)
        path_prefix = playlist_info.get("path_prefix", None)
        portal_version = playlist_info.get("version", "")
        # original_url = playlist_info.get("url")

        def extract_portal_path_from_stream(resp, url):
            try:
                portal_prefix = ""

                for line in resp.iter_lines():
                    try:
                        if isinstance(line, bytes):  # Python 3
                            line = line.decode("utf-8", "ignore")
                        elif not isinstance(line, str):  # Python 2 unicode
                            line = line.encode("utf-8")
                    except:
                        continue

                    line = line.strip()
                    if not line or "this.ajax_loader = this" not in line:
                        continue

                    if "this.portal_path" in line:
                        if '/stalker_portal/' in url:
                            portal_prefix = '/stalker_portal'
                        else:
                            portal_prefix = '/c'

                    # Pattern 1: this.portal_protocol+'://'+this.portal_ip+'/'+this.portal_path+'/server/load.php'
                    match = re.search(r'this\.portal_protocol\s*\+\s*[\'"]://[\'"]\s*\+\s*this\.portal_ip\s*\+\s*[\'"]/[\'"]\s*\+\s*this\.portal_path\s*\+\s*[\'"](/[^\'"]+)', line)

                    if not match:
                        # Pattern 2: this.portal_protocol+'://'+this.portal_ip+'/server/move.php'
                        match = re.search(r'this\.portal_protocol\s*\+\s*[\'"]://[\'"]\s*\+\s*this\.portal_ip\s*\+\s*[\'"](/[^\'"]+)', line)

                    if not match:
                        # Pattern 3: this.portal_ip+'/portal.php'
                        match = re.search(r'this\.portal_ip\s*\+\s*[\'"](/[^\'"]+)', line)

                    if match:
                        path = match.group(1)
                        path = portal_prefix + path  # Combine URL path with matched path
                        path = re.sub(r'/+', '/', path.strip())  # Normalize multiple slashes
                        return path

            except Exception as e:
                print("extract_portal_path_from_stream error:", e)

            return None

        with requests.Session() as http:
            adapter = HTTPAdapter(max_retries=0)
            http.mount("http://", adapter)
            http.mount("https://", adapter)

            # ########################################################################################
            # 1 - read web portal
            # ########################################################################################

            headers = {
                "Host": domain,
                "Accept": "*/*",
                "User-Agent": "Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 (KHTML, like Gecko) MAG250 stbapp ver: 2 rev: 369 Safari/533.3",
                "Accept-Encoding": "gzip, deflate",
                "X-User-Agent": "Model: MAG250; Link: WiFi",
                "Connection": "close",
                "Pragma": "no-cache",
                "Cache-Control": "no-store, no-cache, must-revalidate",
                "Cookie": "mac={}; stb_lang=en; timezone={};".format(mac, timezone),
            }

            if path_prefix == "/stalker_portal/c/":
                primary = host.rstrip("/") + "/stalker_portal/c/"
                fallback = host.rstrip("/") + "/c/"
            elif path_prefix == "/c/":
                primary = host.rstrip("/") + "/c/"
                fallback = host.rstrip("/") + "/stalker_portal/c/"
            else:
                primary = None
                fallback = None

            if primary:
                try:
                    r = http.get(primary, headers=headers, timeout=(6, 10), verify=False, allow_redirects=True)
                    r.raise_for_status()

                    final_url = r.url.lower()

                    if "version.js" in r.text.lower():
                        if "/stalker_portal/c/" in final_url:
                            # path_prefix = host.rstrip("/") + "/stalker_portal/c/"
                            path_prefix = "/stalker_portal/c/"

                        elif "/c/" in final_url:
                            # path_prefix = host.rstrip("/") + "/c/"
                            path_prefix = "/c/"

                except Exception as e:
                    print("Error checking primary {}: {}".format(primary, e))

            if not path_prefix and fallback:
                try:
                    r = http.get(fallback, headers=headers, timeout=(6, 10), verify=False, allow_redirects=True)
                    r.raise_for_status()

                    final_url = r.url.lower()

                    if "version.js" in r.text.lower():
                        if "/stalker_portal/c/" in final_url:
                            # path_prefix = host.rstrip("/") + "/stalker_portal/c/"
                            path_prefix = "/stalker_portal/c/"
                        elif "/c/" in final_url:
                            # path_prefix = host.rstrip("/") + "/c/"
                            path_prefix = "/c/"

                except Exception as e:
                    print("Error checking fallback {}: {}".format(fallback, e))

            if not path_prefix:
                path_prefix = "/c/"

            # Final result
            if debugs:
                if path_prefix is None:
                    print("Could not determine path_prefix.")
                else:
                    print("path_prefix {}".format(path_prefix))

            # ########################################################################################
            # 2 read xpcom.common.js file
            # ########################################################################################

            # portal = None

            if not portal:
                xpcom_url = host.rstrip("/") + path_prefix + "xpcom.common.js"

                try:
                    r = http.get(xpcom_url, headers=headers, timeout=(5, 10), verify=False, stream=False, allow_redirects=True)
                    r.raise_for_status()

                    portal_candidate = extract_portal_path_from_stream(r, xpcom_url)

                    if portal_candidate:
                        if not portal_candidate.startswith("/"):
                            portal_candidate = "/" + portal_candidate

                        portal = host.rstrip("/") + portal_candidate

                except Exception as e:
                    print("Error checking {}: {}".format(xpcom_url, e))

            if not portal:
                xpcom_urls = [
                    host.rstrip("/") + "/c/xpcom.common.js",
                    host.rstrip("/") + "/stalker_portal/c/xpcom.common.js",
                ]

                for url in xpcom_urls:
                    try:
                        r = http.get(url, headers=headers, timeout=(5, 10), verify=False, stream=False, allow_redirects=True)
                        r.raise_for_status()

                        portal_candidate = extract_portal_path_from_stream(r, url)

                        if portal_candidate:
                            if not portal_candidate.startswith("/"):
                                portal_candidate = "/" + portal_candidate

                            portal = host.rstrip("/") + portal_candidate

                            if "/stalker_portal/c/" in url:
                                path_prefix = "/stalker_portal/c/"
                            elif "/c/" in url:
                                path_prefix = "/c/"
                            break

                    except Exception as e:
                        print("Error checking {}: {}".format(url, e))
                        continue

            # Final fallback if nothing worked

            if not portal:
                portal = host.rstrip("/") + "/portal.php"

            if debugs:
                print("*** Final portal path ***", portal)
                print("*** final path_prefix ***", path_prefix)

            # ########################################################################################
            # 3 - Get version number
            # ########################################################################################

            version_url = host.rstrip("/") + path_prefix + "version.js"

            vresponse = make_request(version_url, method="GET", headers=headers, params=None, response_type="text")
            if vresponse:

                match = re.search(r"ver\s*=\s*['\"]([^'\"]+)['\"]", vresponse)

                if match:
                    portal_version = match.group(1).strip()
                    if debugs:
                        print("*** version portal_version ***", version_url, portal_version)

            # ########################################################################################
            # 4. Handshake
            # ########################################################################################

            portal, token, token_random, headers = perform_handshake(portal=portal, host=host, mac=mac, headers=headers)

            if debugs:
                print("*** token ***", host, token)
            if not token:
                return index, {"valid": False}

            # ########################################################################################
            # 5. Get Profiles
            # ########################################################################################

            play_token, status, blocked, returned_mac, returned_id = get_profile_data(
                portal=portal,
                mac=mac,
                token=token,
                token_random=token_random,
                headers=headers,
                param_mode="full"
            )

            # ########################################################################################
            # 6. Get Account Info
            # if account info fails try basic get_profile
            # ########################################################################################

            account_info_url = str(portal) + "?type=account_info&action=get_main_info&JsHttpRequest=1-xml"
            account_info = make_request(account_info_url, method="POST", headers=headers, params=None, response_type="json")

            if debugs:
                print("*** account_info ***", account_info)

            if account_info and isinstance(account_info, dict):
                js_data = account_info.get("js") or {}
                expiry = js_data.get("phone") or js_data.get("end_date", "Unknown")
            else:
                if not returned_mac or not returned_id:
                    play_token, status, blocked, returned_mac, returned_id = get_profile_data(
                        portal=portal,
                        mac=mac,
                        token=token,
                        token_random=token_random,
                        headers=headers,
                        param_mode="basic"
                    )

                    account_info_url = str(portal) + "?type=account_info&action=get_main_info&JsHttpRequest=1-xml"
                    account_info = make_request(account_info_url, method="POST", headers=headers, params=None, response_type="json")

                    if account_info and isinstance(account_info, dict):
                        js_data = account_info.get("js") or {}
                        expiry = js_data.get("phone") or js_data.get("end_date", _("Unknown"))
                    else:
                        return index, {"valid": False}

            if not token:
                valid = False

            if blocked == "1":
                valid = False

            if "stalker" not in portal:
                if not expiry and status != 0:
                    valid = False

            if expiry == "Unlimited":
                expiry = _("Unlimited")

            elif expiry and expiry.isdigit():
                expiry = _("Unknown")

            return index, {
                "portal": portal,
                "version": portal_version,
                "token": token or "",
                "token_random": token_random or "",
                "valid": valid,
                "expiry": expiry or "",
                "play_token": play_token or "",
                "status": status,
                "blocked": blocked,
                "path_prefix": path_prefix,
                "active_connections": active_cons,
                "max_connections": max_cons
            }

    def process_downloads(self):
        if debugs:
            print("*** process_downloads ***")

        threads = min(len(self.url_list), 10)
        results = []

        if hasConcurrent:
            try:
                from concurrent.futures import ThreadPoolExecutor, as_completed

                # We need to maintain order, so we'll use a dictionary to track futures
                with ThreadPoolExecutor(max_workers=threads) as executor:
                    future_to_index = {
                        executor.submit(self.download_url, url_info): idx
                        for idx, url_info in enumerate(self.url_list)
                    }

                    # Initialize results list with None values
                    results = [None] * len(self.url_list)

                    for future in as_completed(future_to_index):
                        idx = future_to_index[future]
                        try:
                            result = future.result()
                            results[idx] = result
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
                        print("2 Error processing URL {}: {} {}".format(idx, e, url_info))
                        results.append((idx, {"valid": False}))

        elif hasMultiprocessing:
            try:
                # Multiprocessing version that maintains order
                from multiprocessing.pool import ThreadPool

                pool = ThreadPool(threads)
                try:
                    # imap maintains order
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
            # Fallback sequential processing
            results = []
            for url_info in self.url_list:
                try:
                    results.append(self.download_url(url_info))
                except Exception as e:
                    print("Error processing URL:", e)
                    results.append((0, {"valid": False}))

        # Update the playlist JSON
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
                        "path_prefx": "",
                        "active_connections": "",
                        "max_connections": "",
                    })
            except Exception as e:
                print(e)

        self.writeJsonFile()
        self.createSetup()
        # self.startXtreamCheck()  # NEW: Start deferred Xtream credentials check

    def writeJsonFile(self):
        if debugs:
            print("*** writeJsonFile ***")

        with open(playlists_json, "w") as f:
            json.dump(self.playlists_all, f)

    def createSetup(self):
        if debugs:
            print("*** createSetup ***")

        self["splash"].hide()

        self.list = []
        index = 0

        for playlist in self.playlists_all:
            domain = playlist["playlist_info"].get("domain", "")
            url = playlist["playlist_info"].get("host", "")
            message = _("Active")
            mac = playlist["playlist_info"].get("mac", "")
            token = playlist["playlist_info"].get("token", "")
            expiry = playlist["playlist_info"].get("expiry", "")
            status = playlist["playlist_info"].get("status", 0)
            blocked = playlist["playlist_info"].get("blocked", "0")
            valid = playlist["playlist_info"].get("valid", True)
            expires = str(expiry)
            portal = playlist["playlist_info"].get("portal", "")

            if "stalker" in portal:
                portalpath = "stalker_portal"
            else:
                portalpath = ""

            # active = str(_("Active Conn:"))
            # activenum = playlist["playlist_info"].get("active_connections", "")
            # maxc = str(_("Max Conn:"))
            # maxnum = playlist["playlist_info"].get("max_connections", "")

            portal_label = str(_("Portal Version:"))
            status_label = str(_("Status:"))

            parsed_date = parse_date_safe(expiry)
            if parsed_date and parsed_date < datetime.now():
                message = _("Expired")

            elif not valid:
                message = _("Not active")

            elif blocked == "1":
                message = _("Blocked")

            elif "stalker" not in portal:
                if str(status) != "0" and expiry:
                    message = _("Unknown")

            portal_version = playlist["playlist_info"].get("version", "")

            self.list.append([index, domain, url, expires, message, mac, token, portal_version, portal_label, valid, status, status_label, portalpath])
            index += 1

        self.drawList = [self.buildListEntry(x[0], x[1], x[2], x[3], x[4], x[5], x[6], x[7], x[8], x[9], x[10], x[11], x[12]) for x in self.list]
        self["playlists"].setList(self.drawList)

    def buildListEntry(self, index, domain, url, expires, message, mac, token, portal_version, portal_label, valid, status, status_label, portalpath):

        if not valid:
            pixmap = LoadPixmap(cached=True, path=os.path.join(common_path, "led_red.png"))

        elif message == _("Active"):
            pixmap = LoadPixmap(cached=True, path=os.path.join(common_path, "led_green.png"))

        elif message == _("Unknown"):
            pixmap = LoadPixmap(cached=True, path=os.path.join(common_path, "led_yellow.png"))

        elif message == _("Expired"):
            pixmap = LoadPixmap(cached=True, path=os.path.join(common_path, "led_yellow.png"))

        else:
            pixmap = LoadPixmap(cached=True, path=os.path.join(common_path, "led_red.png"))

        return (index, str(domain), str(url), str(expires), str(message), pixmap, str(mac), str(portal_version), str(portal_label), str(status), str(status_label), str(portalpath))

    def quit(self, answer=None):
        self.close()

    def deleteServer(self, answer=None):

        if self.list != []:
            self.currentplaylist = glob.active_playlist.copy()

            if answer is None:
                self.session.openWithCallback(
                    self.deleteServer,
                    MessageBox,
                    _("Delete selected server (MAC) entry?")
                )
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

                if stripped.startswith("http://") or stripped.startswith("https://"):
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

            # Remove from JSON
            for i in range(len(self.playlists_all)):
                playlist = self.playlists_all[i]
                playlist_url = playlist.get("playlist_info", {}).get("url", "").strip().rstrip('/')
                playlist_mac = playlist.get("playlist_info", {}).get("mac", "").strip().lower()

                if playlist_url == url_to_delete and playlist_mac == mac_to_delete:
                    del self.playlists_all[i]
                    break

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

                elif glob.current_selection + 1 > ((self["playlists"].count() // 5) * 5):
                    self["scroll_down"].hide()
        else:
            glob.current_selection = 0
            glob.active_playlist = {}

    def getStreamTypes(self):
        if glob.active_playlist["playlist_info"]["valid"] is True:
            from . import menu
            self.session.open(menu.EStalker_Menu)
            self.checkoneplaylist()

    def checkoneplaylist(self):
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

        # Step 1: Process the e-portals.txt file
        with open(playlist_file, "r") as f:
            lines = [line.strip() for line in f]

        new_lines = []
        current_url = None
        macs_to_keep = set()

        # First identify all valid MACs from JSON
        for playlist in self.playlists_all:
            if playlist["playlist_info"].get("valid", False):
                macs_to_keep.add(playlist["playlist_info"]["mac"].lower())

        # Now process the file
        for line in lines:
            if line.startswith(("http://", "https://")):
                current_url = line
                new_lines.append(line)
            elif line and current_url:
                # Only keep if MAC is in our valid set
                if line.lower() in macs_to_keep:
                    new_lines.append(line)
                else:
                    new_lines.append("#" + line)  # Comment out invalid
            else:
                new_lines.append(line)  # Keep comments/empty lines

        # Write back the cleaned file
        with open(playlist_file, "w") as f:
            f.write("\n".join(new_lines) + "\n")

        # Step 2: Clean the JSON data
        self.playlists_all = [
            playlist for playlist in self.playlists_all
            if playlist["playlist_info"].get("valid", False)
        ]

        # Reindex all remaining playlists
        for index, playlist in enumerate(self.playlists_all):
            playlist["playlist_info"]["index"] = index

        # Save the cleaned JSON
        self.writeJsonFile()
        self.createSetup()

        self.session.open(MessageBox, _("Removed all invalid playlists"), MessageBox.TYPE_INFO, timeout=3)

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
            "menu": self.quit}, -2)

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
        self["portalcalls"].setText(str(portaltext))
        self["status"].setText(str(playlist_info.get("status", "")))
        self["expiry"].setText(str(playlist_info.get("expiry", "Unknown")))

        self.get_stream_url()

    def get_stream_url(self):
        if debugs:
            print("*** get_stream_url ***")

        # Try to fetch Xtream credentials
        def fetch_xtream_creds(portal, headers, content_type="itv", domain=""):
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

                link_js = link_data.get("js") or {}
                cmd = link_js.get("cmd")

                if not cmd:
                    return {}

                stream_url = str(cmd)
                parsed = urlparse(stream_url)
                if parsed.scheme in ["http", "https"]:
                    stream_url = parsed.geturl()

                match = re.search(r'/movie/([^/]+)/([^/]+)/', stream_url)
                if match:
                    username = match.group(1)
                    password = match.group(2)
                    return {"username": username, "password": password}

                return {}

            except Exception as e:
                print("Error fetching Xtream creds:", e, domain)
                return {}

        # Try VOD first, then Live

        portal = glob.active_playlist["playlist_info"]["portal"]
        domain = glob.active_playlist["playlist_info"]["domain"]
        mac = glob.active_playlist["playlist_info"]["mac"]
        timezone = get_local_timezone()

        headers = {
            "Host": domain,
            "Accept": "*/*",
            "User-Agent": "Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 (KHTML, like Gecko) MAG250 stbapp ver: 2 rev: 369 Safari/533.3",
            "Accept-Encoding": "gzip, deflate",
            "X-User-Agent": "Model: MAG250; Link: WiFi",
            "Connection": "close",
            "Pragma": "no-cache",
            "Cache-Control": "no-store, no-cache, must-revalidate",
            "Cookie": "mac={}; stb_lang=en; timezone={};".format(mac, timezone),
        }

        xtream_creds = fetch_xtream_creds(portal, headers, content_type="vod", domain=domain) or {}

        if not xtream_creds.get("username") or not xtream_creds.get("password"):
            xtream_creds = fetch_xtream_creds(portal, headers, content_type="itv", domain=domain) or {}

        username = xtream_creds.get("username", "")
        password = xtream_creds.get("password", "")

        if username and password:
            self.fetch_xtream_api(xtream_creds)

    def fetch_xtream_api(self, xtream_creds):
        if debugs:
            print("*** fetch_xtream_api ***")

        # ########################################################################################
        # If credentials found, get Xtream API info
        # ########################################################################################

        username = xtream_creds.get("username", "")
        password = xtream_creds.get("password", "")
        host = glob.active_playlist["playlist_info"]["host"]
        temp_xtream_player_api = host.rstrip("/") + "/player_api.php?username={}&password={}".format(xtream_creds["username"], xtream_creds["password"])
        expiry = glob.active_playlist["playlist_info"]["expiry"]
        status = glob.active_playlist["playlist_info"]["status"]
        active_cons = ""
        max_cons = ""
        created_at = ""
        is_trial = ""
        index = glob.active_playlist["playlist_info"]["index"]

        if username and password and len(password) != 32:
            time.sleep(3)
            api_data = xtream_request(temp_xtream_player_api)

            user_info = {}
            if api_data:
                if api_data and 'user_info' in api_data:
                    user_info = api_data['user_info']
                    active_cons = str(user_info.get('active_cons', ""))
                    max_cons = str(user_info.get('max_connections', ""))

                    if user_info.get('auth') == 1:
                        status_map = {
                            "Active": _("Active"),
                            "Banned": _("Banned"),
                            "Disabled": _("Disabled"),
                            "Expired": _("Expired")
                        }

                        status = status_map.get(user_info.get("status"), _("Unknown"))
                        is_trial = user_info.get('is_trial', "")

                    if 'created_at' in user_info:
                        try:
                            created_timestamp = int(user_info['created_at'])
                            if created_timestamp > 0:
                                dt = datetime.fromtimestamp(created_timestamp)
                                hour = dt.hour % 12 or 12
                                ampm = 'am' if dt.hour < 12 else 'pm'
                                created_at = dt.strftime('%B %d, %Y, ') + '{:d}:{:02d} {}'.format(hour, dt.minute, ampm)
                        except (ValueError, TypeError):
                            pass

                    if 'exp_date' in user_info:
                        try:
                            expiry_timestamp = int(user_info['exp_date'])
                            if expiry_timestamp > 0:
                                dt = datetime.fromtimestamp(expiry_timestamp)
                                hour = dt.hour % 12 or 12
                                ampm = 'am' if dt.hour < 12 else 'pm'
                                expiry = dt.strftime('%B %d, %Y, ') + '{:d}:{:02d} {}'.format(hour, dt.minute, ampm)
                        except (ValueError, TypeError):
                            pass

        self["status"].setText(status)
        self["expiry"].setText(str(expiry))
        self["created"].setText(str(created_at))
        self["trial"].setText(str(is_trial))
        self["activeconn"].setText(str(active_cons))
        self["maxconn"].setText(str(max_cons))

        self.update_results(index, expiry, active_cons, max_cons)

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
        if debugs:
            print("*** writeJsonFile ***")

        try:
            with open(playlists_json, "w") as f:
                json.dump(self.playlists_all, f)
        except Exception as e:
            print("Error writing JSON:", e)

    def quit(self):
        self.close()
