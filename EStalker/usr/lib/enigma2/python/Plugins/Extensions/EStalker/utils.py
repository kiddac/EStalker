import json
import os
import re
import hashlib
from collections import OrderedDict
from datetime import datetime
import string
import random
import time

# Third-party imports
import requests
from requests.adapters import HTTPAdapter, Retry

try:
    from urllib import urlencode
except ImportError:
    from urllib.parse import urlencode

try:
    from urllib import quote  # Python 2
except ImportError:
    from urllib.parse import quote  # Python 3

try:
    from urlparse import urlparse, parse_qsl, urlunparse
except ImportError:
    from urllib.parse import urlparse, parse_qsl, urlunparse

from .plugin import cfg, pythonVer, debugs

try:
    from enigma import eAVSwitch
except Exception:
    from enigma import eAVControl as eAVSwitch

hasAVSwitch = False
try:
    from Components.AVSwitch import avSwitch
    hasAVSwitch = True
except Exception:
    pass

playlist_file = cfg.playlist_file.value
playlists_json = cfg.playlists_json.value

PROTOCOL_PATTERN = re.compile(r"this\.portal_protocol\s*=\s*document\.URL\.replace\(pattern,\s*\"([^\"]+)\"\)")
IP_PATTERN = re.compile(r"this\.portal_ip\s*=\s*document\.URL\.replace\(pattern,\s*\"([^\"]+)\"\)")
PATH_PATTERN = re.compile(r"this\.portal_path\s*=\s*document\.URL\.replace\(pattern,\s*\"([^\"]+)\"\)")
LOADER_PATTERN = re.compile(r"this\.ajax_loader\s*=\s*(.*?\.php);")
URL_PATTERN = re.compile(r"(https?):\/\/([^\/]*)\/([^\/]*)")

playlists_all = []

if os.path.isfile(playlists_json):
    with open(playlists_json, "r") as f:
        try:
            playlists_all = json.load(f)
            playlists_all.sort(key=lambda e: e["playlist_info"]["index"], reverse=False)
        except:
            os.remove(playlists_json)


def get_local_timezone():
    timezone_path = '/etc/timezone'
    default_tz = 'Europe/London'

    try:
        if os.path.exists(timezone_path):
            with open(timezone_path, 'r') as f:
                timezone = f.read().strip()
                if '/' in timezone and not timezone.startswith('#'):
                    return timezone
    except (IOError, PermissionError):
        pass

    return default_tz


def make_request(url, method="GET", headers=None, params=None, response_type=None):
    with requests.Session() as http:
        result = None
        retry = Retry(total=0, backoff_factor=1, status_forcelist=[500, 502, 503, 504])
        adapter = HTTPAdapter(max_retries=retry)
        http.mount("http://", adapter)
        http.mount("https://", adapter)

        try:
            if method.upper() == "POST":
                body = urlencode(params) if params else ""
                post_headers = headers.copy() if headers else {}
                if "Content-Type" not in post_headers:
                    post_headers["Content-Type"] = "application/x-www-form-urlencoded; charset=utf-8"
                r = http.post(url, headers=post_headers, data=body, timeout=(5, 8), verify=False, allow_redirects=True)
            else:
                if params:
                    parsed_url = urlparse(url)
                    existing_params = dict(parse_qsl(parsed_url.query))
                    merged_params = existing_params.copy()
                    merged_params.update(params)
                    query_string = urlencode(merged_params)
                    url = urlunparse(parsed_url._replace(query=query_string))
                r = http.get(url, headers=headers, timeout=(5, 8), verify=False, allow_redirects=True)

            r.raise_for_status()

            if response_type == "json":
                try:
                    result = r.json()
                except ValueError:
                    try:
                        result = json.loads(r.text)
                    except:
                        result = None
            elif response_type == "text":
                try:
                    result = r.text
                except:
                    result = None

            return result

        except Exception:
            return result


def xtream_request(url):
    response = None

    hdr = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/145.0.0.0 Safari/537.36",
        "Accept-Encoding": "gzip, deflate",
    }

    with requests.Session() as http:
        adapter = HTTPAdapter(max_retries=1)
        http.mount("http://", adapter)
        http.mount("https://", adapter)

        try:
            r = http.get(url, headers=hdr, timeout=(5, 5), verify=False)
            r.raise_for_status()

            try:
                response = r.json()
            except ValueError:
                try:
                    response_text = r.text
                    response = json.loads(response_text)
                except ValueError:
                    return None

        except requests.exceptions.RequestException:
            pass

        except Exception:
            pass

    return response


def perform_handshake(portal, host, mac, headers):
    handshake_url = "{}?".format(portal)
    body_params = {
        "type": "stb",
        "action": "handshake",
        "token": "",
        "JsHttpRequest": "1-xml"
    }

    response = make_request(handshake_url, method="GET", headers=headers, params=body_params, response_type="json")

    if not response:
        handshake_url = "{}?".format(portal)
        body_params = {
            "type": "stb",
            "action": "handshake",
            "token": "",
            "JsHttpRequest": "1-xml",
            "mac": mac
        }
        response = make_request(handshake_url, method="GET", headers=headers, params=body_params, response_type="json")

    token = None
    token_random = None

    # print("*** handshake response ***", response)

    if response and isinstance(response, dict):
        js_data = response.get("js", {})

        if "msg" in js_data and "missing" in js_data["msg"].lower():

            def generate_token():
                return ''.join(random.choice(string.ascii_uppercase + string.digits) for _ in range(32))

            fake_token = generate_token()
            prehash = hashlib.sha1(fake_token.encode()).hexdigest()

            headers["Authorization"] = "Bearer " + fake_token

            handshake_url = "{}?".format(portal)

            prehash_params = {
                "type": "stb",
                "action": "handshake",
                "JsHttpRequest": "1-xml",
                "mac": mac,
                "prehash": prehash
            }

            response = make_request(handshake_url, method="GET", headers=headers, params=prehash_params, response_type="json")
            js_data = response.get("js", {}) if response else {}

        token = js_data.get("token")
        token_random = js_data.get("random", "")

        if not token:
            return portal, None, None, headers

        headers["Authorization"] = "Bearer " + token
        headers["Cookie"] = headers.get("Cookie", "") + "; token=" + token

    """
    else:
        print("Invalid handshake response:", portal)
        """

    return portal, token, token_random, headers


def get_profile_data(portal, mac, token, token_random, headers, param_mode):

    profile_params = {}

    # print("***get_profile_data***")
    # print("***portal***", portal)
    # print("***mac***", mac)
    # print("***token***", token)
    # print("***token_random***", token_random)
    # print("***headers***", json.dumps(headers))
    # print("***param_mode***", param_mode)

    sn = hashlib.md5(mac.encode()).hexdigest().upper()[:13]
    device_id = hashlib.sha256(mac.encode()).hexdigest().upper()
    device_id2 = hashlib.sha256(device_id.encode()).hexdigest().upper()
    hw_version_2 = hashlib.sha1(mac.encode()).hexdigest()
    # hw_version_2 = hashlib.sha1(mac.lower().encode()).hexdigest()
    # hw_version_2 = hashlib.sha1(mac.replace(":", "").lower().encode()).hexdigest()
    prehash = hashlib.sha1((sn + mac).encode()).hexdigest()
    # signature = hashlib.sha256((device_id + device_id2).encode()).hexdigest().upper()
    signature2 = hashlib.sha256((device_id + device_id).encode()).hexdigest().upper()

    # print("***sn***", sn)
    # print("***device_id***", device_id)
    # print("***device_id2***", device_id2)
    # print("***hw_version_2***", hw_version_2)
    # print("***prehash***", prehash)
    # print("***signature***", signature)
    # print("***signature2***", signature2)
    # print("")

    dt = datetime.now()
    timestamp = datetime.timestamp(dt) if pythonVer == 3 else time.mktime(dt.timetuple())

    profile_url = "{}?".format(portal)
    base_profile_params = OrderedDict([
        ("type", "stb"),
        ("action", "get_profile"),
        ("JsHttpRequest", "1-xml"),
    ])

    if "/stalker_portal/" in portal:
        host_metrics = {
            "type": "stb",
            "model": "MAG254",
            "mac": mac,
            "sn": sn,
            "uid": device_id2,
            "random": token_random
        }

        metrics_json = json.dumps(host_metrics, separators=(',', ':'))
        encoded_once = quote(metrics_json)

        host_params = OrderedDict([
            ('hd', '1'),
            ('ver', 'ImageDescription: 0.2.18-r23-250; ImageDate: Thu Sep 13 11:31:16 EEST 2018; PORTAL version: 5.3.0; API Version: JS API version: 343; STB API version: 146; Player Engine version: 0x58c'),
            ('num_banks', '2'),
            ('sn', sn),
            ('stb_type', 'MAG250'),
            ('client_type', 'STB'),
            ('image_version', '218'),
            ('video_out', 'hdmi'),
            ('device_id', device_id),
            ('device_id2', device_id),
            ('signature', signature2),
            ('auth_second_step', '1'),
            ('hw_version', '1.7-BD-00'),
            ('not_valid_token', '0'),
            ('metrics', encoded_once),
            ('hw_version_2', hw_version_2),
            ('timestamp', str(int(timestamp))),
            ('api_signature', '262'),
            ('prehash', prehash),
        ])

        profile_params = host_params

    else:
        host_metrics = {
            "mac": mac,
            "sn": sn,
            "type": "STB",
            "model": "MAG250",
            "uid": "",
            "random": ""
        }

        metrics_json = json.dumps(host_metrics, separators=(',', ':'))

        # print("*** metrics_json ***",  metrics_json)

        # url encode metrics
        encoded_once = quote(metrics_json)

        # print("*** metrix encoded_once ***", encoded_once)

        if param_mode == "full":
            host_params = OrderedDict([
                ('hd', '1'),
                ('ver', 'ImageDescription: 0.2.18-r23-250; ImageDate: Thu Sep 13 11:31:16 EEST 2018; PORTAL version: 5.3.0; API Version: JS API version: 343; STB API version: 146; Player Engine version: 0x58c'),
                ('num_banks', '2'),
                ('sn', sn),
                ('stb_type', 'MAG250'),
                ('client_type', 'STB'),
                ('image_version', '218'),
                ('video_out', 'hdmi'),
                ('device_id', device_id),
                ('device_id2', device_id),
                ('signature', signature2),
                ('auth_second_step', '1'),
                ('hw_version', '1.7-BD-00'),
                ('not_valid_token', '0'),
                ('metrics', encoded_once),
                ('hw_version_2', hw_version_2),
                ('timestamp', str(int(timestamp))),
                ('api_signature', '262'),
                ('prehash', prehash),
            ])

        if param_mode == "basic":
            host_params = OrderedDict([
                # ('sn', sn),
                # ('device_id', ''),
                # ('timestamp', str(int(timestamp))),
            ])

        profile_params = host_params

    # print("*** headers ***", json.dumps(headers))
    # print("*** params ***", json.dumps(profile_params))

    base_profile_params.update(profile_params)
    profile_params = base_profile_params

    profile_data = make_request(profile_url, method="GET", headers=headers, params=profile_params, response_type="json")

    if debugs:
        print("*** profile_data ***", portal, mac, json.dumps(profile_data))

    js_data = {}
    play_token = None
    status = 0
    blocked = "0"
    returned_id = ""
    mac = ""

    if profile_data:
        js_data = profile_data.get("js", {})

        if not isinstance(js_data, dict):
            js_data = {}

        if js_data:
            play_token = js_data.get("play_token", None)
            status = js_data.get("status", 0)
            blocked = js_data.get("blocked", "0")
            mac = js_data.get("mac", "")
            returned_id = js_data.get("id", "")

            # If we got an error message and no play_token, try basic fallback
            msg = js_data.get("msg", "")
            if msg and not play_token:
                print("*** profile_data error msg, trying basic fallback ***", msg)
                profile_data = None  # force fallback below

    if not profile_data:
        # print("*** trying profile data basic ***")
        # Fallback: try with no params

        fallback_params = OrderedDict([
            ("type", "stb"),
            ("action", "get_profile"),
            ("JsHttpRequest", "1-xml"),
            ('sn', sn),
            ('device_id', ''),
            ('timestamp', str(int(timestamp))),
        ])

        profile_data = make_request(profile_url, method="GET", headers=headers, params=fallback_params, response_type="json")

        # print("*** profile_data 2 ***", portal, mac, json.dumps(profile_data))
        if profile_data:
            js_data = profile_data.get("js", {})

            if not isinstance(js_data, dict):
                js_data = {}

            if js_data:
                play_token = js_data.get("play_token", None)
                status = js_data.get("status", 0)
                blocked = js_data.get("blocked", "0")
                mac = js_data.get("mac", "")
                returned_id = js_data.get("id", "")

    # print("*** play_token ***", play_token)
    # print("*** status ***", status)
    # print("*** blocked ***", blocked)
    # print("*** mac ***", mac)
    # print("*** returned_id ***", returned_id)

    return play_token, status, blocked, mac, returned_id


def _get_current_aspect_ratio():

    current_ar = None

    # 1 Fallback to proc (ATV / BH / VTi etc)
    if current_ar is None:
        try:
            if os.path.exists("/proc/stb/video/aspect"):
                with open("/proc/stb/video/aspect", "r") as f:
                    aspect = f.read().strip()

                with open("/proc/stb/video/policy", "r") as f:
                    policy = f.read().strip()

                if aspect == "4:3":
                    if policy == "letterbox":
                        current_ar = 0
                    elif policy == "panscan":
                        current_ar = 1

                elif aspect == "16:9":
                    if policy == "letterbox":
                        current_ar = 6
                    elif policy == "panscan":
                        current_ar = 3
                    else:
                        current_ar = 2

                elif aspect == "16:10":
                    if policy == "letterbox":
                        current_ar = 4
                    elif policy == "panscan":
                        current_ar = 5

        except Exception as e:
            print("*** proc read failed ***", e)

    # 2 Try eAVSwitch (if available)
    if current_ar is None:
        try:
            inst = eAVSwitch.getInstance()
            if hasattr(inst, "getAspectRatio"):
                current_ar = int(inst.getAspectRatio())
        except Exception as e:
            print("*** eAVSwitch failed ***", e)

    # 3 DreamOS fallback
    if current_ar is None:
        try:
            if os.path.exists("/sys/class/video/screen_mode"):
                with open("/sys/class/video/screen_mode", "r") as f:
                    mode = f.read().strip()

                print("*** AR via DreamOS ***", mode)

                if "letterbox" in mode:
                    current_ar = 0
                elif "panscan" in mode:
                    current_ar = 1
                elif "16:9" in mode:
                    current_ar = 2

        except Exception as e:
            print("*** DreamOS read failed ***", e)

    # 4 Final fallback - config settings
    if current_ar is None:
        try:
            if hasAVSwitch:
                current_ar = int(avSwitch.getAspectRatioSetting())
        except Exception as e:
            print("*** avSwitch failed ***", e)

    return current_ar
