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
from requests.adapters import HTTPAdapter

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

PROTOCOL_PATTERN = re.compile(r"this\.portal_protocol\s*=\s*document\.URL\.replace\(pattern,\s*\"([^\"]+)\"\)")
IP_PATTERN = re.compile(r"this\.portal_ip\s*=\s*document\.URL\.replace\(pattern,\s*\"([^\"]+)\"\)")
PATH_PATTERN = re.compile(r"this\.portal_path\s*=\s*document\.URL\.replace\(pattern,\s*\"([^\"]+)\"\)")
LOADER_PATTERN = re.compile(r"this\.ajax_loader\s*=\s*(.*?\.php);")
URL_PATTERN = re.compile(r"(https?):\/\/([^\/]*)\/([^\/]*)")


def load_playlists_all():
    """Load playlist data using the currently selected playlist cache."""
    playlists_all = []
    playlists_json = cfg.playlists_json.value

    if os.path.isfile(playlists_json):
        with open(playlists_json, "r") as f:
            try:
                playlists_all = json.load(f)
                playlists_all.sort(key=lambda e: e["playlist_info"]["index"], reverse=False)
            except Exception:
                os.remove(playlists_json)

    return playlists_all


playlists_all = load_playlists_all()


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


def make_request(url, method="GET", headers=None, params=None, response_type=None, http=None):
    own_session = http is None

    if own_session:
        http = requests.Session()

    result = None

    try:
        if method.upper() == "POST":
            body = urlencode(params) if params else ""
            post_headers = headers.copy() if headers else {}

            if "Content-Type" not in post_headers:
                post_headers["Content-Type"] = "application/x-www-form-urlencoded; charset=utf-8"

            response = http.post(url, headers=post_headers, data=body, timeout=10, verify=False, allow_redirects=True)
        else:
            if params:
                parsed_url = urlparse(url)
                existing_params = dict(parse_qsl(parsed_url.query))
                existing_params.update(params)
                url = urlunparse(parsed_url._replace(query=urlencode(existing_params)))

            response = http.get(url, headers=headers, timeout=(8, 8), verify=False, allow_redirects=True)

        response.raise_for_status()

        if response_type == "json":
            try:
                result = response.json()
            except ValueError:
                try:
                    result = json.loads(response.text)
                except (ValueError, TypeError):
                    result = None

        elif response_type == "text":
            result = response.text

    except Exception:
        result = None

    finally:
        if own_session:
            http.close()

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
            r = http.get(url, headers=hdr, timeout=(8, 8), verify=False)
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


def perform_handshake(portal, host, mac, headers, http=None):
    # A handshake starts without a previous bearer token. Remove any stale
    # token cookie; the newly returned token is added after the handshake.
    headers.pop("Authorization", None)
    cookie_parts = []
    for cookie_part in headers.get("Cookie", "").split(";"):
        cookie_part = cookie_part.strip()
        if cookie_part and cookie_part.split("=", 1)[0].strip().lower() != "token":
            cookie_parts.append(cookie_part)
    headers["Cookie"] = "; ".join(cookie_parts)

    handshake_url = "{}?".format(portal)
    body_params = {
        "type": "stb",
        "action": "handshake",
        "token": "",
        "prehash": "0",
        "JsHttpRequest": "1-xml"
    }

    response = make_request(handshake_url, method="GET", headers=headers, params=body_params, response_type="json", http=http)

    if not response:
        handshake_url = "{}?".format(portal)
        body_params = {
            "type": "stb",
            "action": "handshake",
            "token": "",
            "prehash": "0",
            "JsHttpRequest": "1-xml",
            "mac": mac
        }
        response = make_request(handshake_url, method="GET", headers=headers, params=body_params, response_type="json", http=http)

    token = None
    token_random = None
    not_valid = 0

    # print("*** handshake response ***", response)

    if response and isinstance(response, dict):
        js_data = response.get("js") or {}

        # print("*** js ***", js_data)
        if not isinstance(js_data, dict):
            js_data = {}

        if "missing" in str(js_data.get("msg") or "").lower():

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

            response = make_request(handshake_url, method="GET", headers=headers, params=prehash_params, response_type="json", http=http)
            js_data = response.get("js", {}) if isinstance(response, dict) else {}
            if not isinstance(js_data, dict):
                js_data = {}

        token = js_data.get("token")
        token_random = js_data.get("random", "")
        not_valid_value = js_data.get("not_valid", 0)
        not_valid = 1 if str(not_valid_value).strip().lower() in ("1", "true", "yes") else 0

        if not token:
            headers.pop("Authorization", None)
            return portal, None, token_random, not_valid, headers

        headers["Authorization"] = "Bearer " + token
        headers["Cookie"] = headers.get("Cookie", "") + "; token=" + token

    """
    else:
        print("Invalid handshake response:", portal)
        """

    return portal, token, token_random, not_valid, headers


def get_profile_data(portal, mac, token, token_random, headers, http=None, not_valid=0, portal_version=""):

    profile_params = {}

    # print("***get_profile_data***")
    # print("***portal***", portal)
    # print("***mac***", mac)
    # print("***token***", token)
    # print("***token_random***", token_random)
    # print("***headers***", json.dumps(headers))

    sn = hashlib.md5(mac.encode()).hexdigest().upper()[:13]
    device_id = hashlib.sha256(mac.encode()).hexdigest().upper()
    # device_id2 = hashlib.sha256(device_id.encode()).hexdigest().upper()
    hw_version_2 = hashlib.sha1(mac.encode()).hexdigest()
    # hw_version_2 = hashlib.sha1(mac.lower().encode()).hexdigest()
    # hw_version_2 = hashlib.sha1(mac.replace(":", "").lower().encode()).hexdigest()
    # Preserve the established EStalker identity used when the device was
    # registered with portals.
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

    host_metrics = {
        "mac": mac,
        "sn": sn,
        "model": "MAG250",
        "type": "STB",
        "uid": "",
        "random": token_random or ""
    }
    metrics_json = json.dumps(host_metrics, separators=(',', ':'))
    encoded_once = quote(metrics_json)
    reported_portal_version = "5.3.0"

    host_params = OrderedDict([
        ('hd', '1'),
        ('ver', 'ImageDescription: 0.2.18-r23-250; ImageDate: Thu Sep 13 11:31:16 EEST 2018; PORTAL version: {}; API Version: JS API version: 343; STB API version: 146; Player Engine version: 0x58c'.format(reported_portal_version)),
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
        ('not_valid_token', '1' if not_valid else '0'),
        ('metrics', encoded_once),
        ('hw_version_2', hw_version_2),
        ('timestamp', str(int(timestamp))),
        ('api_signature', '262'),
        ('prehash', prehash),
    ])

    profile_params = host_params

    # print("*** headers ***", json.dumps(headers))
    # print("*** params ***", json.dumps(profile_params))

    base_profile_params.update(profile_params)
    profile_params = base_profile_params

    profile_data = make_request(profile_url, method="GET", headers=headers, params=profile_params, response_type="json", http=http)

    """
    if debugs:
        print("*** profile_data ***", portal, mac, json.dumps(profile_data))
        """

    profile = profile_data.get("js") if isinstance(profile_data, dict) else None

    if not isinstance(profile, dict) or not profile.get("id"):
        print("** full params failed ***", profile_url, mac)
        fallback_params = OrderedDict([
            ("type", "stb"),
            ("action", "get_profile"),
            ("JsHttpRequest", "1-xml"),
            ('sn', sn),
            ('device_id', ''),
            ('timestamp', str(int(timestamp))),
        ])

        profile_data = make_request(profile_url, method="GET", headers=headers, params=fallback_params, response_type="json", http=http)

        """
        if debugs:
            print("*** profile_data 2 ***", portal, mac, json.dumps(profile_data))
            """

    js_data = {}
    play_token = None
    status = 1
    blocked = "0"
    returned_id = ""
    force_ch_link_check = "0"
    mac = ""

    if profile_data:
        js_data = profile_data.get("js", {})

        if not isinstance(js_data, dict):
            js_data = {}

        if js_data:
            play_token = js_data.get("play_token", None)
            status = js_data.get("status", 1)
            blocked = js_data.get("blocked", "0")
            mac = js_data.get("mac", "")
            returned_id = js_data.get("id", "")
            force_ch_link_check = js_data.get("force_ch_link_check", "0")

    # print("*** play_token ***", play_token)
    # print("*** status ***", status)
    # print("*** blocked ***", blocked)
    # print("*** mac ***", mac)
    # print("*** returned_id ***", returned_id)

    return play_token, status, blocked, mac, returned_id, force_ch_link_check


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

                # print("*** AR via DreamOS ***", mode)

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


def clearCaches():
    try:
        os.system("sync")

        with open("/proc/sys/vm/drop_caches", "w") as drop_caches:
            drop_caches.write("3\n")
    except (IOError, OSError):
        pass


def get_account_info(portal, headers, http=None, unknown_value="Unknown"):
    account_info_url = "{}?".format(portal)
    account_info_params = {
        "type": "account_info",
        "action": "get_main_info",
        "JsHttpRequest": "1-xml",
    }

    account_info = make_request(account_info_url, method="GET", headers=headers, params=account_info_params, response_type="json", http=http)

    if debugs:
        print("*** account_info ***", account_info_url, account_info)

    if account_info and isinstance(account_info, dict):
        js_data = account_info.get("js") or {}
        expiry = js_data.get("phone") or js_data.get("end_date", unknown_value)
        return expiry, True

    return None, False


def reauthorize_portal(portal, host, mac, headers, http=None):
    own_session = http is None

    if own_session:
        http = requests.Session()

    try:
        portal, token, token_random, not_valid, headers = perform_handshake(portal, host, mac, headers, http=http)

        # not_valid is consumed by get_profile; it is not a handshake failure.
        if not token:
            return None

        play_token, status, blocked, returned_mac, returned_id, force_ch_link_check = get_profile_data(
            portal, mac, token, token_random, headers, http=http, not_valid=not_valid
        )
        expiry, account_valid = get_account_info(portal, headers, http=http)

        return portal, token, token_random, headers, play_token, status, blocked

    finally:
        if own_session:
            http.close()
