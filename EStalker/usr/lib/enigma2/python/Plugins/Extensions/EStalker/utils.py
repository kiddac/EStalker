import json
import os
import re
import hashlib
from datetime import datetime
import string
# import time
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

from .plugin import cfg, pythonVer

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
    """Get local timezone from /etc/timezone or use Europe/London as fallback"""
    timezone_path = '/etc/timezone'
    default_tz = 'Europe/London'

    try:
        if os.path.exists(timezone_path):
            with open(timezone_path, 'r') as f:
                timezone = f.read().strip()
                # Validate it looks like a proper timezone (Area/City format)
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
            if params:
                parsed_url = urlparse(url)
                existing_params = dict(parse_qsl(parsed_url.query))
                merged_params = existing_params.copy()
                merged_params.update(params)
                query_string = urlencode(merged_params)
                url = urlunparse(parsed_url._replace(query=query_string))

            if method.upper() == "POST":
                r = http.post(url, headers=headers, data="", timeout=(6, 20), verify=False, allow_redirects=True)
            else:
                r = http.get(url, headers=headers, timeout=(6, 20), verify=False, allow_redirects=True)

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
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
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

                except json.JSONDecodeError:
                    return None

        except requests.exceptions.RequestException:
            pass

        except Exception:
            pass

    return response


def perform_handshake(portal, host, mac, headers):
    handshake_url = "{}?type=stb&action=handshake&JsHttpRequest=1-xml".format(portal)
    response = make_request(handshake_url, method="POST", headers=headers, params=None, response_type="json")

    if not response:
        handshake_url = "{}?type=stb&action=handshake&JsHttpRequest=1-xml&mac={}".format(portal, mac)
        response = make_request(handshake_url, method="POST", headers=headers, params=None, response_type="json")

    token = None
    token_random = None

    if response and isinstance(response, dict):
        js_data = response.get("js", {})

        if "msg" in js_data and "missing" in js_data["msg"].lower():

            def generate_token():
                return ''.join(random.choice(string.ascii_uppercase + string.digits) for _ in range(32))

            fake_token = generate_token()
            prehash = hashlib.sha1(fake_token.encode()).hexdigest()

            headers["Authorization"] = "Bearer " + fake_token

            handshake_url = "{}?type=stb&action=handshake&JsHttpRequest=1-xml&mac={}&prehash={}".format(portal, mac, prehash)
            response = make_request(handshake_url, method="POST", headers=headers, params=None, response_type="json")
            js_data = response.get("js", {}) if response else {}

        token = js_data.get("token")
        token_random = js_data.get("random", "")

        if not token:
            return portal, None, None, headers

        headers["Authorization"] = "Bearer " + token

    else:
        print("Invalid handshake response:", portal)

    return portal, token, token_random, headers


def get_profile_data(portal, mac, token, token_random, headers, param_mode):

    sn = hashlib.md5(mac.encode()).hexdigest().upper()[:13]
    device_id = hashlib.sha256(mac.encode()).hexdigest().upper()
    device_id2 = device_id
    hw_version_2 = hashlib.sha1(mac.encode()).hexdigest()
    prehash = hashlib.sha1((sn + mac).encode()).hexdigest()

    dt = datetime.now()
    timestamp = datetime.timestamp(dt) if pythonVer == 3 else time.mktime(dt.timetuple())

    profile_url = "{}?type=stb&action=get_profile&JsHttpRequest=1-xml".format(portal)

    if "/stalker_portal/" in portal:
        host_metrics = {
            "type": "stb",
            "model": "MAG254",
            "mac": mac,
            "sn": sn,
            "uid": "",
            "random": token_random
        }

        metrics_json = json.dumps(host_metrics)
        encoded_once = quote(metrics_json)

        host_params = {
            "mac": mac,
            "hd": "1",
            "ver": (
                "ImageDescription: 0.2.18-r14-pub-250; ImageDate: Fri Jan 15 15:20:44 EET 2016; PORTAL version: 5.3.0; API Version: JS API version: 328; STB API version: 134; Player Engine version: 0x566"
            ),
            "num_banks": "2",
            "sn": sn,
            "stb_type": "MAG254",
            "client_type": "STB",
            "image_version": "218",
            "video_out": "hdmi",
            "device_id": device_id,
            "device_id2": device_id2,
            "signature": "",
            "auth_second_step": "1",
            "hw_version": "1.7-BD-00",
            "hw_version_2": hw_version_2,
            "not_valid_token": '0',
            "metrics": encoded_once,
            "timestamp": str(round(timestamp)),
            "api_signature": "261",
            "prehash": prehash
        }

        profile_params = dict(host_params)

    else:
        host_metrics = {
            "mac": mac,
            "sn": sn,
            "type": "STB",
            "model": "MAG250",
            "uid": "",
            "random": ""
        }

        metrics_json = json.dumps(host_metrics)

        # url encode metrics
        encoded_once = quote(metrics_json)

        if param_mode == "full":
            host_params = {
                'hd': '1',
                "sn": sn,
                'stb_type': "MAG250",
                'client_type': 'STB',
                'image_version': '218',
                "device_id": "",
                "device_id2": "",
                'hw_version': '1.7-BD-00',
                "metrics": encoded_once,
                'timestamp': str(timestamp),
                # "auth_second_step": "1",
                # 'hw_version_2': '1.7-BD-00',
                # "hw_version_2": hw_version_2,
            }

        if param_mode == "basic":
            host_params = {
                "sn": sn,
                "device_id": "",
                'timestamp': str(timestamp),
            }

        profile_params = dict(host_params)

    profile_data = make_request(profile_url, method="POST", headers=headers, params=profile_params, response_type="json")

    js_data = {}
    play_token = None
    status = 0
    blocked = "0"
    id = ""
    mac = ""

    if profile_data:
        js_data = profile_data.get("js", {})

        if js_data:
            play_token = js_data.get("play_token", None)
            status = js_data.get("status", 0)
            blocked = js_data.get("blocked", "0")
            mac = js_data.get("mac", "")
            id = js_data.get("id", "")

    return play_token, status, blocked, mac, id
