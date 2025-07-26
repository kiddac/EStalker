#!/usr/bin/python
# -*- coding: utf-8 -*-

from collections import OrderedDict
import json
import os
import re

try:
    from urllib.parse import urlparse
except ImportError:
    from urlparse import urlparse

from .plugin import cfg

playlist_file = cfg.playlist_file.value
playlists_json = cfg.playlists_json.value


def process_files():
    if not os.path.isfile(playlist_file):
        with open(playlist_file, "a"):
            pass

    if not os.path.isfile(playlists_json):
        with open(playlists_json, "a"):
            pass

    try:
        with open(playlist_file, "r") as f:
            lines = f.readlines()
    except:
        return

    mac_regex = re.compile(r'^([0-9A-Fa-f]{2}:){5}[0-9A-Fa-f]{2}$')

    grouped = OrderedDict()
    current_url = None
    collecting = False
    raw_lines_preserved = []

    for raw_line in lines:
        raw_lines_preserved.append(raw_line)
        stripped_line = raw_line.strip()

        if not stripped_line:
            continue

        if stripped_line.startswith("#") and (stripped_line.lstrip("#").strip().startswith("http://") or stripped_line.lstrip("#").strip().startswith("https://")):
            collecting = False
            url = stripped_line.lstrip("#").strip()

            if not url.endswith("/"):
                cleaned_url = url + "/"
            else:
                cleaned_url = url

            cleaned_url = "# " + cleaned_url
            current_url = cleaned_url
            collecting = True

        elif stripped_line.startswith("http://") or stripped_line.startswith("https://"):
            collecting = False  # Stop collecting previous block
            if not stripped_line.endswith("/"):
                cleaned_url = stripped_line + "/"
            else:
                cleaned_url = stripped_line

            current_url = cleaned_url
            collecting = True

        elif collecting and current_url is not None and mac_regex.match(stripped_line):
            if current_url not in grouped:
                grouped[current_url] = []

            grouped[current_url].append(stripped_line.upper())

    # Deduplicate MACs per URL
    for key in grouped:
        grouped[key] = list(OrderedDict.fromkeys(grouped[key]))

    # Write original lines back to file (preserving comments and formatting)
    try:
        with open(playlist_file, "w") as f:
            f.writelines(raw_lines_preserved)
    except:
        pass

    # Build JSON file from non-commented entries
    existing_entries = []
    try:
        with open(playlists_json, "r") as json_file:
            existing_entries = json.load(json_file)
    except:
        existing_entries = []

    existing_lookup = {}
    for entry in existing_entries:
        info = entry.get("playlist_info", {})
        key = (
            info.get("domain", ""),
            str(info.get("port", "")),
            info.get("mac", "").upper()
        )
        existing_lookup[key] = entry

    playlists_grouped = []
    valid_keys = set()
    index = 0

    livetype = cfg.livetype.value
    vodtype = cfg.vodtype.value

    for url, mac_lines in grouped.items():
        if url.startswith("#"):
            continue

        parsed_uri = urlparse(url)
        protocol = parsed_uri.scheme + "://"
        domain = parsed_uri.hostname.lower() if parsed_uri.hostname else ""
        port = parsed_uri.port

        # Remove default ports (80 for http, 443 for https)
        if (parsed_uri.scheme == "http" and port == 80) or (parsed_uri.scheme == "https" and port == 443):
            port = ""

        host = protocol + domain + (":" + str(port) if port else "")
        for mac in mac_lines:
            mac_stripped = mac.upper()
            key = (domain, str(port), mac_stripped)
            if key in valid_keys:
                continue
            valid_keys.add(key)

            if key in existing_lookup:
                existing_entry = existing_lookup[key]
                existing_entry["playlist_info"]["index"] = index

                # Ensure "url" is added if missing
                if "url" not in existing_entry["playlist_info"]:
                    existing_entry["playlist_info"]["url"] = url

                playlists_grouped.append(existing_entry)

            else:
                playlists_grouped.append({
                    "playlist_info": {
                        "index": index,
                        "url": url,
                        "protocol": protocol,
                        "domain": domain,
                        "port": port,
                        "host": host,
                        "mac": mac_stripped,
                        "token": "",
                        "token_random": "",
                        "valid": True,
                        "expiry": "",
                        "version": "",
                        "portal": "",
                        "play_token": "",
                        "status": 0,
                        "blocked": "0",
                        "temp_username": "",
                        "temp_password": "",
                        "active_connections": "",
                        "max_connections": "",
                        "temp_xtream_get_api": "",
                        "temp_xtream_player_api": ""
                    },
                    "player_info": OrderedDict([
                        ("livetype", livetype),
                        ("vodtype", vodtype),
                        ("livehidden", []),
                        ("channelshidden", []),
                        ("vodhidden", []),
                        ("vodstreamshidden", []),
                        ("serieshidden", []),
                        ("seriestitleshidden", []),
                        ("seriesseasonshidden", []),
                        ("seriesepisodeshidden", []),
                        ("catchuphidden", []),
                        ("catchupchannelshidden", []),
                        ("livefavourites", []),
                        ("vodfavourites", []),
                        ("seriesfavourites", []),
                        ("liverecents", []),
                        ("vodrecents", []),
                        ("vodwatched", []),
                        ("serieswatched", []),
                        ("showlive", True),
                        ("showvod", True),
                        ("showseries", True),
                        ("showcatchup", True),
                        ("showadult", False),
                        ("serveroffset", 0),
                        ("catchupoffset", 0),
                        ("epgoffset", 0)
                    ]),
                    "data": {
                        "live_categories": {},
                        "vod_categories": {},
                        "series_categories": {},
                        "live_streams": [],
                        "catchup": False,
                        "customsids": False,
                        "epg_date": "",
                        "data_downloaded": False,
                        "fail_count": 0
                    }
                })
            index += 1

    with open(playlists_json, "w") as json_file:
        json.dump(playlists_grouped, json_file, indent=4)

    return playlists_grouped
