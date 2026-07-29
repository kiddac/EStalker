#!/usr/bin/python
# -*- coding: utf-8 -*-

try:
    from http.client import HTTPConnection
    HTTPConnection.debuglevel = 0
except:
    from httplib import HTTPConnection
    HTTPConnection.debuglevel = 0

from twisted.internet import reactor
from twisted.internet.defer import DeferredSemaphore
from twisted.web.client import Agent, readBody
from twisted.web.http_headers import Headers
from twisted.internet.protocol import Factory

import json
import sys
import gzip
import io
import hashlib

from . import estalker_globals as glob
from .utils import get_local_timezone

try:
    from twisted.web.client import BrowserLikePolicyForHTTPS
    contextFactory = BrowserLikePolicyForHTTPS()
except ImportError:
    from twisted.web.client import WebClientContextFactory
    contextFactory = WebClientContextFactory()

try:
    from urllib import quote
except ImportError:
    from urllib.parse import quote


Factory.noisy = False


class EStalker_EPG_Short:
    def __init__(self, visible_ids, done_callback=None, partial_callback=None):
        # optional partial callback for immediate display
        self.done_callback = done_callback
        self.partial_callback = partial_callback
        self.visible_ids = visible_ids
        self.epg_data = []
        self.failed_ids = set()
        self.responses_received = 0
        self.total_requests = len(visible_ids)
        self.retry_counts = {}
        self.agent = Agent(reactor, contextFactory=contextFactory)
        # MAG/Stalker portals are often sensitive to parallel short-EPG calls.
        self.request_semaphore = DeferredSemaphore(2)
        self.prepare()

    def download_single_epg(self, ch_id):
        return self.request_semaphore.run(self._download_single_epg, ch_id)

    def _download_single_epg(self, ch_id):
        url = self.portal + "?type=itv&action=get_short_epg&ch_id={}&limit=10&size=10&JsHttpRequest=1-xml".format(ch_id)
        d = self.agent.request(b'GET', url.encode(), self.headers)
        d.addCallbacks(
            lambda response, ch_id=ch_id: self.handle_response(response, ch_id),
            lambda failure, ch_id=ch_id: self.handle_error(failure, ch_id)
        )
        cancel_request = getattr(d, "cancel", None)
        if cancel_request:
            timeout_call = reactor.callLater(6.0, cancel_request)

            def cancel_timeout(result):
                if timeout_call.active():
                    timeout_call.cancel()
                return result

            d.addBoth(cancel_timeout)
        return d

    def prepare(self):
        timezone = get_local_timezone()
        token = glob.active_playlist["playlist_info"]["token"]
        domain = str(glob.active_playlist["playlist_info"].get("domain", ""))
        port = glob.active_playlist["playlist_info"].get("port", "")
        host = str(glob.active_playlist["playlist_info"].get("host", "")).rstrip("/")
        mac = glob.active_playlist["playlist_info"].get("mac", "").upper()
        self.portal = glob.active_playlist["playlist_info"].get("portal", None)
        path_prefix = glob.active_playlist["playlist_info"].get("path_prefix", "")
        referer = host + path_prefix + "index.html"
        sn = hashlib.md5(mac.encode()).hexdigest().upper()[:13]
        adid = hashlib.md5((sn + mac).encode()).hexdigest()
        encoded_mac = quote(mac, safe='')
        encoded_timezone = quote(timezone, safe='')

        base_headers = {
            b"Pragma": [b"no-cache"],
            b"Accept-Language": [b"en-US,en;q=0.5"],
            b"Accept-Encoding": [b"gzip, deflate"],
            b"Host": [("{}:{}".format(domain, port) if port else domain).encode()],
            b"User-Agent": [b"Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 (KHTML, like Gecko) MAG250 stbapp ver: 2 rev: 369 Safari/533.3"],
            b"X-User-Agent": [b"Model: MAG250; Link: WiFi"],
            b"Connection": [b"Close"],
            b"Referer": [referer.encode()],
        }

        if self.portal and "/stalker_portal/" in self.portal:
            host_headers = {
                b"Cookie": [("mac={}; stb_lang=en; timezone={}; adid={}".format(encoded_mac, encoded_timezone, adid)).encode()]
            }
        else:
            host_headers = {
                b"Cookie": [("mac={}; stb_lang=en; timezone={}".format(encoded_mac, encoded_timezone)).encode()]
            }

        base_headers.update(host_headers)
        base_headers[b"Authorization"] = [("Bearer " + token).encode()]
        self.headers = Headers(base_headers)
        self.download_epgs()

    def download_epgs(self):
        for ch_id in self.visible_ids:
            self.download_single_epg(ch_id)

    def handle_response(self, response, ch_id):
        if response.code >= 400:
            self.retry_or_complete(ch_id)
            return

        d = readBody(response)
        d.addCallbacks(
            lambda body: self.process_body(body, ch_id, response),
            lambda failure, ch_id=ch_id: self.handle_error(failure, ch_id)
        )
        return d

    def process_body(self, body, ch_id, response):
        try:
            encoding_headers = response.headers.getRawHeaders(
                b"Content-Encoding",
                [b""]
            )
            encoding = encoding_headers[0]

            if isinstance(encoding, bytes):
                encoding = encoding.decode("utf-8")

            encoding = encoding.lower()

            if encoding == "gzip":
                with gzip.GzipFile(fileobj=io.BytesIO(body)) as f:
                    data = f.read()
            else:
                data = body

            if sys.version_info[0] == 3 and isinstance(data, bytes):
                data = data.decode("utf-8", "ignore")

            data = data.strip()

            if data[:1] not in ("{", "["):
                raise ValueError("Invalid short EPG response")

            json_data = json.loads(data)
            if not isinstance(json_data, dict):
                raise ValueError("Invalid short EPG response")

            epg_events = json_data.get("js", [])
            if epg_events is None:
                epg_events = []
            if not isinstance(epg_events, list):
                raise ValueError("Invalid short EPG response")

            # A busy portal can return HTTP 200 with an empty js list. Verify an
            # empty result before accepting that the channel genuinely has no EPG.
            if not epg_events and self.retry_empty_response(ch_id):
                return

            for event in epg_events:
                if isinstance(event, dict) and not event.get("ch_id"):
                    event["ch_id"] = str(ch_id)

            if epg_events:
                self.epg_data.extend(epg_events)

                if self.partial_callback:
                    self.partial_callback({"js": epg_events})

        except Exception:
            self.retry_or_complete(ch_id)
            return

        self.failed_ids.discard(str(ch_id))
        self.responses_received += 1
        self.check_complete()

    def check_complete(self):
        if self.responses_received >= self.total_requests:
            if self.done_callback:
                self.done_callback({
                    "js": self.epg_data,
                    "failed_ids": list(self.failed_ids),
                })

    def handle_error(self, failure, ch_id=None):
        if ch_id is not None:
            self.retry_or_complete(ch_id)
            return

        self.responses_received += 1
        self.check_complete()

    def retry_or_complete(self, ch_id):
        retry_key = str(ch_id)
        retries = self.retry_counts.get(retry_key, 0)
        if retries < 2:
            self.retry_counts[retry_key] = retries + 1
            reactor.callLater(0.5 * (retries + 1), self.download_single_epg, ch_id)
            return

        self.failed_ids.add(retry_key)
        self.responses_received += 1
        self.check_complete()

    def retry_empty_response(self, ch_id):
        retry_key = str(ch_id)
        retries = self.retry_counts.get(retry_key, 0)
        if retries >= 2:
            return False

        self.retry_counts[retry_key] = retries + 1
        reactor.callLater(0.5 * (retries + 1), self.download_single_epg, ch_id)
        return True
