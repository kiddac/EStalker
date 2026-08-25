#!/usr/bin/python
# -*- coding: utf-8 -*-

try:
    from http.client import HTTPConnection
    HTTPConnection.debuglevel = 0
except:
    from httplib import HTTPConnection
    HTTPConnection.debuglevel = 0

from twisted.internet import reactor
from twisted.internet.threads import deferToThread
from twisted.web.client import Agent, readBody
from twisted.web.http_headers import Headers
from twisted.internet.protocol import Factory

import json
import sys
import gzip
import io
import hashlib
import zlib

from . import estalker_globals as glob
from .utils import get_local_timezone, reauthorize_portal

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
        # A channel may appear more than once in the visible list. Fetch it once
        # so completion accounting cannot wait for a duplicate response.
        self.visible_ids = []
        seen_ids = set()
        for ch_id in visible_ids:
            if ch_id not in seen_ids:
                seen_ids.add(ch_id)
                self.visible_ids.append(ch_id)
        self.epg_data = []
        self.responses_received = 0
        self.total_requests = len(self.visible_ids)
        self.done_called = False
        self.completed_ids = set()
        self.retry_503 = {}
        self.auth_retried = set()
        self.auth_queue = set()
        self.auth_in_progress = False
        self.auth_attempted = False
        self.auth_generation = 0
        self.agent = Agent(reactor, contextFactory=contextFactory)
        self.prepare()

    def download_single_epg(self, ch_id):
        if ch_id in self.completed_ids:
            return

        generation = self.auth_generation
        url = self.portal + "?type=itv&action=get_short_epg&ch_id={}&size=10&JsHttpRequest=1-xml".format(ch_id)
        d = self.agent.request(b'GET', url.encode(), self.headers)
        d.addCallback(lambda response, ch_id=ch_id, generation=generation: self.handle_response(response, ch_id, generation))
        d.addErrback(lambda failure, ch_id=ch_id, generation=generation: self.handle_error(failure, ch_id, generation))

    def prepare(self):
        timezone = get_local_timezone()
        playlist_info = glob.active_playlist["playlist_info"]
        self.token = playlist_info.get("token", "")
        domain = str(glob.active_playlist["playlist_info"].get("domain", ""))
        port = glob.active_playlist["playlist_info"].get("port", "")
        self.host = str(glob.active_playlist["playlist_info"].get("host", "")).rstrip("/")
        self.mac = glob.active_playlist["playlist_info"].get("mac", "").upper()
        self.portal = glob.active_playlist["playlist_info"].get("portal", None)
        path_prefix = glob.active_playlist["playlist_info"].get("path_prefix", "")
        referer = self.host + path_prefix + "index.html"
        sn = hashlib.md5(self.mac.encode()).hexdigest().upper()[:13]
        adid = hashlib.md5((sn + self.mac).encode()).hexdigest()
        encoded_mac = quote(self.mac, safe='')
        encoded_timezone = quote(timezone, safe='')

        saved_headers = playlist_info.get("headers", {})
        self.request_headers = saved_headers.copy() if isinstance(saved_headers, dict) else {}

        # Compatibility fallback for playlists saved before the xpcom-derived
        # authenticated headers were persisted.
        if not self.request_headers:
            cookie = "mac={}; stb_lang=en; timezone={}".format(encoded_mac, encoded_timezone)
            if self.portal and "/stalker_portal/" in self.portal:
                cookie += "; adid={}".format(adid)

            self.request_headers = {
                "Pragma": "no-cache",
                "Accept-Language": "en-US,en;q=0.5",
                "Accept-Encoding": "gzip, deflate",
                "Host": "{}:{}".format(domain, port) if port else domain,
                "User-Agent": "Mozilla/5.0 (QtEmbedded; U; Linux; C) AppleWebKit/533.3 (KHTML, like Gecko) MAG200 stbapp ver: 2 rev: 250 Safari/533.3",
                "X-User-Agent": "Model: MAG250; Link: WiFi",
                "Connection": "Close",
                "Referer": referer,
                "Cookie": cookie,
            }

        self.request_headers["Authorization"] = "Bearer " + self.token
        self._update_twisted_headers()
        self.download_epgs()

    def _update_twisted_headers(self):
        twisted_headers = {}
        for name, value in self.request_headers.items():
            values = value if isinstance(value, (list, tuple)) else [value]
            twisted_headers[str(name).encode("utf-8")] = [str(item).encode("utf-8") for item in values]
        self.headers = Headers(twisted_headers)

    def download_epgs(self):
        if not self.visible_ids:
            self.check_complete()
            return

        for ch_id in self.visible_ids:
            self.download_single_epg(ch_id)

    def handle_response(self, response, ch_id, generation):
        if response.code == 503:
            retries = self.retry_503.get(ch_id, 0)
            if retries < 2:
                self.retry_503[ch_id] = retries + 1
                reactor.callLater(1.0, self.download_single_epg, ch_id)
            else:
                self._retry_with_reauthorization(ch_id, generation)
            return

        if response.code < 200 or response.code >= 300:
            self._retry_with_reauthorization(ch_id, generation)
            return

        d = readBody(response)
        d.addCallbacks(
            lambda body, ch_id=ch_id, generation=generation: self.process_body(body, ch_id, response, generation),
            lambda failure, ch_id=ch_id, generation=generation: self.handle_error(failure, ch_id, generation)
        )

    def process_body(self, body, ch_id, response, generation):
        try:
            encoding_headers = response.headers.getRawHeaders(b"Content-Encoding", [b""])
            encoding = encoding_headers[0].decode('utf-8').lower() if isinstance(encoding_headers[0], bytes) else encoding_headers[0].lower()

            if encoding == "gzip":
                with gzip.GzipFile(fileobj=io.BytesIO(body)) as f:
                    data = f.read()
            elif encoding == "deflate":
                data = zlib.decompress(body)
            else:
                data = body

            if not data:
                self._retry_with_reauthorization(ch_id, generation)
                return

            if sys.version_info[0] == 3:
                data = data.decode('utf-8')

            json_data = json.loads(data)
            epg_events = json_data.get("js", [])

            if epg_events:
                self.epg_data.extend(epg_events)

                if self.partial_callback:
                    self.partial_callback({"js": self.epg_data})

        except Exception as e:
            print(e)
            self._retry_with_reauthorization(ch_id, generation)
            return

        self._mark_complete(ch_id)

    def _retry_with_reauthorization(self, ch_id, generation):
        if ch_id in self.completed_ids:
            return

        # This request was sent before another request refreshed the token.
        # Retry it immediately with the new headers instead of handshaking again.
        if generation < self.auth_generation:
            self.auth_retried.add(ch_id)
            self.download_single_epg(ch_id)
            return

        if ch_id in self.auth_retried or self.auth_attempted and not self.auth_in_progress:
            self._mark_complete(ch_id)
            return

        self.auth_queue.add(ch_id)
        if self.auth_in_progress:
            return

        self.auth_in_progress = True
        self.auth_attempted = True
        d = deferToThread(
            reauthorize_portal,
            self.portal,
            self.host,
            self.mac,
            self.request_headers.copy()
        )
        d.addCallbacks(self._reauthorization_complete, self._reauthorization_failed)

    def _reauthorization_complete(self, result):
        self.auth_in_progress = False
        queued_ids = list(self.auth_queue)
        self.auth_queue.clear()

        if not result:
            for ch_id in queued_ids:
                self._mark_complete(ch_id)
            return

        self.portal, self.token, token_random, self.request_headers, play_token, status, blocked = result
        self.auth_generation += 1
        self._update_twisted_headers()

        glob.active_playlist["playlist_info"].update({
            "portal": self.portal,
            "token": self.token,
            "token_random": token_random,
            "headers": self.request_headers,
            "play_token": play_token,
            "status": status,
            "blocked": blocked,
        })

        for ch_id in queued_ids:
            self.auth_retried.add(ch_id)
            self.download_single_epg(ch_id)

    def _reauthorization_failed(self, failure):
        self.auth_in_progress = False
        queued_ids = list(self.auth_queue)
        self.auth_queue.clear()
        for ch_id in queued_ids:
            self._mark_complete(ch_id)

    def _mark_complete(self, ch_id):
        if ch_id in self.completed_ids:
            return

        self.completed_ids.add(ch_id)
        self.responses_received = len(self.completed_ids)
        self.check_complete()

    def check_complete(self):
        if not self.done_called and self.responses_received >= self.total_requests:
            self.done_called = True
            if self.done_callback:
                self.done_callback({"js": self.epg_data})

    def handle_error(self, failure, ch_id=None, generation=0):
        if hasattr(failure.value, 'response'):
            response = failure.value.response
            code = getattr(response, 'code', 0)
            if code == 503 and ch_id is not None:
                retries = self.retry_503.get(ch_id, 0)
                if retries < 2:
                    self.retry_503[ch_id] = retries + 1
                    reactor.callLater(1.0, self.download_single_epg, ch_id)
                else:
                    self._retry_with_reauthorization(ch_id, generation)
                return

        if ch_id is not None:
            self._retry_with_reauthorization(ch_id, generation)
