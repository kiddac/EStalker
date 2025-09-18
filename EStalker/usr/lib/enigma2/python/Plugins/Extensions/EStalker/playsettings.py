#!/usr/bin/python
# -*- coding: utf-8 -*-

# Standard library imports
import os
import json

# Enigma2 components
from Components.ActionMap import ActionMap
from Components.ConfigList import ConfigListScreen
from Components.config import getConfigListEntry, ConfigText, ConfigSelection, ConfigYesNo, ConfigEnableDisable, NoSave
from Components.Pixmap import Pixmap
from Screens.MessageBox import MessageBox
from Screens.Screen import Screen

# Local application/library-specific imports
from . import _
from . import estalker_globals as glob
from .plugin import skin_directory, cfg
from .eStaticText import StaticText

playlist_file = cfg.playlist_file.value
playlists_json = cfg.playlists_json.value


class EStalker_Settings(ConfigListScreen, Screen):
    ALLOW_SUSPEND = True

    def __init__(self, session):
        Screen.__init__(self, session)
        self.session = session

        skin_path = os.path.join(skin_directory, cfg.skin.value)
        skin = os.path.join(skin_path, "settings.xml")

        if os.path.exists("/var/lib/dpkg/status"):
            skin = os.path.join(skin_path, "DreamOS/settings.xml")

        with open(skin, "r") as f:
            self.skin = f.read()

        self.setup_title = _("Playlist Settings")

        self.onChangedEntry = []

        self.list = []
        ConfigListScreen.__init__(self, self.list, session=self.session, on_change=self.changedEntry)

        self["key_red"] = StaticText(_("Back"))
        self["key_green"] = StaticText(_("Save"))

        self["VKeyIcon"] = Pixmap()
        self["VKeyIcon"].hide()
        self["HelpWindow"] = Pixmap()
        self["HelpWindow"].hide()

        self["actions"] = ActionMap(["EStalkerActions"], {
            "cancel": self.cancel,
            "red": self.cancel,
            "green": self.save,
        }, -2)

        self.onFirstExecBegin.append(self.initConfig)
        self.onLayoutFinish.append(self.__layoutFinished)

    def clear_caches(self):
        try:
            with open("/proc/sys/vm/drop_caches", "w") as drop_caches:
                drop_caches.write("1\n2\n3\n")
        except IOError:
            pass

    def __layoutFinished(self):
        self.setTitle(self.setup_title)

    def cancel(self, answer=None):
        if answer is None:
            if self["config"].isChanged():
                self.session.openWithCallback(self.cancel, MessageBox, _("Really close without saving settings?"))
            else:
                self.close()
        elif answer:
            for x in self["config"].list:
                x[1].cancel()

            self.close()

    def initConfig(self):
        live_streamtype_choices = [("1", "DVB(1)"), ("4097", "IPTV(4097)")]
        vod_streamtype_choices = [("4097", "IPTV(4097)")]

        if os.path.exists("/usr/bin/gstplayer"):
            live_streamtype_choices.append(("5001", "GStreamer(5001)"))
            vod_streamtype_choices.append(("5001", "GStreamer(5001)"))

        if os.path.exists("/usr/bin/exteplayer3"):
            live_streamtype_choices.append(("5002", "ExtePlayer(5002)"))
            vod_streamtype_choices.append(("5002", "ExtePlayer(5002)"))

        if os.path.exists("/usr/bin/apt-get"):
            live_streamtype_choices.append(("8193", "DreamOS GStreamer(8193)"))
            vod_streamtype_choices.append(("8193", "DreamOS GStreamer(8193)"))

        # playlist_info = glob.active_playlist.get("playlist_info", {})
        player_info = glob.active_playlist.get("player_info", {})

        self.liveType = str(player_info.get("livetype", ""))
        self.vodType = str(player_info.get("vodtype", ""))
        self.showlive = player_info.get("showlive", False)
        self.showvod = player_info.get("showvod", False)
        self.showseries = player_info.get("showseries", False)
        self.showcatchup = player_info.get("showcatchup", False)
        self.showadult = player_info.get("showadult", False)

        self.liveTypeCfg = NoSave(ConfigSelection(default=self.liveType, choices=live_streamtype_choices))
        self.vodTypeCfg = NoSave(ConfigSelection(default=self.vodType, choices=vod_streamtype_choices))
        self.showliveCfg = NoSave(ConfigYesNo(default=self.showlive))
        self.showvodCfg = NoSave(ConfigYesNo(default=self.showvod))
        self.showseriesCfg = NoSave(ConfigYesNo(default=self.showseries))
        self.showcatchupCfg = NoSave(ConfigYesNo(default=self.showcatchup))
        self.showadultCfg = NoSave(ConfigYesNo(default=self.showadult))

        self.createSetup()

    def createSetup(self):
        self.list = [
            getConfigListEntry(_("Show LIVE category:"), self.showliveCfg),
            getConfigListEntry(_("Show VOD category:"), self.showvodCfg),
            getConfigListEntry(_("Show SERIES category:"), self.showseriesCfg),
            getConfigListEntry(_("Show CATCHUP category:"), self.showcatchupCfg),
        ]

        if self.showliveCfg.value:
            self.list.append(getConfigListEntry(_("Stream Type LIVE:"), self.liveTypeCfg))

        if self.showvodCfg.value or self.showseriesCfg.value:
            self.list.append(getConfigListEntry(_("Stream Type VOD/SERIES:"), self.vodTypeCfg))

        self.list.append(getConfigListEntry(_("Show Adult channels:"), self.showadultCfg))
        self["config"].list = self.list
        self["config"].l.setList(self.list)
        self.handleInputHelpers()

    def handleInputHelpers(self):
        from enigma import ePoint
        currConfig = self["config"].getCurrent()

        if currConfig is not None:
            if isinstance(currConfig[1], ConfigText):
                if "VKeyIcon" in self:
                    try:
                        self["VirtualKB"].setEnabled(True)
                    except:
                        pass

                    try:
                        self["virtualKeyBoardActions"].setEnabled(True)
                    except:
                        pass
                    self["VKeyIcon"].show()

                if "HelpWindow" in self and currConfig[1].help_window and currConfig[1].help_window.instance is not None:
                    helpwindowpos = self["HelpWindow"].getPosition()
                    currConfig[1].help_window.instance.move(ePoint(helpwindowpos[0], helpwindowpos[1]))

            else:
                if "VKeyIcon" in self:
                    try:
                        self["VirtualKB"].setEnabled(False)
                    except:
                        pass

                    try:
                        self["virtualKeyBoardActions"].setEnabled(False)
                    except:
                        pass
                    self["VKeyIcon"].hide()

    def changedEntry(self):
        self.item = self["config"].getCurrent()
        for x in self.onChangedEntry:
            x()

        try:
            if isinstance(self["config"].getCurrent()[1], ConfigEnableDisable) or isinstance(self["config"].getCurrent()[1], ConfigYesNo) or isinstance(self["config"].getCurrent()[1], ConfigSelection):
                self.createSetup()
        except:
            pass

    def getCurrentEntry(self):
        return self["config"].getCurrent() and self["config"].getCurrent()[0] or ""

    def getCurrentValue(self):
        return self["config"].getCurrent() and str(self["config"].getCurrent()[1].getText()) or ""

    def save(self):
        self.playlists_all = self.getPlaylistJson()

        playlist_info = glob.active_playlist.get("playlist_info", {})
        player_info = glob.active_playlist.get("player_info", {})

        self.host = playlist_info.get("host", "")
        self.mac = playlist_info.get("mac", "")

        if self["config"].isChanged():
            showlive = self.showliveCfg.value
            showvod = self.showvodCfg.value
            showseries = self.showseriesCfg.value
            showcatchup = self.showcatchupCfg.value
            livetype = self.liveTypeCfg.value
            vodtype = self.vodTypeCfg.value
            showadult = self.showadultCfg.value

            player_info["showlive"] = showlive
            player_info["showvod"] = showvod
            player_info["showseries"] = showseries
            player_info["showcatchup"] = showcatchup
            player_info["livetype"] = livetype
            player_info["vodtype"] = vodtype
            player_info["showadult"] = showadult

        self.getPlaylistUserFile()

    def getPlaylistJson(self):
        playlists_all = []
        if os.path.exists(playlists_json) and os.stat(playlists_json).st_size > 0:
            try:
                with open(playlists_json) as f:
                    playlists_all = json.load(f)
            except json.JSONDecodeError as e:
                print("Error loading playlists:", e)
                os.remove(playlists_json)
        return playlists_all

    def getPlaylistUserFile(self):
        for index, playlist in enumerate(self.playlists_all):
            playlist_info = playlist.get("playlist_info", {})
            if all(key in playlist_info for key in ["host", "mac"]):
                if (playlist_info["host"], playlist_info["mac"]) == (self.host, self.mac):
                    self.playlists_all[index] = glob.active_playlist
                    break
        self.writeJsonFile()

    def writeJsonFile(self):
        with open(playlists_json, "w") as f:
            json.dump(self.playlists_all, f)
        self.clear_caches()
        self.close()
