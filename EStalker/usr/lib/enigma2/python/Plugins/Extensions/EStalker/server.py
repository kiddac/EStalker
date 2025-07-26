#!/usr/bin/python
# -*- coding: utf-8 -*-

# Standard library imports
import os
import json

try:
    from http.client import HTTPConnection
    HTTPConnection.debuglevel = 0
except ImportError:
    from httplib import HTTPConnection
    HTTPConnection.debuglevel = 0


# Enigma2 components
from Components.ActionMap import ActionMap
from Components.ConfigList import ConfigListScreen
from Components.config import getConfigListEntry, NoSave, ConfigText, ConfigSelection, ConfigNumber
from Components.Pixmap import Pixmap
from Screens.MessageBox import MessageBox
from Screens.Screen import Screen

# Local application/library-specific imports
from . import _
from .plugin import skin_directory, cfg, debugs
from .eStaticText import StaticText
from . import processfiles as loadfiles

playlist_file = cfg.playlist_file.value
playlists_json = cfg.playlists_json.value


class EStalker_AddServer(ConfigListScreen, Screen):

    def __init__(self, session):
        if debugs:
            print("*** __init__ ***")
        Screen.__init__(self, session)
        self.session = session

        skin_path = os.path.join(skin_directory, cfg.skin.value)
        skin = os.path.join(skin_path, "settings.xml")

        if os.path.exists("/var/lib/dpkg/status"):
            skin = os.path.join(skin_path, "DreamOS/settings.xml")

        with open(skin, "r") as f:
            self.skin = f.read()

        self.setup_title = _("Add Playlist")
        self.onChangedEntry = []
        self.list = []
        self.mac_addresses = []

        ConfigListScreen.__init__(self, self.list, session=self.session)

        self["key_red"] = StaticText(_("Back"))
        self["key_green"] = StaticText(_("Save"))
        self["VKeyIcon"] = Pixmap()
        self["VKeyIcon"].hide()
        self["HelpWindow"] = Pixmap()
        self["HelpWindow"].hide()

        self.protocol = "http://"
        self.output = "ts"

        self["actions"] = ActionMap(["EStalkerActions"], {
            "cancel": self.cancel,
            "red": self.cancel,
            "green": self.save,
            "ok": self.okPressed,
        }, -2)

        self.playlists_all = self.getPlaylistJson()
        self.onFirstExecBegin.append(self.initConfig)
        self.onLayoutFinish.append(self.__layoutFinished)

    def __layoutFinished(self):
        self.setTitle(self.setup_title)

    def initConfig(self):
        if debugs:
            print("*** initConfig ***")

        self.protocolCfg = NoSave(ConfigSelection(default=self.protocol, choices=[("http://", "http://"), ("https://", "https://")]))
        self.serverCfg = NoSave(ConfigText(fixed_size=False))
        self.portCfg = NoSave(ConfigText(fixed_size=False))
        self.macCfg = NoSave(ConfigText(default="", fixed_size=False))
        self.createSetup()

    def createSetup(self):
        if debugs:
            print("*** createSetup ***")

        self.list = []
        self.list.append(getConfigListEntry(_("Protocol:"), self.protocolCfg))
        self.list.append(getConfigListEntry(_("Server URL: i.e. domain.xyz"), self.serverCfg))
        self.list.append(getConfigListEntry(_("Port:"), self.portCfg))
        self.list.append(getConfigListEntry(_("MAC Address (12 hex chars, no colons):"), self.macCfg))

        # Show added MAC addresses
        for i, mac in enumerate(self.mac_addresses):
            self.list.append(getConfigListEntry(_("Added MAC #%d:") % (i + 1), NoSave(ConfigText(default=mac, fixed_size=False))))

        self["config"].list = self.list
        self["config"].l.setList(self.list)
        self.handleInputHelpers()

    def okPressed(self):
        if debugs:
            print("*** okPressed ***")

        """Handle OK button press for adding MAC addresses"""
        currConfig = self["config"].getCurrent()
        if currConfig and currConfig[1] == self.macCfg:
            mac = self.macCfg.value.strip()
            if mac:
                if self.validate_mac(mac):
                    formatted_mac = ":".join(mac[i:i + 2] for i in range(0, 12, 2)).upper()
                    self.mac_addresses.append(formatted_mac)
                    self.macCfg.setValue("")
                    self.createSetup()
                    self.session.open(MessageBox, _("MAC address added"), MessageBox.TYPE_INFO, timeout=3)
                else:
                    self.session.open(MessageBox, _("Invalid MAC format (use XXXXXXXXXXXX)"), MessageBox.TYPE_ERROR, timeout=3)
            return

    def validate_mac(self, mac):
        if debugs:
            print("*** validate_mac ***")

        """Validate MAC address format"""
        import re
        return re.match(r"^[0-9A-Fa-f]{12}$", mac) is not None

    def save(self):
        if debugs:
            print("*** save ***")

        """Handle green button press - save configuration"""
        # If MAC field has content, add it first
        if self.macCfg.value.strip():
            self.okPressed()
            return

        # Proceed with saving if no MAC was being added
        if not self.mac_addresses:
            self.session.open(MessageBox, _("At least one MAC address is required"), MessageBox.TYPE_ERROR, timeout=5)
            return

        protocol = self.protocolCfg.value
        domain = self.serverCfg.value.strip().lower()
        port = self.portCfg.value

        host = "{}{}:{}".format(protocol, domain, port) if port else "{}{}".format(protocol, domain)
        urlline = "{}".format(host)

        # Write to playlists.txt

        try:
            with open(playlist_file, 'a') as f:
                f.write('\n' + urlline + '\n')
                for mac in self.mac_addresses:
                    f.write(mac + '\n')
                f.write('\n')

            self.session.open(MessageBox, _("Playlist added successfully!"), MessageBox.TYPE_INFO, timeout=5)
            self.close()

        except IOError as e:
            print("Error writing to playlists.txt:", e)
            self.session.open(MessageBox, _("Error saving playlist"), MessageBox.TYPE_ERROR, timeout=5)

        loadfiles.process_files()

    def cancel(self, answer=None):
        if debugs:
            print("*** cancel ***")

        if answer is None:
            if self["config"].isChanged():
                self.session.openWithCallback(self.cancel, MessageBox, _("Really close without saving settings?"))
            else:
                self.close()
        elif answer:
            for x in self["config"].list:
                x[1].cancel()

            self.close()

    def handleInputHelpers(self):
        if debugs:
            print("*** handleInputHelpers ***")

        from enigma import ePoint
        currConfig = self["config"].getCurrent()

        if currConfig is not None:
            if isinstance(currConfig[1], ConfigText):
                if "VKeyIcon" in self:
                    if isinstance(currConfig[1], ConfigNumber):
                        try:
                            self["VirtualKB"].setEnabled(False)
                        except:
                            pass

                        try:
                            self["virtualKeyBoardActions"].setEnabled(False)
                        except:
                            pass

                        self["VKeyIcon"].hide()
                    else:
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
                    self["VKeyIcon"].hide()

    def getPlaylistJson(self):
        if debugs:
            print("*** getPlaylistJson ***")

        playlists_all = []

        # Check if the playlist file exists and is not empty
        if os.path.exists(playlists_json) and os.path.getsize(playlists_json) > 0:
            try:
                with open(playlists_json) as f:
                    playlists_all = json.load(f)
            except Exception as e:
                print("Error loading playlist JSON:", e)
                os.remove(playlists_json)

        return playlists_all
