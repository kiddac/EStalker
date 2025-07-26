#!/usr/bin/python
# -*- coding: utf-8 -*-

import os
import shutil
import sys
import twisted.python.runtime

from . import _

from Components.config import config, ConfigSubsection, ConfigSelection, ConfigDirectory, ConfigYesNo, ConfigSelectionNumber, ConfigPIN, ConfigInteger, configfile, ConfigText
from enigma import getDesktop, addFont
from Plugins.Plugin import PluginDescriptor

try:
    from multiprocessing.pool import ThreadPool
    hasMultiprocessing = True
except ImportError:
    hasMultiprocessing = False

try:
    from concurrent.futures import ThreadPoolExecutor
    if twisted.python.runtime.platform.supportsThreads():
        hasConcurrent = True
    else:
        hasConcurrent = False
except ImportError:
    hasConcurrent = False

pythonFull = float(str(sys.version_info.major) + "." + str(sys.version_info.minor))
pythonVer = sys.version_info.major

isDreambox = os.path.exists("/usr/bin/apt-get")

isVTI = os.path.exists("/etc/vtiversion.info")

debugs = False

with open("/usr/lib/enigma2/python/Plugins/Extensions/EStalker/version.txt", "r") as f:
    version = f.readline()

screenwidth = getDesktop(0).size()

dir_etc = "/etc/enigma2/estalker/"
dir_tmp = "/tmp/estalker/"
dir_plugins = "/usr/lib/enigma2/python/Plugins/Extensions/EStalker/"


if screenwidth.width() == 2560:
    skin_directory = os.path.join(dir_plugins, "skin/uhd/")
elif screenwidth.width() > 1280:
    skin_directory = os.path.join(dir_plugins, "skin/fhd/")
else:
    skin_directory = os.path.join(dir_plugins, "skin/hd/")

folders = [folder for folder in os.listdir(skin_directory) if folder != "common"]

languages = [
    ("", "English"),
    ("de-DE", "Deutsch"),
    ("es-ES", "Español"),
    ("fr-FR", "Français"),
    ("it-IT", "Italiano"),
    ("nl-NL", "Nederlands"),
    ("tr-TR", "Türkçe"),
    ("cs-CZ", "Český"),
    ("da-DK", "Dansk"),
    ("hr-HR", "Hrvatski"),
    ("hu-HU", "Magyar"),
    ("no-NO", "Norsk"),
    ("pl-PL", "Polski"),
    ("pt-PT", "Português"),
    ("ro-RO", "Română"),
    ("ru-RU", "Pусский"),
    ("sh-SH", "Srpski"),
    ("sk-SK", "Slovenčina"),
    ("fi-FI", "suomi"),
    ("sv-SE", "svenska"),
    ("uk-UA", "Український"),
    ("ar-SA", "العربية"),
    ("bg-BG", "български език"),
    ("el-GR", "ελληνικά"),
    ("sq-AL", "shqip"),
    ("zh-CN", "中文")
]

# Configurations initialization
config.plugins.EStalker = ConfigSubsection()
cfg = config.plugins.EStalker

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

cfg.livetype = ConfigSelection(default="4097", choices=live_streamtype_choices)
cfg.vodtype = ConfigSelection(default="4097", choices=vod_streamtype_choices)


cfg.location = ConfigDirectory(default=dir_etc)
cfg.main = ConfigYesNo(default=True)
cfg.livepreview = ConfigYesNo(default=False)
cfg.stopstream = ConfigYesNo(default=False)
cfg.skin = ConfigSelection(default="default", choices=folders)
cfg.timeout = ConfigSelectionNumber(1, 20, 1, default=20, wraparound=True)
cfg.TMDBLanguage2 = ConfigSelection(default="", choices=languages)
# cfg.catchupstart = ConfigSelectionNumber(0, 30, 1, default=0, wraparound=True)
# cfg.catchupend = ConfigSelectionNumber(0, 30, 1, default=0, wraparound=True)
cfg.subs = ConfigYesNo(default=False)
cfg.skipplaylistsscreen = ConfigYesNo(default=False)
cfg.adult = ConfigYesNo(default=False)
cfg.adultpin = ConfigPIN(default=0000)
cfg.retries = ConfigSubsection()
cfg.retries.adultpin = ConfigSubsection()
cfg.retries.adultpin.tries = ConfigInteger(default=3)
cfg.retries.adultpin.time = ConfigInteger(default=3)
cfg.location_valid = ConfigYesNo(default=True)

cfg.channelpicons = ConfigYesNo(default=True)
cfg.infobarpicons = ConfigYesNo(default=True)
cfg.channelcovers = ConfigYesNo(default=True)
cfg.infobarcovers = ConfigYesNo(default=True)

# Set default file paths
playlist_file = os.path.join(dir_etc, "playlists.txt")
playlists_json = os.path.join(dir_etc, "playlists-data-2.json")

# Set skin and font paths
skin_path = os.path.join(skin_directory, cfg.skin.value)
common_path = os.path.join(skin_directory, "common/")

location = cfg.location.value

if location:
    try:
        if os.path.exists(location):
            playlist_file = os.path.join(cfg.location.value, "playlists.txt")
            cfg.location_valid.setValue(True)
        else:
            os.makedirs(location)  # Create directory if it doesn't exist
            playlist_file = os.path.join(location, "playlists.txt")

            cfg.location_valid.setValue(True)
    except:
        pass
else:

    cfg.location.setValue(dir_etc)
    cfg.location_valid.setValue(False)

cfg.playlist_file = ConfigText(playlist_file)
cfg.playlists_json = ConfigText(playlists_json)

cfg.save()
configfile.save()

font_folder = os.path.join(dir_plugins, "fonts/")

# create folder for working files
if not os.path.exists(dir_etc):
    os.makedirs(dir_etc)

# delete temporary folder and contents
if os.path.exists(dir_tmp):
    shutil.rmtree("/tmp/estalker")

# create temporary folder for downloaded files
if not os.path.exists(dir_tmp):
    os.makedirs(dir_tmp)

# check if playlists.txt file exists in specified location
if not os.path.isfile(cfg.playlist_file.value):
    with open(cfg.playlist_file.value, "a") as f:
        f.close()

# check if playlists-data.json file exists in specified location
if not os.path.isfile(cfg.playlists_json.value):
    with open(cfg.playlists_json.value, "a") as f:
        f.close()


def main(session, **kwargs):
    from . import mainmenu
    session.open(mainmenu.EStalker_MainMenu)
    return


def mainmenu(menu_id, **kwargs):
    if menu_id == "mainmenu":
        return [(_("EStalker"), main, "EStalker", 50)]
    else:
        return []


def Plugins(**kwargs):
    addFont(os.path.join(font_folder, "m-plus-rounded-1c-regular.ttf"), "estalkerregular", 100, 0)
    addFont(os.path.join(font_folder, "m-plus-rounded-1c-medium.ttf"), "estalkerbold", 100, 0)
    addFont(os.path.join(font_folder, "slyk-medium.ttf"), "slykregular", 100, 0)
    addFont(os.path.join(font_folder, "slyk-bold.ttf"), "slykbold", 100, 0)
    addFont(os.path.join(font_folder, "classfont2.ttf"), "iconfont", 100, 0)

    iconFile = "icons/plugin-icon_sd.png"
    if screenwidth.width() > 1280:
        iconFile = "icons/plugin-icon.png"

    description = _("IPTV Ministra stalker player by KiddaC")
    pluginname = _("EStalker")

    main_menu = PluginDescriptor(name=pluginname, description=description, where=PluginDescriptor.WHERE_MENU, fnc=mainmenu, needsRestart=True)

    extensions_menu = PluginDescriptor(name=pluginname, description=description, where=PluginDescriptor.WHERE_EXTENSIONSMENU, fnc=main, needsRestart=True)

    result = [
        PluginDescriptor(name=pluginname, description=description, where=PluginDescriptor.WHERE_PLUGINMENU, icon=iconFile, fnc=main)
    ]

    result.append(extensions_menu)

    if cfg.main.value:
        result.append(main_menu)

    return result
