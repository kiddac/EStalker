#!/bin/sh
## setup command=wget https://raw.githubusercontent.com/kiddac/EStalker/master/installer.sh -O - | /bin/sh

description="
What is new:
- Online update checking when EStalker is opened
"

PLUGINPATH=/usr/lib/enigma2/python/Plugins/Extensions/EStalker
TMPDIR=/tmp/EStalker_update
ARCHIVE_ROOT=EStalker-master/EStalker

echo " ** Download and install EStalker ** "
rm -rf "$TMPDIR"
mkdir -p "$TMPDIR"
cd "$TMPDIR" || exit 1

if ! wget -q "https://github.com/kiddac/EStalker/archive/refs/heads/master.tar.gz" -O master.tar.gz \
   || ! tar -xzf master.tar.gz \
   || [ ! -f "$ARCHIVE_ROOT/usr/lib/enigma2/python/Plugins/Extensions/EStalker/plugin.py" ]; then
    echo "Download failed. Nothing was changed."
    cd /tmp
    rm -rf "$TMPDIR"
    exit 1
fi

# Never install bytecode built by a different Python version.
find "$ARCHIVE_ROOT/usr" -name '*.py[co]' -exec rm -f {} \; 2>/dev/null
find "$ARCHIVE_ROOT/usr" -type d -name '__pycache__' -prune -exec rm -rf {} \; 2>/dev/null

if ! cp -r "$ARCHIVE_ROOT/usr" /; then
    echo "Copying the files failed. Run the installer again."
    cd /tmp
    rm -rf "$TMPDIR"
    exit 1
fi

# Remove stale bytecode and let the receiver rebuild it after restart.
find "$PLUGINPATH" -name '*.py[co]' -exec rm -f {} \; 2>/dev/null
find "$PLUGINPATH" -type d -name '__pycache__' -prune -exec rm -rf {} \; 2>/dev/null

cd /tmp
rm -rf "$TMPDIR"

if [ ! -f "$PLUGINPATH/plugin.py" ]; then
    echo "EStalker was not installed correctly."
    exit 1
fi

sync
echo
echo "EStalker installed successfully. Restarting Enigma2..."
killall enigma2
exit 0
