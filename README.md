<p align="center"><img src="adguard_logo.png" width="96" alt=""></p>

# Ad Guard for Spotify

A Windows app that watches the Spotify desktop client and deals with ads automatically:
it either **mutes** an ad until it ends, or **restarts Spotify** to skip it and resumes
your music. It also shows what's playing, with album art and playback controls, and keeps
a history of blocked ads.

## Download

1. Go to [**Releases**](../../releases/latest) and download **`AdGuard.exe`**.
2. Double-click it. Nothing to install.
3. If Windows shows *"Windows protected your PC"*, click **More info → Run anyway**
   (the app isn't code-signed).

Requires Windows 10 or 11 and the Spotify desktop app.

## Run from source

```
py -m pip install psutil pycaw comtypes customtkinter pillow
py -m pip install winrt-runtime winrt-Windows.Media.Control winrt-Windows.Storage.Streams winrt-Windows.Foundation winrt-Windows.Foundation.Collections
py spotify_ad_guard.py
```

The second line is optional (album art and better pause detection).

## Build the EXE

```
py -m pip install pyinstaller
py -m PyInstaller --noconfirm --onefile --windowed --icon adguard.ico --collect-all customtkinter --collect-submodules winrt --name AdGuard spotify_ad_guard.py
```
