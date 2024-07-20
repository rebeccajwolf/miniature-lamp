#!/bin/sh
echo "Starting Clean Mem..."
pkill -9 python
pkill -9 xvfb
pkill -9 chrome
pkill -9 chromium
echo "Finished Cleaning Mem..."
