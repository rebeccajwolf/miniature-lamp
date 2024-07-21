#!/bin/sh
echo "Starting Clean Mem..."
pkill -9 python3
pkill -9 Xvfb
pkill -9 chrome
pkill -9 chromium
pkill -9 chromedriver
echo "Finished Cleaning Mem..."
