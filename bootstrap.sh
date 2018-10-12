#!/bin/sh
#git submodule init
#git submodule update
cp src/c2nim/c2nim.nim src/c2nim_esp8266.nim
patch -N -f -d src < c2nim_esp8266.nim.patch
