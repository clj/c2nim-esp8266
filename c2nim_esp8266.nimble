# Package

version     = "0.9.14.1"
author      = "Christian Lyder Jacobsen"
description = "A version of c2nim for the esp8266 APIs"
license     = "MIT"

bin = @["c2nim_esp8266"]
skipExt = @["nim"]
srcDir = "src"
skipDirs = @["c2nim"]

task bootstrap, "Bootstrap":
    exec "sh bootstrap.sh"

before install:
    bootstrapTask()

# Deps

requires "nim >= 0.19.0"
