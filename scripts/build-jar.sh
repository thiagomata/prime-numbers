#!/usr/bin/env bash

source "$HOME/.sdkman/bin/sdkman-init.sh"
sdk use java 21.0.7-zulu
export DYLD_LIBRARY_PATH="/opt/homebrew/Cellar/z3/4.16.0/lib:${DYLD_LIBRARY_PATH:-}"
sbt 'set stainlessEnabled := false' clean assembly
