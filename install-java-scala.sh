#!/usr/bin/env bash
if [ ! -f ~/.sdkman/bin/sdkman-init.sh ]; then
  curl -s "https://get.sdkman.io" | bash
  source "$HOME/.sdkman/bin/sdkman-init.sh"
fi
source "$HOME/.sdkman/bin/sdkman-init.sh"
sdk install java 21.0.7-zulu
sdk install scala 3.5.0
sdk install sbt
