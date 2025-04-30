#!/usr/bin/env just --justfile

verify:
    #!/usr/bin/env bash
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk install java 21.0.7-zulu
    sdk use java 21.0.7-zulu
    ./stainless-dotty-standalone-*/stainless $(find ./src/main/scala -name '*.scala' | tr '\n' ' ')

verify-docker:
    docker-compose -f docker-compose.yaml run stainless