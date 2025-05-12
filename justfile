#!/usr/bin/env just --justfile

verify:
    #!/usr/bin/env bash
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk install java 21.0.7-zulu
    sdk use java 21.0.7-zulu
    ./stainless-dotty-standalone-*/stainless --fail-early=true $(find ./src/main/scala -name '*.scala' | tr '\n' ' ')

verify-docker:
    docker-compose -f docker-compose.yaml run stainless

build:
    sbt clean reload assembly jacoco

run a b:
    java -jar target/scala-3.5.0/prime-numbers-assembly-0.0.0.jar  {{a}} {{b}}

check a b div mod:
    java -jar target/scala-3.5.0/prime-numbers-assembly-0.0.0.jar  {{a}} {{b}} {{div}} {{mod}}