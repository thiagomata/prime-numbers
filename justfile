#!/usr/bin/env just --justfile

verify:
    jenv local 21
    stainless $(find ./src/main/scala -name '*.scala' | tr '\n' ' ')

verify-docker:
    docker-compose -f docker-compose.yaml run stainless

build:
    sbt clean reload assembly jacoco

run a b:
    java -jar target/scala-3.5.0/prime-numbers-assembly-0.0.0.jar  {{a}} {{b}}

check a b div mod:
    java -jar target/scala-3.5.0/prime-numbers-assembly-0.0.0.jar  {{a}} {{b}} {{div}} {{mod}}