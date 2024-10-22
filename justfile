#!/usr/bin/env just --justfile

verify:
    jenv local 21
    stainless $(find ./src/main/scala -name '*.scala' | tr '\n' ' ')

verify-docker:
    docker-compose -f docker-compose.yaml run stainless