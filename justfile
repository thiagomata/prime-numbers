#!/usr/bin/env just --justfile

verify:
    #!/usr/bin/env bash
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk install java 21.0.7-zulu
    sdk use java 21.0.7-zulu
    pkill -f sbt 2>/dev/null; pkill -f java;
    rm -f verify-error.log
    rm -f verify.log
    Z3_LIB="/opt/homebrew/Cellar/z3/4.16.0/lib"
    DYLD_LIBRARY_PATH="$Z3_LIB:${DYLD_LIBRARY_PATH:-}" \
    JAVA_OPTS="-Djava.library.path=$Z3_LIB" \
    ./stainless-dotty-standalone-*/stainless --timeout=120 $(find ./src/main/scala -name '*.scala' | sort | tr '\n' ' ') 2> >(tee verify-error.log | tee -a verify.log >&2) 1> >(tee -a verify.log)

verify-no-cache:
    #!/usr/bin/env bash
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk install java 21.0.7-zulu
    sdk use java 21.0.7-zulu
    pkill -f sbt 2>/dev/null; pkill -f java;
    rm -f verify-error.log
    rm -f verify.log
    Z3_LIB="/opt/homebrew/Cellar/z3/4.16.0/lib"
    DYLD_LIBRARY_PATH="$Z3_LIB:${DYLD_LIBRARY_PATH:-}" \
    JAVA_OPTS="-Djava.library.path=$Z3_LIB" \
    ./stainless-dotty-standalone-*/stainless --timeout=120 --vc-cache=false $(find ./src/main/scala -name '*.scala' | sort | tr '\n' ' ') 2> >(tee verify-error.log | tee -a verify.log >&2) 1> >(tee -a verify.log)

verify-docker:
    docker-compose -f docker-compose.yaml run stainless

build:
    #!/usr/bin/env bash
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk use java 21.0.7-zulu
    export DYLD_LIBRARY_PATH="/opt/homebrew/Cellar/z3/4.16.0/lib:${DYLD_LIBRARY_PATH:-}"
    sbt clean reload assembly jacoco

test:
    #!/usr/bin/env bash
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk use java 21.0.7-zulu
    export DYLD_LIBRARY_PATH="/opt/homebrew/Cellar/z3/4.16.0/lib:${DYLD_LIBRARY_PATH:-}"
    sbt 'set stainlessEnabled := false' 'testOnly * -- -l v1.tags.SlowLemmaTest' 2>&1 | tee test.log

test-all:
    #!/usr/bin/env bash
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk use java 21.0.7-zulu
    export DYLD_LIBRARY_PATH="/opt/homebrew/Cellar/z3/4.16.0/lib:${DYLD_LIBRARY_PATH:-}"
    sbt 'set stainlessEnabled := false' test 2>&1 | tee test-all.log

test-slow:
    #!/usr/bin/env bash
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk use java 21.0.7-zulu
    export DYLD_LIBRARY_PATH="/opt/homebrew/Cellar/z3/4.16.0/lib:${DYLD_LIBRARY_PATH:-}"
    sbt 'set stainlessEnabled := false' 'testOnly v1.seq.sieve.SpecSieveSequenceTest -- -n v1.tags.SlowLemmaTest' 2>&1 | tee test-slow.log

run a b:
    java -jar target/scala-3.5.0/prime-numbers-assembly-0.0.0.jar  {{a}} {{b}}

check a b div mod:
    java -jar target/scala-3.5.0/prime-numbers-assembly-0.0.0.jar  {{a}} {{b}} {{div}} {{mod}}
