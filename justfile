#!/usr/bin/env just --justfile

compile:
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log compile "{{justfile_directory()}}"
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk install java 21.0.7-zulu
    sdk use java 21.0.7-zulu
    sbt 'set stainlessEnabled := false' compile

verify focus="":
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log verify "{{justfile_directory()}}" "focus={{focus}}"
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk install java 21.0.7-zulu
    sdk use java 21.0.7-zulu
    bash "{{justfile_directory()}}/scripts/verify-stop.sh"
    cd "{{justfile_directory()}}"
    mkdir -p logs
    rm -f logs/verify-error.log
    rm -f logs/verify.log
    Z3_LIB="/opt/homebrew/Cellar/z3/4.16.0/lib"
    function_filter=()
    if [[ -n "{{focus}}" ]]; then
      function_filter=(--functions="{{focus}}")
    fi
    DYLD_LIBRARY_PATH="$Z3_LIB:${DYLD_LIBRARY_PATH:-}" \
    JAVA_OPTS="-Xmx16g -Djava.library.path=$Z3_LIB" \
    ./stainless-dotty-standalone-*/stainless --timeout=300 "${function_filter[@]}" $(./scripts/find-src.sh) 2> >(tee logs/verify-error.log | tee -a logs/verify.log >&2) 1> >(tee -a logs/verify.log)

verify-ch chapters="":
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log verify-ch "{{justfile_directory()}}" "chapters={{chapters}}"
    exec "{{justfile_directory()}}/scripts/verify-ch.sh" {{chapters}}

verify-stop:
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log verify-stop "{{justfile_directory()}}"
    bash "{{justfile_directory()}}/scripts/verify-stop.sh"

verify-watch focus="":
    #!/usr/bin/env bash
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk install java 21.0.7-zulu
    sdk use java 21.0.7-zulu
    exec "{{justfile_directory()}}/scripts/verify-watch.sh" {{focus}}

clean-logs:
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log clean-logs "{{justfile_directory()}}"
    rm -f "{{justfile_directory()}}"/logs/*.log
    echo "Cleared all logs in logs/"

verify-class class="":
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log verify-class "{{justfile_directory()}}" "class={{class}}"
    cd "{{justfile_directory()}}" && exec just verify "{{class}}._"

check-cycles scope="":
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log check-cycles "{{justfile_directory()}}" "scope={{scope}}"
    python3 "{{justfile_directory()}}/scripts/check-scala-cycles.py" "{{scope}}"

verify-file file pattern="":
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log verify-file "{{justfile_directory()}}" "file={{file}} pattern={{pattern}}"
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk install java 21.0.7-zulu
    sdk use java 21.0.7-zulu
    bash "{{justfile_directory()}}/scripts/verify-stop.sh"
    cd "{{justfile_directory()}}"
    mkdir -p logs
    rm -f logs/verify-error.log
    rm -f logs/verify-file.log
    Z3_LIB="/opt/homebrew/Cellar/z3/4.16.0/lib"
    funcs=()
    while IFS= read -r line; do
      name=$(echo "$line" | sed -n 's/.*def \([a-zA-Z0-9_]\+\).*/\1/p')
      if [[ -n "$name" ]]; then
        funcs+=(--functions="$name")
      fi
    done < <(grep -v "^//\|^$\|^import\|^package\|^object\|^class\|^case\|^require\|^val\|^var\|^def this" "$file")
    DYLD_LIBRARY_PATH="$Z3_LIB:${DYLD_LIBRARY_PATH:-}" \
    JAVA_OPTS="-Xmx16g -Djava.library.path=$Z3_LIB" \
    ./stainless-dotty-standalone-*/stainless --timeout=300 "${funcs[@]}" $(./scripts/find-src.sh) 2> >(tee logs/verify-error.log | tee -a logs/verify-file.log >&2) 1> >(tee -a logs/verify-file.log)

verify-debug focus="":
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log verify-debug "{{justfile_directory()}}" "focus={{focus}}"
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk install java 21.0.7-zulu
    sdk use java 21.0.7-zulu
    bash "{{justfile_directory()}}/scripts/verify-stop.sh"
    cd "{{justfile_directory()}}"
    mkdir -p logs
    rm -f logs/verify-error.log
    rm -f logs/verify-debug.log
    Z3_LIB="/opt/homebrew/Cellar/z3/4.16.0/lib"
    function_filter=()
    if [[ -n "{{focus}}" ]]; then
      function_filter=(--functions="{{focus}}" --debug-objects="{{focus}}")
    fi
    DYLD_LIBRARY_PATH="$Z3_LIB:${DYLD_LIBRARY_PATH:-}" \
    JAVA_OPTS="-Xmx16g -Djava.library.path=$Z3_LIB" \
    ./stainless-dotty-standalone-*/stainless --batched --timeout=300 --debug=verification,full-vc,solver "${function_filter[@]}" $(./scripts/find-src.sh) 2> >(tee logs/verify-error.log | tee -a logs/verify-debug.log >&2) 1> >(tee -a logs/verify-debug.log)

verify-no-cache focus="":
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log verify-no-cache "{{justfile_directory()}}" "focus={{focus}}"
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk install java 21.0.7-zulu
    sdk use java 21.0.7-zulu
    bash "{{justfile_directory()}}/scripts/verify-stop.sh"
    cd "{{justfile_directory()}}"
    mkdir -p logs
    rm -f logs/verify-error.log
    rm -f logs/verify-no-cache.log
    Z3_LIB="/opt/homebrew/Cellar/z3/4.16.0/lib"
    function_filter=()
    if [[ -n "{{focus}}" ]]; then
      function_filter=(--functions="{{focus}}")
    fi
    DYLD_LIBRARY_PATH="$Z3_LIB:${DYLD_LIBRARY_PATH:-}" \
    JAVA_OPTS="-Xmx16g -Djava.library.path=$Z3_LIB" \
    ./stainless-dotty-standalone-*/stainless --batched --timeout=300 --vc-cache=false "${function_filter[@]}" $(./scripts/find-src.sh) 2> >(tee logs/verify-error.log | tee -a logs/verify-no-cache.log >&2) 1> >(tee -a logs/verify-no-cache.log)

build:
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log build "{{justfile_directory()}}"
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk use java 21.0.7-zulu
    export DYLD_LIBRARY_PATH="/opt/homebrew/Cellar/z3/4.16.0/lib:${DYLD_LIBRARY_PATH:-}"
    sbt clean reload assembly jacoco

jar:
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log jar "{{justfile_directory()}}"
    bash "{{justfile_directory()}}/scripts/build-jar.sh"

bin:
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log bin "{{justfile_directory()}}"
    bash "{{justfile_directory()}}/scripts/build-jar.sh"

test:
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log test "{{justfile_directory()}}"
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk use java 21.0.7-zulu
    export DYLD_LIBRARY_PATH="/opt/homebrew/Cellar/z3/4.16.0/lib:${DYLD_LIBRARY_PATH:-}"
    sbt 'set stainlessEnabled := false' 'testOnly * -- -l v1.tags.SlowLemmaTest' 2>&1 | tee test.log

test-all:
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log test-all "{{justfile_directory()}}"
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk use java 21.0.7-zulu
    export DYLD_LIBRARY_PATH="/opt/homebrew/Cellar/z3/4.16.0/lib:${DYLD_LIBRARY_PATH:-}"
    sbt 'set stainlessEnabled := false' test 2>&1 | tee test-all.log

test-slow:
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log test-slow "{{justfile_directory()}}"
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk use java 21.0.7-zulu
    export DYLD_LIBRARY_PATH="/opt/homebrew/Cellar/z3/4.16.0/lib:${DYLD_LIBRARY_PATH:-}"
    sbt 'set stainlessEnabled := false' 'testOnly * -- -n v1.tags.SlowLemmaTest' 2>&1 | tee test-slow.log

run a b: jar
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log run "{{justfile_directory()}}" "a={{a}} b={{b}}"
    java -jar target/scala-3.5.0/prime-numbers-assembly-0.0.0.jar  {{a}} {{b}}

check a b div mod: jar
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log check "{{justfile_directory()}}" "a={{a}} b={{b}} div={{div}} mod={{mod}}"
    java -jar target/scala-3.5.0/prime-numbers-assembly-0.0.0.jar  {{a}} {{b}} {{div}} {{mod}}

show steps count: jar
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log show "{{justfile_directory()}}" "steps={{steps}} count={{count}}"
    java -jar target/scala-3.5.0/prime-numbers-assembly-0.0.0.jar  show {{steps}} {{count}}
