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
    python3 "{{justfile_directory()}}/python/tools/check_scala_cycles.py" "{{scope}}"

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

python-setup:
    #!/usr/bin/env bash
    set -euo pipefail
    cd "{{justfile_directory()}}/python"
    python3 -m venv .venv
    .venv/bin/pip install -e ".[dev]"

empirical-test:
    #!/usr/bin/env bash
    set -euo pipefail
    cd "{{justfile_directory()}}"
    exec python/.venv/bin/pytest python/tests/ -v

empirical-window max_prime="1000" output="data/candidates/window-measurements.csv":
    #!/usr/bin/env bash
    set -euo pipefail
    cd "{{justfile_directory()}}"
    exec python/.venv/bin/sieve-sequence-window "{{max_prime}}" "{{output}}"

empirical-window-sparse stride="100" max_prime="20000" output="data/candidates/window-measurements-sparse.csv":
    #!/usr/bin/env bash
    set -euo pipefail
    cd "{{justfile_directory()}}"
    exec python/.venv/bin/sieve-sequence-window --sparse "{{stride}}" "{{max_prime}}" "{{output}}"

empirical-lineage q="17" output="":
    #!/usr/bin/env bash
    set -euo pipefail
    cd "{{justfile_directory()}}"
    q={{quote(q)}}
    output={{quote(output)}}
    if [[ -z "$output" ]]; then
      output="data/candidates/lineage-Q${q}.csv"
    fi
    [[ "$q" =~ ^[0-9]+$ && -n "$output" ]]
    exec python/.venv/bin/sieve-sequence-lineage "$q" "$output"

empirical-hazard q="17" output="":
    #!/usr/bin/env bash
    set -euo pipefail
    cd "{{justfile_directory()}}"
    q={{quote(q)}}
    output={{quote(output)}}
    if [[ -z "$output" ]]; then
      output="data/candidates/fixed-lineage-hazard-Q${q}.csv"
    fi
    [[ "$q" =~ ^[0-9]+$ && -n "$output" ]]
    exec python/.venv/bin/sieve-sequence-hazard "$q" "$output"

empirical-deferred3 max_prime="2000" output="data/candidates/deferred3-measurements.csv":
    #!/usr/bin/env bash
    set -euo pipefail
    cd "{{justfile_directory()}}"
    exec python/.venv/bin/sieve-sequence-deferred3 "{{max_prime}}" "{{output}}"

empirical-chart-hazard:
    cd "{{justfile_directory()}}/python" && exec .venv/bin/python -m sieve_sequence.fixed_lineage_hazard_chart

empirical-chart-full-cycle:
    cd "{{justfile_directory()}}/python" && exec .venv/bin/python -m sieve_sequence.full_cycle_destruction_chart
    cd "{{justfile_directory()}}/python" && exec .venv/bin/python -m sieve_sequence.full_cycle_survival_chart

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


verify-bg focus="":
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log verify-bg "{{justfile_directory()}}" "focus={{focus}}"
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
    ./stainless-dotty-standalone-*/stainless --timeout=300 "${function_filter[@]}" $(./scripts/find-src.sh) >> logs/verify.log 2>&1 &
    echo "Started in background. PID=$! — watch: tail -f logs/verify.log"

verify-debug-bg focus="":
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log verify-debug-bg "{{justfile_directory()}}" "focus={{focus}}"
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
    ./stainless-dotty-standalone-*/stainless --batched --timeout=300 --debug=verification,full-vc,solver "${function_filter[@]}" $(./scripts/find-src.sh) >> logs/verify-debug.log 2>&1 &
    echo "Started in background. PID=$! — watch: tail -f logs/verify-debug.log"

spark-run numStages="10":
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log spark-run "{{justfile_directory()}}" "numStages={{numStages}}"
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk use java 21.0.7-zulu
    sbt "spark/runMain v1.chapter8.SieveGenerator {{numStages}}"

spark-generate numStages="10":
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log spark-generate "{{justfile_directory()}}" "numStages={{numStages}}"
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk use java 21.0.7-zulu
    rm -rf spark/data/sieve-df/
    sbt "spark/runMain v1.chapter8.SieveGenerator {{numStages}}"

spark-test:
    #!/usr/bin/env bash
    source "{{justfile_directory()}}/scripts/just-log.sh"
    just_log spark-test "{{justfile_directory()}}"
    source "$HOME/.sdkman/bin/sdkman-init.sh"
    sdk use java 21.0.7-zulu
    sbt "spark/test"

spark-cat stage="1" file="gaps":
    #!/usr/bin/env bash
    base="{{justfile_directory()}}/spark/data/sieve-df"
    dir="$base/stage_$(printf '%03d' {{stage}})/{{file}}"
    if [[ -f "$dir.csv.gz" ]]; then
      # Single gzip file (e.g. values.csv.gz, gaps-2.csv.gz)
      gunzip -c "$dir.csv.gz" | column -t -s,
      exit 0
    fi
    if [[ ! -d "$dir" ]]; then
      echo "Not found: $dir or $dir.csv.gz" >&2
      exit 1
    fi
    # Partitioned CSV directory (e.g. gaps/)
    parts=("$dir"/part-*.csv.gz)
    if [[ ${#parts[@]} -eq 0 ]]; then
      echo "No part files in $dir" >&2
      exit 1
    fi
    gunzip -c "${parts[0]}" | head -1 | column -t -s,
    for f in "${parts[@]}"; do
      gunzip -c "$f" | tail -n +2
    done | column -t -s,
    gunzip -c "${parts[0]}" | head -1 | column -t -s,
    for f in "${parts[@]}"; do
      gunzip -c "$f" | tail -n +2
    done | column -t -s,

# Build arXiv article PDF(s): `just arxiv-pdf` builds every article under
# articles/arxiv/, `just arxiv-pdf modulo` builds one. The PDF is written to
# articles/arxiv/<article>/output/pdf/<article>.pdf; auxiliary LaTeX files
# stay in a per-article scratch dir under $TMPDIR (outside the repository).
arxiv-pdf article="":
    #!/usr/bin/env bash
    set -euo pipefail
    base="{{justfile_directory()}}/articles/arxiv"
    if [[ -n "{{article}}" ]]; then
      dirs=("$base/{{article}}")
    else
      dirs=("$base"/*/)
    fi
    for dir in "${dirs[@]}"; do
      if [[ ! -f "$dir/main.tex" ]]; then
        continue
      fi
      name=$(basename "$dir")
      build="${TMPDIR:-/tmp}/arxiv-build-$name"
      mkdir -p "$build"
      # -g forces a rebuild: latexmk does not track files that main.tex only
      # probes with \IfFileExists, so a newly added section file would
      # otherwise be silently missed in the persistent build directory.
      (cd "$dir" && latexmk -g -pdf -interaction=nonstopmode -halt-on-error -outdir="$build" main.tex)
      mkdir -p "$dir/output/pdf"
      cp "$build/main.pdf" "$dir/output/pdf/$name.pdf"
      echo "Built $dir/output/pdf/$name.pdf"
    done
