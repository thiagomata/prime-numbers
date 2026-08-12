#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/markdown-cleanup-review.sh [--commands|--commands-with-done|--rm-commands|--rm-commands-with-done]

Review markdown cleanup candidates without deleting files.

Options:
  --commands   Print git rm commands for the strongest delete candidates.
               The commands are printed to stdout only; they are not executed.
  --commands-with-done
               Print git rm commands for strongest candidates plus done tickets
               except the small referenced anchor set. Printed only.
  --rm-commands
               Print plain rm commands for the strongest delete candidates,
               one file per line. Printed only.
  --rm-commands-with-done
               Print plain rm commands for strongest candidates plus done
               tickets except the small referenced anchor set. Printed only.
EOF
}

print_counts() {
  printf 'Markdown inventory\n'
  printf '==================\n'
  printf 'All markdown files: '
  git ls-files '*.md' | wc -l | tr -d ' '
  printf '\n'

  printf 'tickets/trash markdown files: '
  git ls-files 'tickets/trash/*.md' | wc -l | tr -d ' '
  printf '\n'

  printf 'deprecated article files: '
  git ls-files 'articles/deprecated/*.md' | wc -l | tr -d ' '
  printf '\n\n'

  printf 'tickets/done markdown files: '
  git ls-files 'tickets/done/*.md' | wc -l | tr -d ' '
  printf '\n\n'
}

strong_candidates() {
  git ls-files 'tickets/trash/*.md' 'articles/deprecated/*.md'
}

done_archive_candidates() {
  git ls-files 'tickets/done/*.md' |
    grep -Ev 'tickets/done/(canonical-spec-to-cycle-alignment|spec-same-head-filter-density|scientific-review-articles-2026-07-17|gap-dynamics-v2-research-update|integral-cycle-examiner-review|ticket-lifecycle-restructure-2026-06-21|verify-timeout-root-cause)\.md$'
}

print_candidates() {
  printf 'Strongest delete candidates after owner review\n'
  printf '==============================================\n'
  strong_candidates
  printf '\n\n'
  printf 'Done ticket deep-archive candidates after lesson extraction\n'
  printf '==========================================================\n'
  done_archive_candidates
  printf '\n'
}

print_commands() {
  printf '# Review these commands before running them manually.\n'
  strong_candidates |
    awk '{ printf "git rm -- \047%s\047\n", $0 }'
}

print_commands_with_done() {
  printf '# Review these commands before running them manually.\n'
  {
    strong_candidates
    done_archive_candidates
  } |
    awk '{ printf "git rm -- \047%s\047\n", $0 }'
}

print_rm_commands() {
  printf '# Review these commands before running them manually.\n'
  strong_candidates |
    awk '{ printf "rm -- \047%s\047\n", $0 }'
}

print_rm_commands_with_done() {
  printf '# Review these commands before running them manually.\n'
  {
    strong_candidates
    done_archive_candidates
  } |
    awk '{ printf "rm -- \047%s\047\n", $0 }'
}

case "${1:-}" in
  "")
    print_counts
    print_candidates
    ;;
  "--commands")
    print_commands
    ;;
  "--commands-with-done")
    print_commands_with_done
    ;;
  "--rm-commands")
    print_rm_commands
    ;;
  "--rm-commands-with-done")
    print_rm_commands_with_done
    ;;
  "-h"|"--help")
    usage
    ;;
  *)
    usage
    exit 2
    ;;
esac
