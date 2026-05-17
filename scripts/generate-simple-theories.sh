#!/bin/bash
# generate-simple-theories.sh
#
# Compile every example in simple_theories/ with each supported output target
# and write the results into a .generated/ subfolder inside each example's
# directory.
#
# Usage:
#   scripts/generate-simple-theories.sh [--targets lean,coq] [--dir simple_theories/foo]
#
# Options:
#   --targets <list>   Comma-separated subset of targets to run (default: all).
#                      Valid target names: lean_using_props, coq_using_props
#   --dir <path>       Process only this single example directory instead of all.
#   --no-annotations   Omit --comment-groups --comment-tags from output.
#   --dry-run          Print commands without executing them.
#
# Adding a new target later:
#   Append an entry to the TARGETS array below.  Each entry is a colon-separated
#   record:  name:flag:extra_flags:extension
#   • name         — used as the output filename stem and for --targets filtering
#   • flag         — the primary CLI flag passed to eidos-parser (e.g. --lean_using_props)
#   • extra_flags  — space-separated additional flags (use "" for none)
#   • extension    — file extension for the output file (without the dot)

set -euo pipefail

# ---------------------------------------------------------------------------
# Target definitions
# ---------------------------------------------------------------------------
# Format: "name:flag:extra_flags:extension"
TARGETS=(
  "dump_ir:--dump-ir::irdump"
  "lean_using_props:--lean_using_props::lean"
  "coq_using_props:--coq_using_props::v"
  "mereological:--mereological::mereo.theory"
)

# ---------------------------------------------------------------------------
# Defaults
# ---------------------------------------------------------------------------
SIMPLE_THEORIES_DIR="simple_theories"
ANNOTATION_FLAGS=""
FILTER_TARGETS=""
SINGLE_DIR=""
DRY_RUN=false

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------
while [[ $# -gt 0 ]]; do
  case "$1" in
    --targets)
      FILTER_TARGETS="$2"; shift 2 ;;
    --dir)
      SINGLE_DIR="$2"; shift 2 ;;
    --no-annotations)
      ANNOTATION_FLAGS=""; shift ;;
    --dry-run)
      DRY_RUN=true; shift ;;
    *)
      echo "Unknown option: $1" >&2
      echo "Usage: $0 [--targets lean_using_props,coq_using_props] [--dir path] [--no-annotations] [--dry-run]" >&2
      exit 1 ;;
  esac
done

# ---------------------------------------------------------------------------
# Colour helpers
# ---------------------------------------------------------------------------
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m'

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

run_cmd() {
  if $DRY_RUN; then
    echo "  [dry-run] $*"
  else
    "$@"
  fi
}

# Return 0 if the target name is in the filter list (or no filter is set).
target_enabled() {
  local name="$1"
  [[ -z "$FILTER_TARGETS" ]] && return 0
  [[ ",$FILTER_TARGETS," == *",$name,"* ]]
}

# ---------------------------------------------------------------------------
# Main loop
# ---------------------------------------------------------------------------
total=0; ok=0; failed=0; skipped=0

process_example() {
  local example_dir="$1"
  local dirname
  dirname="$(basename "$example_dir")"

  # The "main" theory file is the one whose stem matches the directory name.
  # (Other files such as base.theory are helper files referenced by @.)
  local theory_file="$example_dir/$dirname.theory"
  if [[ ! -f "$theory_file" ]]; then
    echo -e "${YELLOW}SKIP${NC}  $dirname  (no $dirname.theory found)"
    skipped=$((skipped + 1))
    return
  fi

  local generated_dir="$example_dir/.generated"
  run_cmd mkdir -p "$generated_dir"

  echo -e "${CYAN}=== $dirname ===${NC}"

  for target_spec in "${TARGETS[@]}"; do
    IFS=':' read -r tname tflag textra text <<< "$target_spec"

    target_enabled "$tname" || continue

    local out_file="$generated_dir/$tname.$text"

    # Build the full argument list.
    # Order: primary flag, extra flags, annotation flags, theory file path.
    local cmd_args=("$tflag")
    # shellcheck disable=SC2206
    [[ -n "$textra" ]]          && cmd_args+=($textra)
    # shellcheck disable=SC2206
    [[ -n "$ANNOTATION_FLAGS" ]] && cmd_args+=($ANNOTATION_FLAGS)
    cmd_args+=("$theory_file")

    total=$((total + 1))
    printf "  %-30s " "$tname"

    if $DRY_RUN; then
      echo "[dry-run] cabal run eidos-parser -- ${cmd_args[*]} > $out_file"
      ok=$((ok + 1))
      continue
    fi

    local tmp
    tmp="$(mktemp)"
    local err_tmp
    err_tmp="$(mktemp)"

    if cabal run eidos-parser -- "${cmd_args[@]}" > "$tmp" 2>"$err_tmp"; then
      mv "$tmp" "$out_file"
      rm -f "$err_tmp"
      echo -e "${GREEN}OK${NC}  → .generated/$tname.$text"
      ok=$((ok + 1))
    else
      rm -f "$tmp"
      echo -e "${RED}FAILED${NC}"
      # Show first few lines of stderr to aid diagnosis
      head -5 "$err_tmp" | sed 's/^/      /'
      rm -f "$err_tmp"
      failed=$((failed + 1))
    fi
  done
}

if [[ -n "$SINGLE_DIR" ]]; then
  process_example "$SINGLE_DIR"
else
  for d in "$SIMPLE_THEORIES_DIR"/*/; do
    [[ -d "$d" ]] && process_example "${d%/}"
  done
fi

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo
echo "=========================================="
echo -e "Results: ${GREEN}$ok OK${NC}, ${RED}$failed failed${NC}, ${YELLOW}$skipped skipped${NC} ($total total)"
echo "=========================================="

[[ $failed -gt 0 ]] && exit 1 || exit 0
