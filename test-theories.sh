#!/bin/bash
# test-theories.sh - Test all theories in the theories/ directory

set -e  # Exit on error

GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "=========================================="
echo "Testing all theories in theories/ directory"
echo "=========================================="
echo

# Counters
total=0
passed=0
failed=0

# External references (e.g. @monoid, @ring) require IO mode so the resolver can
# read sibling files from theories/.  Pure mode is still available for focused
# parser/type-check tests by setting EIDOS_TEST_MODE=pure.
MODE="${EIDOS_TEST_MODE:-io}"
if [ "$MODE" = "pure" ]; then
    RUN_ARGS=(--pure)
    MODE_LABEL="pure mode (external refs disabled)"
else
    RUN_ARGS=()
    MODE_LABEL="IO mode (external refs enabled)"
fi

echo "Using $MODE_LABEL"
echo

# Run tests for each theory
for theory in theories/*.theory; do
    if [ -f "$theory" ]; then
        total=$((total + 1))
        filename=$(basename "$theory")
        
        echo -n "Testing $filename... "
        
        if cabal run eidos-parser -- "${RUN_ARGS[@]}" "$theory" > /dev/null 2>&1; then
            echo -e "${GREEN}PASSED${NC}"
            passed=$((passed + 1))
        else
            echo -e "${RED}FAILED${NC}"
            failed=$((failed + 1))
            # Show the error for debugging
            echo "  Error details:"
            cabal run eidos-parser -- "${RUN_ARGS[@]}" "$theory" 2>&1 | head -5 | sed 's/^/    /'
        fi
    fi
done

echo
echo "=========================================="
echo "Results: $passed passed, $failed failed, $total total"
echo "=========================================="

if [ $failed -gt 0 ]; then
    exit 1
fi
