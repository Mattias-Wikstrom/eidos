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

# Run tests for each theory
for theory in theories/*.theory; do
    if [ -f "$theory" ]; then
        total=$((total + 1))
        filename=$(basename "$theory")
        
        echo -n "Testing $filename... "
        
        # Run the parser in pure mode (no external references)
        if cabal run eidos-parser -- --pure "$theory" > /dev/null 2>&1; then
            echo -e "${GREEN}PASSED${NC}"
            passed=$((passed + 1))
        else
            echo -e "${RED}FAILED${NC}"
            failed=$((failed + 1))
            # Show the error for debugging
            echo "  Error details:"
            cabal run eidos-parser -- --pure "$theory" 2>&1 | head -5 | sed 's/^/    /'
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
