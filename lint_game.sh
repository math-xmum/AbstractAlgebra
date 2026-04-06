#!/bin/bash
# Lint script: verify game design consistency
# Checks that the game implementation matches the design spec

set -e
ERRORS=0
WARNINGS=0

echo "=== Abstract Algebra Game Lint ==="
echo ""

# 1. Check world dependency declarations are in Game.lean
echo "[1] Checking Dependency declarations..."
STRAY_DEPS=$(grep -rn '^Dependency ' Game/Levels/ --include="*.lean" 2>/dev/null | grep -v "^Binary" || true)
if [ -n "$STRAY_DEPS" ]; then
    echo "  ERROR: Dependency declarations found outside Game.lean (should all be in Game.lean):"
    echo "$STRAY_DEPS" | sed 's/^/    /'
    ERRORS=$((ERRORS + 1))
else
    echo "  OK: All Dependency declarations are in Game.lean"
fi

# 2. Check for duplicate NewTactic declarations across worlds
echo ""
echo "[2] Checking for duplicate NewTactic across worlds..."
# Extract all NewTactic entries per world
DUPES=$(grep -rn "^NewTactic" Game/Levels/ --include="*.lean" 2>/dev/null | grep -v RBGame | \
    sed 's/.*NewTactic //' | tr ' ' '\n' | sed '/^$/d' | sort | uniq -d || true)
if [ -n "$DUPES" ]; then
    echo "  WARNING: These tactics are introduced (NewTactic) in multiple levels:"
    for tac in $DUPES; do
        echo "    $tac:"
        grep -rn "NewTactic.*\b${tac}\b" Game/Levels/ --include="*.lean" 2>/dev/null | grep -v RBGame | sed 's/^/      /'
    done
    WARNINGS=$((WARNINGS + 1))
fi

# 3. Check that BasicLean introduces fundamental tactics
echo ""
echo "[3] Checking BasicLean introduces fundamental tactics..."
BASIC_TACTICS="rfl simp rw exact intro apply constructor ext"
for tac in $BASIC_TACTICS; do
    if ! grep -q "NewTactic.*\b${tac}\b" Game/Levels/BasicLean/*.lean 2>/dev/null; then
        echo "  ERROR: Fundamental tactic '$tac' not introduced in BasicLean"
        ERRORS=$((ERRORS + 1))
    fi
done
echo "  Checked: $BASIC_TACTICS"

# 4. Check no simp in level proofs (only in NewTactic declarations and Hints)
echo ""
echo "[4] Checking for simp usage in level proofs..."
SIMP_IN_PROOFS=$(grep -rn "^\s*simp\b" Game/Levels/ --include="*.lean" 2>/dev/null | \
    grep -v RBGame | grep -v "NewTactic" | grep -v "Hint" | grep -v "OnlyTactic" | \
    grep -v "^.*:.*--" | grep -v "simp_rw\|simp_all\|simp only" || true)
if [ -n "$SIMP_IN_PROOFS" ]; then
    echo "  WARNING: Bare 'simp' found in proofs (prefer explicit theorems):"
    echo "$SIMP_IN_PROOFS" | head -10 | sed 's/^/    /'
    WARNINGS=$((WARNINGS + 1))
fi

# 5. Check world names match expected list
echo ""
echo "[5] Checking world declarations..."
EXPECTED_WORLDS="BasicLean BasicFunctions EquivalenceRelation Magma BasicGroupTheory GroupHomomorphism GroupAction"
ACTUAL_WORLDS=$(grep -rn '^World "' Game/Levels/ --include="*.lean" 2>/dev/null | grep -v RBGame | \
    grep -v '/L[0-9]' | sed 's/.*World "\(.*\)"/\1/' | sort)
for w in $EXPECTED_WORLDS; do
    if ! echo "$ACTUAL_WORLDS" | grep -q "^${w}$"; then
        echo "  ERROR: Expected world '$w' not found"
        ERRORS=$((ERRORS + 1))
    fi
done
UNEXPECTED=$(echo "$ACTUAL_WORLDS" | while read w; do
    echo "$EXPECTED_WORLDS" | tr ' ' '\n' | grep -q "^${w}$" || echo "$w"
done)
if [ -n "$UNEXPECTED" ]; then
    echo "  WARNING: Unexpected worlds found: $UNEXPECTED"
    WARNINGS=$((WARNINGS + 1))
fi
echo "  Found worlds: $ACTUAL_WORLDS"

# 6. Check each level has exactly one Introduction block
echo ""
echo "[6] Checking for duplicate Introduction blocks..."
for f in $(find Game/Levels -name "L*.lean" -not -path "*/RBGame/*"); do
    COUNT=$(grep -c '^Introduction' "$f" 2>/dev/null || true)
    COUNT=${COUNT:-0}
    if [ "$COUNT" -gt 1 ]; then
        echo "  WARNING: $f has $COUNT Introduction blocks (should be 1)"
        WARNINGS=$((WARNINGS + 1))
    fi
done

# 7. Check Magma hints mention binary operation
echo ""
echo "[7] Checking Magma hints mention binary operation..."
for f in Game/Levels/Magma/L*.lean; do
    if grep -q "isMagma\|isAddMagma\|magma" "$f" 2>/dev/null; then
        if ! grep -qi "under.*multiplication\|under.*addition\|binary operation\|under.*composition" "$f" 2>/dev/null; then
            echo "  WARNING: $f discusses magma but may not specify the binary operation"
            WARNINGS=$((WARNINGS + 1))
        fi
    fi
done

# 8. Check no RBGame imports in main game
echo ""
echo "[8] Checking for RBGame references in main game..."
RBGAME_REFS=$(grep -rn "RBGame" Game.lean Game/Metadata.lean Game/Levels/*.lean 2>/dev/null | grep -v "^Binary" || true)
if [ -n "$RBGAME_REFS" ]; then
    echo "  WARNING: RBGame references found in main game files:"
    echo "$RBGAME_REFS" | sed 's/^/    /'
    WARNINGS=$((WARNINGS + 1))
fi

# Summary
echo ""
echo "=== Summary ==="
echo "Errors:   $ERRORS"
echo "Warnings: $WARNINGS"
if [ $ERRORS -gt 0 ]; then
    echo "FAILED"
    exit 1
else
    echo "PASSED (with $WARNINGS warnings)"
    exit 0
fi
