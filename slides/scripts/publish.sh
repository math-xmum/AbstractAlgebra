#!/usr/bin/env bash
#
# Publish one slide deck to math-xmum.github.io.
#
# Usage:
#   scripts/publish.sh <slide-basename> [handout-pdf]
#
# Where <slide-basename> is the name without extension, e.g. 05-free-abelian-classification.
# The handout PDF is optional; if omitted, the script looks for
# exercises/L<NN>_Homework.pdf matching the leading number of the slide.
#
# Steps performed:
#   1. Export slide → <basename>.pdf   (via `slidev export`)
#   2. Build static site → dist-<basename>/  (via `slidev build --base /aa2-slides/<basename>/`)
#   3. Copy dist + slide PDF + handout PDF into the github.io repo at
#      aa2-slides/<basename>/
#   4. Commit + push the github.io repo.
#
# Prerequisites:
#   - The github.io repo is cloned at $SITE_REPO (default ~/mydoc/math-xmum.github.io).
#   - You are on the slides/ directory or call the script with its full path.
#
# Does NOT update index.html — do that by hand when flipping a lecture from
# "coming" to "live" (one-time per lecture).

set -euo pipefail

SITE_REPO="${SITE_REPO:-$HOME/mydoc/math-xmum.github.io}"
SLIDES_DIR="$(cd "$(dirname "$0")/.." && pwd)"

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <slide-basename> [handout-pdf]" >&2
  echo "Example: $0 05-free-abelian-classification" >&2
  exit 1
fi

BASENAME="$1"
SLIDE_MD="$SLIDES_DIR/${BASENAME}.md"
[[ -f "$SLIDE_MD" ]] || { echo "Error: $SLIDE_MD not found" >&2; exit 1; }

# Derive the lecture number from the leading digits (05 -> 05, 05-... -> 05)
LEC_NUM="$(echo "$BASENAME" | sed -E 's/^0*([0-9]+).*/\1/')"
LEC_NUM="$(printf '%02d' "$LEC_NUM")"

HANDOUT_PDF="${2:-$SLIDES_DIR/exercises/L${LEC_NUM}_Homework.pdf}"

echo "=== 1/4: Export slide PDF ==="
cd "$SLIDES_DIR"
npx slidev export "${BASENAME}.md" --output "${BASENAME}.pdf"

echo "=== 2/4: Build static site ==="
rm -rf "dist-${BASENAME}"
npx slidev build "${BASENAME}.md" \
  --base "/aa2-slides/${BASENAME}/" \
  --out "dist-${BASENAME}"

echo "=== 3/4: Copy to $SITE_REPO ==="
DEST="$SITE_REPO/aa2-slides/${BASENAME}"
rm -rf "$DEST"
mkdir -p "$DEST"
cp -r "dist-${BASENAME}"/. "$DEST/"
cp "${BASENAME}.pdf" "$DEST/"
if [[ -f "$HANDOUT_PDF" ]]; then
  cp "$HANDOUT_PDF" "$DEST/"
  echo "  handout: $(basename "$HANDOUT_PDF")"
else
  echo "  (no handout at $HANDOUT_PDF — skipping)"
fi

echo "=== 4/4: Commit + push $SITE_REPO ==="
cd "$SITE_REPO"
git add "aa2-slides/${BASENAME}/"
if git diff --cached --quiet; then
  echo "  nothing staged — already up to date"
  exit 0
fi
git commit -m "Publish AAII ${BASENAME}"
git pull --rebase
git push
echo
echo "Published: https://math-xmum.github.io/aa2-slides/${BASENAME}/"
