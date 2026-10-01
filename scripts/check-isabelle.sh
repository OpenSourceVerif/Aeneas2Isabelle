#!/bin/sh
# Check the Isabelle prelude and every generated theory in tests/isabelle with
# `isabelle build`.  Each theory gets its own session so that one failure does
# not hide the others.
#
# Usage: scripts/check-isabelle.sh [--strict] [ISABELLE]
#   --strict   fail on `sorry` (by default quick_and_dirty mode is enabled, so
#              admitted lemmas are reported but do not fail the build)
#   ISABELLE   the isabelle executable (default: `isabelle` on PATH)
#
# Theories are checked in a scratch directory: raw Unicode symbols are recoded to
# Isabelle's \<name> escapes (jEdit does this transparently, batch builds do not),
# and the bare `imports "Primitives"` is qualified with the prelude session.
set -eu
cd "$(dirname "$0")/.."
STRICT=0
if [ "${1:-}" = "--strict" ]; then STRICT=1; shift; fi
ISABELLE="${1:-isabelle}"
WORK="${ISABELLE_CHECK_DIR:-$(mktemp -d /tmp/aeneas-isabelle-check.XXXXXX)}"
rm -rf "$WORK/prelude" "$WORK/tests"; mkdir -p "$WORK/prelude" "$WORK/tests"
cp backends/isabelle/Primitives.thy backends/isabelle/ROOT "$WORK/prelude/"
: > "$WORK/tests/ROOT"
SESSIONS=""
for f in tests/isabelle/*.thy; do
  [ -e "$f" ] || { echo "no theories in tests/isabelle (run make test-isabelle first)"; exit 1; }
  b=$(basename "$f" .thy)
  # the prelude copied next to the generated theories is checked from backends/isabelle
  [ "$b" = Primitives ] && continue
  mkdir -p "$WORK/tests/$b"
  sed 's/^    "Primitives"$/    "Aeneas_Prelude.Primitives"/' "$f" > "$WORK/tests/$b/$b.thy"
  printf 'session T_%s in "%s" = Aeneas_Prelude +\n  options [document = false]\n  theories %s\n\n' "$b" "$b" "$b" >> "$WORK/tests/ROOT"
  SESSIONS="$SESSIONS T_$b"
done
python3 scripts/isabelle-recode.py "$WORK"/prelude/*.thy "$WORK"/tests/*/*.thy
OPTS=""; [ $STRICT = 1 ] || OPTS="-o quick_and_dirty"
echo "Checking $(echo $SESSIONS | wc -w | tr -d ' ') theories in $WORK"
set +e
"$ISABELLE" build $OPTS -d "$WORK/prelude" -d "$WORK/tests" -j 4 Aeneas_Prelude $SESSIONS > "$WORK/build.log" 2>&1
STATUS=$?
set -e
grep -E '^(Finished|.* FAILED)' "$WORK/build.log" | sed 's/ (.*//' | sort
grep -E '^\*\*\*' "$WORK/build.log" | grep -v Cheating | head -50 || true
echo "log: $WORK/build.log"
exit $STATUS
