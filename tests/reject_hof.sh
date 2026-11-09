#!/usr/bin/env bash
# reject_hof.sh — the rejection tests of higher-order specialization.
#
# Every tests/hof_reject_*.cst must be rejected before any VC: exit status 1, a
# `specialization error:` whose text contains the file's `EXPECT:` line, and no OCaml
# exception (`Fatal error`).
#
# Usage: tests/reject_hof.sh
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

pass=0; fail=0
for f in tests/hof_reject_*.cst; do
  base=$(basename "$f")
  want=$(sed -n 's/^EXPECT: //p' "$f")
  if [ -z "$want" ]; then
    printf "  FAIL  %-28s no EXPECT: line\n" "$base"; fail=$((fail+1)); continue
  fi
  out=$(dune exec ./main.exe -- --solve "$f" 2>&1); status=$?
  if [ "$status" = "1" ] && printf '%s\n' "$out" | grep -q "^specialization error:" \
     && printf '%s\n' "$out" | grep -qF -- "$want" \
     && ! printf '%s\n' "$out" | grep -q "Fatal error"; then
    printf "  PASS  %-28s rejected as expected\n" "$base"; pass=$((pass+1))
  else
    printf "  FAIL  %-28s exit %s: %s\n" "$base" "$status" "$(printf '%s' "$out" | head -3)"
    fail=$((fail+1))
  fi
done

echo "reject-hof: $pass passed, $fail failed"
[ "$fail" = "0" ]
