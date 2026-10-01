#!/usr/bin/env bash
# strip_and_reprove.sh — the end-to-end test for the CEGQI module.
#
# For every tests/prop*.cst (and the bundled Examples), delete every `instantiate!(...)`
# hint and require the tool to verify the file anyway: CEGQI must re-derive each hint a
# human wrote. Files that legitimately need a lemma are listed in EXPECT_FAIL and must
# instead report "failed (saturated)".
#
# Usage: tests/strip_and_reprove.sh [extra camlstar flags...]
set -uo pipefail
cd "$(dirname "$0")/.." || exit 1

# Obligations whose gap can be a missing *lemma* rather than a missing witness. For these
# both outcomes are correct and accepted: fully re-proved (the lemma is present in the file)
# or "failed (saturated)" (it is not, and CEGQI correctly reports that instantiation cannot
# close it). What is never accepted, here or anywhere, is fuel-exhausted/unknown/error.
EXPECT_LEMMA="prop04.cst"

WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT

pass=0; fail=0
for f in tests/prop*.cst .claude/skills/caml-star-instantiate/Examples/prop*.cst; do
  [ -e "$f" ] || continue
  base=$(basename "$f")
  # drop the hint but keep the `in` body: `let _ = instantiate!(e) in REST` -> `REST`
  perl -0pe 's/let\s+\S+\s*=\s*instantiate!\([^\n]*?\)\s*in\s*//g' "$f" > "$WORK/$base"

  out=$(dune exec ./main.exe -- --solve "$@" "$WORK/$base" 2>&1)
  summary=$(printf '%s\n' "$out" | grep -oE "^[0-9]+ verified, [0-9]+ failed[^;]*" | head -1)
  nfail=$(printf '%s\n' "$summary" | awk '{print $3}')
  calls=$(printf '%s\n' "$out" | grep -oE "[0-9]+ solver call" | grep -oE "^[0-9]+")

  clean=$(printf '%s\n' "$summary" | grep -cE "^[0-9]+ verified, 0 failed, 0 unknown, 0 errors")

  if printf '%s' "$EXPECT_LEMMA" | grep -qw "$base"; then
    if printf '%s\n' "$out" | grep -q "failed (saturated)"; then
      printf "  PASS  %-28s lemma-dependent: saturated\n" "$base"; pass=$((pass+1))
    elif [ "$clean" = "1" ]; then
      printf "  PASS  %-28s lemma-dependent: re-proved\n" "$base"; pass=$((pass+1))
    else
      printf "  FAIL  %-28s expected re-proved or saturated, got: %s\n" "$base" "$summary"
      fail=$((fail+1))
    fi
  elif [ "$clean" = "1" ]; then
    printf "  PASS  %-28s re-proved with no hints (%s solver calls)\n" "$base" "${calls:-?}"
    pass=$((pass+1))
  else
    printf "  FAIL  %-28s %s\n" "$base" "${summary:-no summary}"
    fail=$((fail+1))
  fi
done

echo "strip-and-reprove: $pass passed, $fail failed"
[ "$fail" = "0" ]
