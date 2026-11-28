#!/usr/bin/env bash
# Check the output and exit codes of the `lrat_check` executable (scripts/LratCheck.lean) on a
# valid refutation, a wrong proof, a formula that is not valid UTF-8, a missing file and a wrong
# argument count. Not run by CI.
# Usage: scripts/lrat_check_test.sh [LRAT_CHECK] (default .lake/build/bin/lrat_check; run
# `lake build lrat_check` first)
set -u
cd "$(dirname "$0")/.." || exit 1
bin=${1:-.lake/build/bin/lrat_check}
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
# Every clause over two variables, refuted through a RAT step on the fresh variable 3.
printf 'p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n' > "$dir/f.cnf"
printf '5 3 0 0\n6 -3 1 0 -5 1 2 0\n7 1 0 6 5 0\n8 0 7 3 4 0\n' > "$dir/ok.lrat"
# The same proof without its empty-clause step.
printf '5 3 0 0\n6 -3 1 0 -5 1 2 0\n7 1 0 6 5 0\n' > "$dir/wrong.lrat"
# The formula with a byte that is not valid UTF-8 in a comment.
printf 'c \377\np cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n' > "$dir/bad.cnf"
fail=0
# check NAME EXIT STDOUT ARGS...: the exit code is EXIT and standard output is exactly STDOUT.
check() {
  local name=$1 want_rc=$2 want_out=$3; shift 3
  local out rc
  out=$("$bin" "$@" 2> "$dir/err"); rc=$?
  if [ "$rc" = "$want_rc" ] && [ "$out" = "$want_out" ]; then
    echo "ok   $name: rc=$rc stdout=[$out]"
  else
    echo "FAIL $name: rc=$rc (want $want_rc) stdout=[$out] (want [$want_out])"; fail=1
  fi
  sed 's/^/       stderr: /' "$dir/err"
}
check "valid refutation" 0 "s VERIFIED UNSAT" "$dir/f.cnf" "$dir/ok.lrat"
check "wrong proof" 1 \
  "s REJECTED the certificate does not derive the empty clause by valid steps" \
  "$dir/f.cnf" "$dir/wrong.lrat"
check "invalid UTF-8 formula" 1 "s REJECTED cannot read the formula: it is not valid UTF-8" \
  "$dir/bad.cnf" "$dir/ok.lrat"
check "missing proof file" 2 "" "$dir/f.cnf" "$dir/missing.lrat"
check "wrong argument count" 2 "" "$dir/f.cnf"
exit $fail
