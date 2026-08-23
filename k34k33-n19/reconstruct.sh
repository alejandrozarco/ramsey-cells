#!/usr/bin/env bash
# Regenerate and re-check every computational artifact in this directory.
#   0. rebuild the negated-cube formula from the .icnf and replay cover.lrat against it
#      (this is what makes the cube decomposition exhaustive)
#   1. re-encode the CNF and confirm it matches the shipped file bit-for-bit
#   2. re-check the n=18 colouring with the independent checker
#   3. re-solve every subcube, re-check every LRAT certificate, delete it
#
# Needs python3 and, on PATH or via the env vars below:
#   cadical    >= 1.5   (tested with 3.0.1)   -- CaDiCaL >= 3 must run with --no-factor,
#                                                which this script passes; factoring
#                                                introduces extension variables that the
#                                                checker soundly rejects.
#   lrat-trim  (https://github.com/arminbiere/lrat-trim)
#   lrat-check (from https://github.com/marijnheule/drat-trim)
set -uo pipefail
cd "$(dirname "$0")"
CAD=${CADICAL:-cadical}; TRIM=${LRAT_TRIM:-lrat-trim}; CHECK=${LRAT_CHECK:-lrat-check}
for t in "$CAD" "$TRIM" "$CHECK"; do
  command -v "$t" >/dev/null || { echo "FATAL: $t not on PATH"; exit 1; }
done
BASE=instance/k34k33_n19.cnf; ICNF=instance/k34k33_n19_d10.icnf

echo "== 0. cube decomposition is exhaustive =="
python3 - "$ICNF" > /tmp/negcubes.cnf <<'PY'
import sys
cubes=[]; mx=0
for line in open(sys.argv[1]):
    if not line.startswith('a '): continue
    lits=[int(x) for x in line[2:].split() if x!='0']
    cubes.append(lits); mx=max(mx,max(abs(l) for l in lits))
out=[f"p cnf {mx} {len(cubes)}"]+[" ".join(str(-l) for l in c)+" 0" for c in cubes]
print("\n".join(out))
PY
if $CHECK /tmp/negcubes.cnf instance/cover.lrat 2>&1 | grep -q "^c VERIFIED"; then
  echo "   cover.lrat refutes the conjunction of all negated cubes: every assignment"
  echo "   satisfies at least one of the $(grep -c '^a ' $ICNF) cubes"
else
  echo "   cover certificate NOT VERIFIED"; exit 1
fi

echo "== 1. re-encode =="
python3 tools/gen_ramsey.py 19 K3x4,K3x3 --vertex-lex -o /tmp/regen.cnf
if cmp -s /tmp/regen.cnf "$BASE"; then echo "   encoder reproduces the shipped CNF"
else echo "   MISMATCH -- encoder output differs from shipped CNF"; exit 1; fi

echo "== 2. the n=18 colouring =="
python3 tools/check_ramsey.py witness/witness_k34k33_n18.txt K3x4,K3x3 || exit 1

echo "== 3. every subcube =="
NV=$(awk '/^p cnf/{print $3;exit}' "$BASE"); NC=$(awk '/^p cnf/{print $4;exit}' "$BASE")
N=$(grep -c '^a ' "$ICNF"); ok=0; bad=0
for i in $(seq 1 "$N"); do
  lits=$(grep '^a ' "$ICNF" | sed -n "${i}p" | sed 's/^a //; s/ 0$//'); nl=$(wc -w <<<"$lits")
  g=/tmp/leaf_$i.cnf
  { echo "p cnf $NV $((NC+nl))"; for l in $lits; do echo "$l 0"; done
    grep -v '^c' "$BASE" | grep -v '^p cnf'; } > "$g"
  if ! $CAD --lrat --no-binary --no-factor --unsat -q "$g" /tmp/leaf_$i.raw 2>/dev/null \
       | grep -q "UNSATISFIABLE"; then
    echo "   subcube $i: NOT reported unsatisfiable"; bad=$((bad+1))
    rm -f "$g" /tmp/leaf_$i.raw; continue
  fi
  $TRIM --ascii "$g" /tmp/leaf_$i.raw /tmp/leaf_$i.lrat >/dev/null 2>&1
  if $CHECK "$g" /tmp/leaf_$i.lrat 2>&1 | grep -q "^c VERIFIED"; then ok=$((ok+1))
  else echo "   subcube $i: certificate NOT VERIFIED"; bad=$((bad+1)); fi
  rm -f "$g" /tmp/leaf_$i.raw /tmp/leaf_$i.lrat
  [ $((i % 50)) -eq 0 ] && echo "   $i/$N ..."
done
echo "== $ok certificates verified, $bad failed, of $N subcubes =="
