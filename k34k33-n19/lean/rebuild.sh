#!/usr/bin/env bash
# Rebuild the Lean theorem base_unsat : base.Unsat from the files in this repository.
#
#   bash lean/rebuild.sh [workdir]
#
# Needs: git, elan (https://github.com/leanprover/elan), and on PATH or via the env vars
# below: cadical >= 3 (with --lrat), lrat-trim, lrat-check.
#
# Cost: about 2.4 CPU-hours to refute the 571 subcubes, then a long Lean build. The final
# composing step imports one module per subcube, roughly 16 GB of .olean, and needs the
# memory to hold them: it succeeded on a 64 GB machine and failed on 16 GB.
#
# Everything is regenerated. Nothing here trusts the certificates shipped in this repo;
# cover.lrat is rebuilt too, and the result is compared against the shipped copy.
set -uo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
W="${1:-$PWD/lean-rebuild}"
CAD=${CADICAL:-cadical}; TRIM=${LRAT_TRIM:-lrat-trim}; CHECK=${LRAT_CHECK:-lrat-check}
for t in "$CAD" "$TRIM" "$CHECK" git elan; do
  command -v "$t" >/dev/null || { echo "FATAL: $t not on PATH"; exit 1; }
done
mkdir -p "$W" && cd "$W" || exit 1
CNF="$HERE/instance/k34k33_n19.cnf"; ICNF="$HERE/instance/k34k33_n19_d10.icnf"
NAME=k34k33_n19_unsat

echo "== 1. lrat-catcher =="
[ -d lrat-catcher ] || git clone -q https://github.com/leansolving/lrat-catcher
cd lrat-catcher && git checkout -q 4ec2168 && lake build lratcatch-export lratcatch-cover-parallel
LC=$PWD; cd "$W"

echo "== 2. split the formula by the cube file =="
# writes export/leaf1.cnf .. export/leafN.cnf, plus export/negcubes.cnf
[ -d export ] || "$LC/.lake/build/bin/lratcatch-export" "$CNF" "$ICNF" export
N=$(ls export | grep -c '^leaf[0-9]*\.cnf$'); echo "   $N leaf formulas"

echo "== 3. cover certificate =="
# negcubes.cnf is the conjunction of the NEGATED cubes; refuting it shows the cubes
# leave no assignment uncovered. This is what instance/cover.lrat contains.
if [ ! -s cover.lrat ]; then
  $CAD --lrat --no-binary --no-factor --unsat -q export/negcubes.cnf cover.raw >/dev/null 2>&1
  $TRIM --ascii export/negcubes.cnf cover.raw cover.lrat >/dev/null 2>&1
fi
$CHECK export/negcubes.cnf cover.lrat 2>&1 | grep -q "^c VERIFIED" \
  && echo "   rebuilt cover.lrat verifies" || { echo "   cover FAILED"; exit 1; }
cmp -s cover.lrat "$HERE/instance/cover.lrat" \
  && echo "   byte-identical to the shipped instance/cover.lrat" \
  || echo "   NOTE: differs byte-wise from the shipped copy (both may still be valid)"

echo "== 4. refute every subcube =="
mkdir -p proofs
for i in $(seq 1 "$N"); do
  [ -s "proofs/leaf_$i.lrat" ] && continue
  $CAD --lrat --no-binary --no-factor --unsat -q "export/leaf$i.cnf" "proofs/raw_$i" >/dev/null 2>&1
  [ -s "proofs/raw_$i" ] || { echo "   subcube $i produced no proof"; exit 1; }
  $TRIM --ascii "export/leaf$i.cnf" "proofs/raw_$i" "proofs/leaf_$i.lrat" >/dev/null 2>&1
  $CHECK "export/leaf$i.cnf" "proofs/leaf_$i.lrat" 2>&1 | grep -q "^c VERIFIED" \
    || { echo "   subcube $i certificate NOT VERIFIED"; exit 1; }
  rm -f "proofs/raw_$i"
  [ $((i % 50)) -eq 0 ] && echo "   $i/$N"
done
echo "   $N/$N verified"

echo "== 5. emit the Lean modules =="
# chunkSize must stay 1: a module whose embedded certificate pushes its .olean past ~2 GB
# builds but cannot afterwards be imported.
cd "$LC"
./.lake/build/bin/lratcatch-cover-parallel "$CNF" "$ICNF" "$W/proofs/leaf_" "$W/cover.lrat" "$NAME" 1

echo "== 6. build the chunks, then compose =="
bash "LRATCatcher/Generated/$NAME/build.sh"
lake build "LRATCatcher.Generated.$NAME.Main"

echo "== done. compare the axioms against the shipped record =="
echo "   the build prints '#print axioms base_unsat'; it should list propext,"
echo "   Classical.choice, Quot.sound and 572 native_decide axioms, and no sorryAx,"
echo "   matching AXIOMS.txt in this repository."
