#!/usr/bin/env bash
# Re-decode the raw solver model and re-check the colouring. Needs python3 only --
# no SAT solver, because checking a colouring requires no search.
set -uo pipefail
cd "$(dirname "$0")"

echo "== 1. re-decode the raw model, independently of the shipped witness =="
python3 - <<'PY'
pos = set()
for line in open("raw/solver_model_subcube246.vlines"):
    if not line.startswith("v"):
        continue
    for tok in line.split():
        if tok in ("v", "0"):
            continue
        v = int(tok)
        if v > 0:
            pos.add(v)
n = 21
order = [(i, j) for i in range(1, n + 1) for j in range(i + 1, n + 1)]
dec = {}
for k, e in enumerate(order):           # var(e,c) = edge_index(e)*2 + c
    a, b = (k * 2 + 1) in pos, (k * 2 + 2) in pos
    assert a != b, f"edge {e}: not exactly one colour"
    dec[e] = 1 if a else 2
banked = {}
for l in open("witness/witness_k35k25_n21.txt"):
    if l.startswith("#") or not l.strip():
        continue
    i, j, c = map(int, l.split())
    banked[(i, j)] = c
diff = [e for e in order if dec[e] != banked[e]]
print(f"   {len(order)} edges, {len(diff)} differ from the shipped witness")
assert not diff
PY

echo "== 2. check the colouring (independent checker) =="
python3 tools/check_ramsey.py witness/witness_k35k25_n21.txt K3x5,K2x5 || exit 1

echo "== 3. check it again from the definition, both orientations, with controls =="
python3 - <<'PY'
from itertools import combinations
col = {}
for l in open("witness/witness_k35k25_n21.txt"):
    if l.startswith("#") or not l.strip():
        continue
    i, j, c = map(int, l.split())
    col[(min(i, j), max(i, j))] = c
V = list(range(1, 22))
def c(u, v): return col[(min(u, v), max(u, v))]
def find(colour, s, t):
    for A in combinations(V, s):
        cand = [w for w in V if w not in A and all(c(a, w) == colour for a in A)]
        if len(cand) >= t:
            return A, tuple(cand[:t])
    return None
for name, colour, s, t in [("K_{3,5} colour 1", 1, 3, 5), ("K_{5,3} colour 1", 1, 5, 3),
                           ("K_{2,5} colour 2", 2, 2, 5), ("K_{5,2} colour 2", 2, 5, 2)]:
    r = find(colour, s, t)
    print(f"   {name:18s} {'FOUND ' + str(r) if r else 'ABSENT'}")
    assert r is None, "forbidden subgraph present"
for name, colour, s, t in [("K_{2,2} colour 1 (control)", 1, 2, 2),
                           ("K_{2,2} colour 2 (control)", 2, 2, 2)]:
    r = find(colour, s, t)
    print(f"   {name:26s} {'FOUND — search works' if r else '*** CONTROL FAILED ***'}")
    assert r is not None
def maxcodeg(colour, s):
    return max(sum(1 for w in V if w not in A and all(c(a, w) == colour for a in A))
               for A in combinations(V, s))
print(f"   max common colour-1 nbrs over 3-sets: {maxcodeg(1,3)} (5 would give K_3,5)")
print(f"   max common colour-2 nbrs over 2-sets: {maxcodeg(2,2)} (5 would give K_2,5)")
PY

echo "== 4. re-encode and compare to the shipped formula =="
python3 tools/gen_ramsey.py 21 K3x5,K2x5 --vertex-lex -o /tmp/regen21.cnf
cmp -s /tmp/regen21.cnf instance/k35k25_n21.cnf \
  && echo "   encoder reproduces the shipped CNF bit-for-bit" \
  || { echo "   MISMATCH"; exit 1; }
echo "== all checks passed =="
