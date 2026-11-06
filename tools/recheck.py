"""Second check, written from the definitions only.

Usage: python3 recheck.py FILE A B KIND     (KIND = bip for K_{2,A}/K_{2,B}, book for B_A/B_B)
Reads lines "i j c" (comments '#'), requires a complete 2-colouring of K_N on 1..N.
K_{2,t} is in colour c iff some pair of vertices has >= t common colour-c neighbours.
B_t is in colour c iff some colour-c EDGE has >= t common colour-c neighbours.
Prints N, colour-1 edge count, colour-1 degree range, the max codegree per colour, verdict.
"""
import sys
from itertools import combinations

path, A, B, kind = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
col = {}
for line in open(path):
    line = line.split('#')[0].split()
    if not line:
        continue
    i, j, c = map(int, line)
    assert i != j and c in (1, 2)
    e = (min(i, j), max(i, j))
    assert e not in col, "duplicate edge"
    col[e] = c
N = max(max(e) for e in col)
assert len(col) == N * (N - 1) // 2 and min(min(e) for e in col) == 1, "not complete"
nb = {c: {v: set() for v in range(1, N + 1)} for c in (1, 2)}
for (i, j), c in col.items():
    nb[c][i].add(j); nb[c][j].add(i)
worst = {}
for c in (1, 2):
    pairs = [e for e in combinations(range(1, N + 1), 2) if kind == 'bip' or col[e] == c]
    worst[c] = max(len(nb[c][u] & nb[c][v]) for u, v in pairs)
ok = worst[1] < A and worst[2] < B
d1 = [len(nb[1][v]) for v in range(1, N + 1)]
e1 = sum(1 for c in col.values() if c == 1)
print(f"N={N} e1={e1} e2={len(col)-e1} deg1={min(d1)}..{max(d1)} max1={worst[1]}<{A} max2={worst[2]}<{B} "
      + ("VALID" if ok else "INVALID"))
