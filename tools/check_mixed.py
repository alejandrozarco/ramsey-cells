#!/usr/bin/env python3
"""Arbiter for MIXED specs (bipartite K_sxt and books B_t), written from the definitions,
sharing no code with any encoder.

  K_{s,t} subset G  iff some s-SET has >= t common neighbours.
  B_t = K_2 + t*K_1 subset G  iff some EDGE has >= t common neighbours.
"""
import sys, itertools, re
def load(p):
    col, n = {}, 0
    for l in open(p):
        if l.startswith("#") or not l.strip(): continue
        i, j, c = map(int, l.split()); col[(min(i,j),max(i,j))] = c; n = max(n,i,j)
    return n, col
n, col = load(sys.argv[1])
specs = sys.argv[2].split(",")
assert len(col) == n*(n-1)//2, f"not a complete K_{n}: {len(col)} edges"
assert set(col.values()) <= {1,2}, "colours outside {1,2}"
C = lambda i,j: col[(min(i,j),max(i,j))]
ok_all = True
for ci, g in enumerate(specs, start=1):
    m = re.fullmatch(r"K(\d+)x(\d+)", g)
    if m:
        s, t = int(m.group(1)), int(m.group(2)); mx = 0
        for S in itertools.combinations(range(1,n+1), s):
            cn = sum(1 for w in range(1,n+1) if w not in S and all(C(v,w)==ci for v in S))
            mx = max(mx, cn)
        ok = mx <= t-1
        print(f"  colour {ci}: {g}: max common nbrs of a {s}-set = {mx}, limit {t-1} -> {'ok' if ok else 'VIOLATION'}")
    else:
        t = int(g[1:]); mx = 0
        for u, v in itertools.combinations(range(1,n+1), 2):
            if C(u,v) != ci: continue          # book needs its spine edge in this colour
            cn = sum(1 for w in range(1,n+1) if w!=u and w!=v and C(u,w)==ci and C(v,w)==ci)
            mx = max(mx, cn)
        ok = mx <= t-1
        print(f"  colour {ci}: {g}: max common nbrs over colour-{ci} EDGES = {mx}, limit {t-1} -> {'ok' if ok else 'VIOLATION'}")
    ok_all &= ok
print("VALID" if ok_all else "INVALID")
