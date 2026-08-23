#!/usr/bin/env python3
"""Arbiter for book cells. Written from the definition B_t = K_2 + t*K_1, independently
of gen_ramsey_book.py: colour c contains B_t iff some EDGE uv of colour c has at least t
common colour-c neighbours."""
import sys, itertools
def load(p):
    col, n = {}, 0
    for l in open(p):
        if l.startswith("#") or not l.strip(): continue
        i, j, c = map(int, l.split()); col[(min(i,j),max(i,j))] = c; n = max(n,i,j)
    return n, col
def check(n, col, specs):
    C = lambda i,j: col[(min(i,j),max(i,j))]
    out = []
    for ci, g in enumerate(specs, start=1):
        t = int(g[1:]); mx = 0
        for u, v in itertools.combinations(range(1, n+1), 2):
            if C(u,v) != ci: continue           # book needs the spine edge in colour c
            cn = sum(1 for w in range(1,n+1) if w!=u and w!=v and C(u,w)==ci and C(v,w)==ci)
            mx = max(mx, cn)
        out.append((ci, g, mx, t-1, mx <= t-1))
    return out
if __name__ == "__main__":
    n, col = load(sys.argv[1]); specs = sys.argv[2].split(",")
    assert len(col) == n*(n-1)//2, f"not a complete K_{n}"
    res = check(n, col, specs)
    for ci, g, mx, lim, ok in res:
        print(f"  colour {ci}: max common nbrs over colour-{ci} EDGES = {mx}, "
              f"limit {lim} ({g})  -> {'ok' if ok else 'VIOLATION'}")
    print("VALID" if all(r[4] for r in res) else "INVALID")
