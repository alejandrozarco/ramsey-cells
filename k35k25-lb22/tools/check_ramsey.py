#!/usr/bin/env python3
"""
INDEPENDENT witness checker for multicolor Ramsey colorings. The arbiter.
Shares no code with gen_ramsey.py — checks are written directly from the
graph definitions, using different formulations than the encoder's embedding
enumeration (e.g. J4-freeness is checked as "every 4-set has <= 4 edges of
that color", which is equivalent to containing no K4-e).

Witness format: lines "i j c" (1-based vertices, color), one per edge of K_n.

Usage: check_ramsey.py <witness_file> <colors, e.g. K3,J4,J4>
Exit 0 = VALID (no forbidden monochromatic subgraph), 1 = INVALID, 2 = malformed.
"""
import sys
from itertools import combinations


def main():
    wf, spec = sys.argv[1], sys.argv[2]
    colors = spec.split(",")
    col = {}
    verts = set()
    for line in open(wf):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        i, j, c = map(int, line.split())
        if i > j:
            i, j = j, i
        if (i, j) in col:
            print(f"MALFORMED: duplicate edge {i} {j}")
            sys.exit(2)
        col[(i, j)] = c
        verts.update((i, j))
    n = max(verts)
    if verts != set(range(1, n + 1)) or len(col) != n * (n - 1) // 2:
        print(f"MALFORMED: expected complete K_{n}, got {len(col)} edges")
        sys.exit(2)
    if any(not (1 <= c <= len(colors)) for c in col.values()):
        print("MALFORMED: color out of range")
        sys.exit(2)

    def ecol(a, b):
        return col[(a, b) if a < b else (b, a)]

    for c, g in enumerate(colors, start=1):
        if g == "K3":
            for a, b, d in combinations(range(1, n + 1), 3):
                if ecol(a, b) == c and ecol(a, d) == c and ecol(b, d) == c:
                    print(f"INVALID: color {c} ({g}) triangle {a},{b},{d}")
                    sys.exit(1)
        elif g == "K4":
            for S in combinations(range(1, n + 1), 4):
                if all(ecol(x, y) == c for x, y in combinations(S, 2)):
                    print(f"INVALID: color {c} ({g}) K4 on {S}")
                    sys.exit(1)
        elif g == "J4":
            # contains K4-e in color c  <=>  some 4-set has >= 5 of its 6 edges in c
            for S in combinations(range(1, n + 1), 4):
                if sum(1 for x, y in combinations(S, 2) if ecol(x, y) == c) >= 5:
                    print(f"INVALID: color {c} ({g}) K4-e within {S}")
                    sys.exit(1)
        elif g == "C4":
            # contains C4 in color c  <=>  some pair has >= 2 common c-neighbors
            for u, v in combinations(range(1, n + 1), 2):
                common = sum(1 for w in range(1, n + 1)
                             if w != u and w != v and ecol(u, w) == c and ecol(v, w) == c)
                if common >= 2:
                    print(f"INVALID: color {c} ({g}) C4 through {u},{v}")
                    sys.exit(1)
        elif g.startswith("K") and "x" in g:
            # complete bipartite K_{s,t}, spec "KsxT" e.g. K3x4.
            # G contains K_{s,t} in color c  <=>  some s-set has >= t common c-neighbors
            # (the s-side of any embedded copy is such a set, and conversely).
            s, t = (int(x) for x in g[1:].split("x"))
            # primary check via the t-SIDE (any t-set with >= s common c-neighbors),
            # deliberately the opposite side from the encoder's s-set constraints;
            # the cheap s-side check is kept as a redundant cross-check.
            for S in combinations(range(1, n + 1), t):
                Sset = set(S)
                common = sum(1 for w in range(1, n + 1)
                             if w not in Sset and all(ecol(u, w) == c for u in S))
                if common >= s:
                    print(f"INVALID: color {c} ({g}) K_{{{s},{t}}} on t-side {S}")
                    sys.exit(1)
            for S in combinations(range(1, n + 1), s):
                common = sum(1 for w in range(1, n + 1)
                             if w not in S and all(ecol(u, w) == c for u in S))
                if common >= t:
                    print(f"INVALID: color {c} ({g}) K_{{{s},{t}}} on s-side {S}")
                    sys.exit(1)
        elif g == "P3":
            # path on 3 vertices: two edges sharing a center vertex
            for mid in range(1, n + 1):
                nb = [v for v in range(1, n + 1) if v != mid and ecol(mid, v) == c]
                if len(nb) >= 2:
                    print(f"INVALID: color {c} ({g}) path {nb[0]}-{mid}-{nb[1]}")
                    sys.exit(1)
        else:
            print(f"MALFORMED: unknown graph {g}")
            sys.exit(2)
    print(f"VALID: coloring of K_{n} avoids " +
          ", ".join(f"{g} in color {c}" for c, g in enumerate(colors, 1)))
    sys.exit(0)


if __name__ == "__main__":
    main()
