#!/usr/bin/env python3
"""General Ramsey-witness arbiter. Written from the DEFINITIONS and sharing no code with
any encoder -- that independence is the whole point, so do not import from gen_*.py.

  usage:  check_any.py <witness file> <spec>        e.g. check_any.py w.txt K3,J4,J4
  exit 0 = VALID (the colouring really avoids every forbidden graph in its colour)

Handles any number of colours, unlike check_ramsey.py/check_mixed.py which assume two.
Token forms:
  KsxT   K_{s,t} bipartite -- present iff some s-SET has >= t common neighbours
  Bt     book B_t = K_2 + t*K_1 -- present iff some EDGE has >= t common neighbours
  Kk     clique on k vertices
  J4     K_4 minus an edge  (= B_2; DS1 line 1277)
  Cn     cycle on n vertices  (C4 = K_{2,2})
  Wn     wheel on n vertices = hub + C_{n-1}   (DS1 lines 1540-1541: W_n has n vertices)
An UNRECOGNISED token is a hard error, never a silent fallback.
"""
import sys, itertools, re

def load(path):
    col, n = {}, 0
    for line in open(path):
        if line.startswith("#") or not line.strip():
            continue
        i, j, c = map(int, line.split())
        col[(min(i, j), max(i, j))] = c
        n = max(n, i, j)
    return n, col

def pattern(tok):
    """Return (nverts, edges) for a named graph token, or None for codegree families."""
    m = re.fullmatch(r"K(\d+)", tok)
    if m:
        k = int(m.group(1))
        return k, [(i, j) for i in range(k) for j in range(i + 1, k)]
    if tok in ("J4", "K4-e"):
        return 4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]      # K4 minus edge (2,3)
    m = re.fullmatch(r"C(\d+)", tok)
    if m:
        k = int(m.group(1))
        assert k >= 3, f"C{k} is not a graph"
        return k, [(i, (i + 1) % k) for i in range(k)]
    m = re.fullmatch(r"W(\d+)", tok)
    if m:
        k = int(m.group(1))                                     # W_k has k vertices
        assert k >= 4, f"W{k} is not a wheel"
        rim = k - 1
        return k, ([(0, r + 1) for r in range(rim)] +
                   [(r + 1, (r + 1) % rim + 1) for r in range(rim)])
    return None

def embeds(nv, edges, adj, hosts):
    """True iff the pattern embeds injectively into the graph given by adj over hosts.
    Plain backtracking with adjacency pruning; patterns here are tiny."""
    deg = [0] * nv
    for a, b in edges:
        deg[a] += 1; deg[b] += 1
    order = sorted(range(nv), key=lambda v: -deg[v])            # most-constrained first
    pos = {v: i for i, v in enumerate(order)}
    # edges to check when placing order[i]: those joining it to an earlier-placed vertex
    back = [[] for _ in range(nv)]
    for a, b in edges:
        i, j = pos[a], pos[b]
        if i < j: back[j].append(a)
        else:     back[i].append(b)
    used, assign = set(), {}
    def go(i):
        if i == nv:
            return True
        v = order[i]
        for h in hosts:
            if h in used:
                continue
            if all(assign[u] in adj[h] for u in back[i]):
                assign[v] = h; used.add(h)
                if go(i + 1):
                    return True
                used.discard(h); del assign[v]
        return False
    return go(0)

def main():
    wf, spec = sys.argv[1], sys.argv[2]
    n, col = load(wf)
    toks = spec.split(",")
    r = len(toks)
    assert len(col) == n * (n - 1) // 2, f"not a complete K_{n}: {len(col)} edges"
    bad = set(col.values()) - set(range(1, r + 1))
    assert not bad, f"colours {sorted(bad)} outside 1..{r} for a {r}-colour spec"
    C = lambda i, j: col[(min(i, j), max(i, j))]
    V = range(1, n + 1)
    ok_all = True
    for ci, g in enumerate(toks, start=1):
        m = re.fullmatch(r"K(\d+)x(\d+)", g)
        if m:                                                   # K_{s,t} by codegree
            s, t = int(m.group(1)), int(m.group(2)); mx = 0
            for S in itertools.combinations(V, s):
                mx = max(mx, sum(1 for w in V if w not in S and all(C(v, w) == ci for v in S)))
            ok = mx <= t - 1
            print(f"  colour {ci}: {g}: max common nbrs of an {s}-set = {mx}, "
                  f"limit {t-1} -> {'ok' if ok else 'VIOLATION'}")
        elif re.fullmatch(r"B(\d+)", g):                        # book by codegree over EDGES
            t = int(g[1:]); mx = 0
            for u, v in itertools.combinations(V, 2):
                if C(u, v) != ci:
                    continue                                    # a book needs its spine
                mx = max(mx, sum(1 for w in V if w != u and w != v
                                 and C(u, w) == ci and C(v, w) == ci))
            ok = mx <= t - 1
            print(f"  colour {ci}: {g}: max common nbrs over colour-{ci} edges = {mx}, "
                  f"limit {t-1} -> {'ok' if ok else 'VIOLATION'}")
        else:
            pat = pattern(g)
            assert pat is not None, f"unrecognised graph token {g!r} in spec {spec!r}"
            nv, edges = pat
            adj = {v: {w for w in V if w != v and C(v, w) == ci} for v in V}
            hit = embeds(nv, edges, adj, list(V))
            ok = not hit
            print(f"  colour {ci}: {g}: contains a copy = {hit} -> {'ok' if ok else 'VIOLATION'}")
        ok_all &= ok
    print("VALID" if ok_all else "INVALID")
    return 0 if ok_all else 1

if __name__ == "__main__":
    sys.exit(main())
