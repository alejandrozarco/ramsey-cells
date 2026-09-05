#!/usr/bin/env python3
"""
Encoder for multicolor graph Ramsey SAT instances.

Instance: does there exist an r-coloring of the edges of K_n such that color c
contains no copy of forbidden graph G_c (c = 1..r)?  SAT <=> such a coloring
exists <=> R(G_1,...,G_r) > n.

Encoding:
  - var(e, c) for each edge e of K_n and color c in 1..r  (true <=> e has color c)
  - ALO per edge: (v_e1 | ... | v_er)
  - AMO per edge, pairwise: (~v_ec | ~v_ec') for c < c'
    (assignments are then exactly edge colorings; symmetry arguments act cleanly)
  - for every copy of G_c in K_n (every distinct image edge set E under injective
    embedding): clause  OR_{e in E} ~var(e, c)
  - optional --swap-break C1 C2 (sound only when G_C1 == G_C2): row-1 lex
    constraint  (var({1,j},C1))_j  >=lex  (var({1,j},C2))_j  over j = 2..n,
    via a standard eq-chain with auxiliary variables.  Sound because swapping
    colors C1<->C2 is an automorphism of the constraint set, and any coloring
    or its swap satisfies the lex order.
  - optional --cube D: WLOG fix vertex 1's color-1
    neighborhood to {2..D+1} (units).  D = "10plus" fixes {2..11} in color 1
    and leaves the rest free, covering all degrees >= 10 up to relabeling.
    Sound: vertex relabelings fixing vertex 1 commute with the C2<->C3 swap.

Graphs: K3, K4, J4 (= K4-e, edges 01 02 03 12 13), P3 (path, edges 01 12).
"""
import argparse
import itertools
import sys

GRAPHS = {
    "K3": (3, [(0, 1), (0, 2), (1, 2)]),
    "K4": (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]),
    "J4": (4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]),  # K4 minus edge (2,3)
    "P3": (3, [(0, 1), (1, 2)]),
    "C4": (4, [(0, 1), (1, 2), (2, 3), (3, 0)]),          # 4-cycle = K_{2,2}
}


def edge_index(n):
    idx = {}
    k = 0
    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):
            idx[(i, j)] = k
            k += 1
    return idx


def copies(n, gname):
    """Distinct edge sets of copies of G in K_n (vertices 1..n)."""
    k, gedges = GRAPHS[gname]
    seen = set()
    out = []
    for sub in itertools.combinations(range(1, n + 1), k):
        local = set()
        for perm in itertools.permutations(sub):
            es = frozenset(tuple(sorted((perm[u], perm[v]))) for u, v in gedges)
            local.add(es)
        for es in local:
            if es not in seen:
                seen.add(es)
                out.append(es)
    return out


def build(n, colors, swap_break=None, cube=None, vertex_lex=False):
    """Returns (clauses, nvars, comments). colors: list of graph names, 1-based colors."""
    r = len(colors)
    eidx = edge_index(n)
    E = len(eidx)

    def var(e, c):  # e = (i,j) i<j, c in 1..r
        assert 1 <= c <= r, f"color {c} out of range for r={r}"
        return eidx[e] * r + c

    nvars = E * r
    cls = []
    comments = [f"c R({','.join(colors)}) at n={n}: SAT iff R > n",
                f"c {E} edges x {r} colors = {E*r} edge vars"]

    for e in eidx:
        cls.append([var(e, c) for c in range(1, r + 1)])          # ALO
        for c1, c2 in itertools.combinations(range(1, r + 1), 2):  # AMO
            cls.append([-var(e, c1), -var(e, c2)])

    for c, g in enumerate(colors, start=1):
        if "x" in g and g.startswith("K"):
            # complete bipartite K_{s,t} via CODEGREE encoding (never enumerate copies):
            # color c is K_{s,t}-free  <=>  every s-set has <= t-1 common c-neighbors.
            # y_{S,w} is an upper indicator: (AND_{v in S} edge(v,w,c)) -> y, then a
            # one-directional sequential counter bounds  sum_w y_{S,w} <= t-1.
            s, t = (int(x) for x in g[1:].split("x"))
            k = t - 1
            nsets = 0
            for S in itertools.combinations(range(1, n + 1), s):
                nsets += 1
                ys = []
                for w in range(1, n + 1):
                    if w in S:
                        continue
                    nvars += 1
                    y = nvars
                    cls.append([-var(tuple(sorted((v, w))), c) for v in S] + [y])
                    ys.append(y)
                # Sinz <=k over ys: R(i,j) = "at least j of ys[0..i]" (1-based)
                m = len(ys)
                assert m > k, "n too small for the bound to bind"
                R = {}
                for i in range(1, m):        # registers for prefixes 1..m-1
                    for j in range(1, k + 1):
                        nvars += 1
                        R[(i, j)] = nvars
                cls.append([-ys[0], R[(1, 1)]])
                for i in range(2, m):
                    cls.append([-ys[i - 1], R[(i, 1)]])
                    for j in range(1, k + 1):
                        cls.append([-R[(i - 1, j)], R[(i, j)]])
                    for j in range(2, k + 1):
                        cls.append([-ys[i - 1], -R[(i - 1, j - 1)], R[(i, j)]])
                for i in range(2, m + 1):
                    cls.append([-ys[i - 1], -R[(i - 1, k)]])
            comments.append(f"c color {c} forbids {g} (codegree): {nsets} {s}-sets, <= {k} common nbrs each")
            continue
        cps = copies(n, g)
        comments.append(f"c color {c} forbids {g}: {len(cps)} copies")
        for es in cps:
            cls.append([-var(e, c) for e in sorted(es)])

    if swap_break:
        # Chain of 2+ color indices with identical forbidden graphs. For each adjacent
        # pair (c_i, c_{i+1}) impose row-1 lex order c_i >= c_{i+1}. Sound: the colors in
        # the chain are interchangeable (S_k acts), and any coloring can be recolored so
        # the row-1 indicator vectors are in non-increasing lex order; the adjacent-pair
        # constraints assert exactly that sortedness. Commutes with vertex-lex as before.
        chain = list(swap_break)
        for a, b in zip(chain, chain[1:]):
            assert colors[a - 1] == colors[b - 1], "swap-break needs identical forbidden graphs"
    for c1, c2 in (zip(chain, chain[1:]) if swap_break else []):
        seq = [(var((1, j), c1), var((1, j), c2)) for j in range(2, n + 1)]
        # a >= lex b with eq-chain aux vars
        eq = {}
        for t in range(1, len(seq)):  # eq_t needed as premise for position t+1
            nvars += 1
            eq[t] = nvars
        a1, b1 = seq[0]
        cls.append([-b1, a1])
        for t in range(1, len(seq)):
            at, bt = seq[t]
            ap, bp = seq[t - 1]
            e = eq[t]
            prem = [] if t == 1 else [-eq[t - 1]]
            # eq_t <-> (prefix eq) & (a_t-1..: define over position t-1's equality chain)
            # eq_t means positions 1..t of (a,b) are equal
            # eq_1 <-> (a_1 == b_1); eq_t <-> eq_{t-1} & (a_t == b_t) [positions 1-based]
            # here seq index t-1 is position t
            pa, pb = seq[t - 1]
            if t == 1:
                cls += [[-e, -pa, pb], [-e, pa, -pb], [e, pa, pb], [e, -pa, -pb]]
            else:
                ep = eq[t - 1]
                cls += [[-e, ep], [-e, -pa, pb], [-e, pa, -pb],
                        [e, -ep, pa, pb], [e, -ep, -pa, -pb]]
            cls.append([-e, -bt, at])
        comments.append(f"c swap-break colors {c1}>={c2} on row 1 (lex), {len(seq)-1} aux vars")

    if vertex_lex:
        # Static partial symmetry breaking: for each adjacent transposition s=(v,v+1)
        # in the allowed blocks, impose  valseq(x) <=lex valseq(x o s), where valseq
        # is the color-value sequence over edges in global edge order and values are
        # ordered 1 < 2 < 3.  Sound because the lex-min of the orbit under the group
        # generated by the allowed vertex transpositions satisfies every single-generator
        # constraint simultaneously (each x o s is in the orbit, and x is its minimum),
        # and cube constraints are preserved by the blocks.  NOTE: the color swap is a
        # symmetry only when the forbidden graphs are identical; it is broken separately
        # by --swap-break, which asserts that, and it is NOT part of the group here.
        if cube is None:
            transpositions = list(range(1, n))
        elif cube == "10plus":
            transpositions = list(range(2, 10)) + list(range(12, n))
        else:
            d = int(cube)
            transpositions = list(range(2, d + 1)) + list(range(d + 2, n))
        edges_in_order = sorted(eidx, key=lambda e: eidx[e])
        n_lex_aux = 0
        for v in transpositions:
            sig = lambda x: v + 1 if x == v else (v if x == v + 1 else x)
            moved = []
            for e in edges_in_order:
                f = tuple(sorted((sig(e[0]), sig(e[1]))))
                if f != e:
                    moved.append((e, f))
            eqch = None  # eq-chain var: positions so far all equal
            for t, (e, f) in enumerate(moved):
                prem = [] if eqch is None else [-eqch]
                # val(e) <= val(f) given prefix equality: forbid val(e) > val(f)
                for cf in range(1, r + 1):
                    for ce in range(cf + 1, r + 1):
                        cls.append(prem + [-var(e, ce), -var(f, cf)])
                if t == len(moved) - 1:
                    break
                # q <-> (val(e) == val(f));  new chain var eq' <-> eq & q
                nvars += 1
                q = nvars
                n_lex_aux += 1
                for c in range(1, r + 1):
                    cls.append([-q, -var(e, c), var(f, c)])
                    cls.append([q, -var(e, c), -var(f, c)])
                nvars += 1
                newch = nvars
                n_lex_aux += 1
                if eqch is None:
                    cls += [[-newch, q], [newch, -q]]
                else:
                    cls += [[-newch, eqch], [-newch, q], [newch, -eqch, -q]]
                eqch = newch
        comments.append(f"c vertex-lex: {len(transpositions)} adjacent transpositions, "
                        f"{n_lex_aux} aux vars")

    if cube is not None:
        if cube == "10plus":
            fixed = list(range(2, 12))
            free_rest = True
        else:
            d = int(cube)
            fixed = list(range(2, d + 2))
            free_rest = False
        for j in fixed:
            cls.append([var((1, j), 1)])
        if not free_rest:
            for j in range(fixed[-1] + 1 if fixed else 2, n + 1):
                cls.append([-var((1, j), 1)])
        comments.append(f"c cube {cube}: N_1(1) {'>=' if free_rest else '='} {{{fixed[0] if fixed else ''}..{fixed[-1] if fixed else ''}}}")

    return cls, nvars, comments


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("n", type=int)
    ap.add_argument("colors", help="comma list, e.g. K3x4,K3x3")
    ap.add_argument("--swap-break", help="two color indices, e.g. 2,3")
    ap.add_argument("--cube", help="0..9 or 10plus")
    ap.add_argument("--vertex-lex", action="store_true")
    ap.add_argument("-o", "--out", default="/dev/stdout")
    a = ap.parse_args()
    colors = a.colors.split(",")
    for g in colors:
        if "x" in g and g.startswith("K"):
            s, t = (int(x) for x in g[1:].split("x"))
            assert 2 <= s <= t, f"bad bipartite spec {g} (need 2<=s<=t)"
        else:
            assert g in GRAPHS, f"unknown graph {g}"
    sb = tuple(int(x) for x in a.swap_break.split(",")) if a.swap_break else None
    if sb is not None:
        assert len(sb) >= 2, "swap-break needs at least two color indices"
    cls, nv, com = build(a.n, colors, sb, a.cube, a.vertex_lex)
    with open(a.out, "w") as f:
        for c in com:
            f.write(c + "\n")
        f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls:
            f.write(" ".join(map(str, c)) + " 0\n")
    print(f"wrote {a.out}: {nv} vars, {len(cls)} clauses", file=sys.stderr)


if __name__ == "__main__":
    main()
