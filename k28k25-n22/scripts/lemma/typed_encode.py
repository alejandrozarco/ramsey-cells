#!/usr/bin/env python3
"""Degree-typed formulas for two-colour codegree cells R(K_{2,s}, K_{2,t}); written for K2x8,K2x5 at N=22
(2026-09-09 ~05:40 UTC, the 2003 cell).

Type = a nondecreasing sequence D[1..N] of blue (colour-2) degrees. Canonical form: for a good colouring choose a
labelling with d_1 <= ... <= d_N; the labellings with sorted degrees form a coset of the within-class permutation
group (classes = maximal runs of equal degree); take the lex-min colouring (gen_ramsey's valseq order) in that
coset. It satisfies (i) blue degree exactly D[v] at v, (ii) valseq(x) <=lex valseq(x o s) for every adjacent
transposition s inside a class (x o s is in the coset). So every good graph with degree multiset D has a
representative satisfying the formula for D, and the cell is refuted once the formula is UNSAT for every type a
good graph can have (for the 2003 cell: the 44 histograms 8^a 9^b 10^c of the degree lemma, scripts/astra/).

Formula for D = base (gen_ramsey.build with the within-class transposition list) + exact degree per vertex
(bidirectional Sinz counter) + per-pair codegree intervals implied by the identity
    c_red(i,j) = (N-2) - d_i - d_j + 2 A_ij + c_blue(i,j),   0 <= c_blue <= b,  0 <= c_red <= r,
for both colours, both directions, conditional on the colour of ij (bidirectional counters over the common
neighbour indicators). The base already carries c_blue <= b and c_red <= r.

--selftest: brute force on tiny cells (every colouring enumerated): every canonical good colouring satisfies the
formula of its type, every model of a typed formula decodes to a good colouring of that type, and the typed
formula is SAT exactly for the types that occur.
usage: typed_encode.py N K2xs,K2xt --type d1,...,dN -o out.cnf   |   typed_encode.py --selftest
"""
import argparse, itertools, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.abspath(os.path.join(HERE, '..', '..')))
from gen_ramsey import build, edge_index
from lemma_encode import Enc
CAD = os.environ.get('CADICAL', 'cadical')

def bounds(N, b, r, di, dj, A):
    """Identity-only (blue_lo, blue_hi, red_lo, red_hi) for a pair with blue degrees di, dj and blue adjacency A."""
    base = (N - 2) - di - dj + 2 * A            # c_red - c_blue
    blue_lo = max(0, -base); blue_hi = min(b, r - base)
    red_lo = max(0, base); red_hi = min(r, base + b)
    return blue_lo, blue_hi, red_lo, red_hi

def budget_of(N, b, r, d):
    """Lambda_v: the exact total deficit at a vertex of blue degree d (Astra 2026-09-09 (A), checked by hand):
    sum over blue neighbours of (r - c_red) plus sum over non-neighbours of (b - c_blue) = d(r - t) + b t, t = N-1-d.
    For K2x8,K2x5 at N=22 this is (d-9)^2 + 3. Negative means the degree is impossible."""
    t = N - 1 - d
    return d * (r - t) + b * t

def classes_of(D):
    cl = []; start = 0
    for i in range(1, len(D) + 1):
        if i == len(D) or D[i] != D[start]: cl.append((start + 1, i)); start = i
    return cl        # 1-based inclusive vertex ranges

def add_counting(enc, N, b, r, D, var, tight=False, budget=False, classcounts=False, cl=None, channel=False):
    """Append to enc: exact blue degree D[v] per vertex, per-pair codegree intervals from the identity (tightened by the
    per-vertex budgets if tight), the exact deficit sums (B) if budget, class edge counts if classcounts. Sound for
    any labelling: these are properties of a good graph with degree sequence D. Returns the clause-family counts."""
    counts = {}; n0 = len(enc.cls)
    Lam = {v: budget_of(N, b, r, D[v - 1]) for v in range(1, N + 1)}
    for v in range(1, N + 1):                                    # exact blue degree
        xs = [var(v, u, 2) for u in range(1, N + 1) if u != v]; m = len(xs); d = D[v - 1]
        R = enc.bidir_counter(xs, min(m, d + 1))
        if d >= 1: enc.add([R[(m, d)]])
        if d + 1 <= m: enc.add([-R[(m, d + 1)]])
    counts['degree'] = len(enc.cls) - n0
    Ry = {}; Rz = {}; M = N - 2
    for i, j in itertools.combinations(range(1, N + 1), 2):      # identity intervals, conditional on A_ij
        di, dj = D[i - 1], D[j - 1]; A = var(i, j, 2)
        ws = [w for w in range(1, N + 1) if w not in (i, j)]
        ys = []; zs = []
        for w in ws:
            y = enc.new(); ys.append(y); enc.add([-var(i, w, 2), -var(j, w, 2), y]); enc.add([-y, var(i, w, 2)]); enc.add([-y, var(j, w, 2)])
            z = enc.new(); zs.append(z); enc.add([-var(i, w, 1), -var(j, w, 1), z]); enc.add([-z, var(i, w, 1)]); enc.add([-z, var(j, w, 1)])
        Ry[(i, j)] = enc.bidir_counter(ys, min(M, b + 1)); Rz[(i, j)] = enc.bidir_counter(zs, min(M, r + 1))
        # Ry[(i,j)][(M,t)] <-> C_ij >= t, the EXACT blue-codegree threshold over all M = N-2 vertices
        # w outside {i,j}. Stashed on the encoder so a later layer can reference these thresholds
        # without rebuilding them. Attribute only: no clause is added, removed or reordered here, and
        # the emitted CNF is byte-identical with and without this line (checked by sha256 on three
        # cubes before the change was kept).
        L = {a: (N - 2) - di - dj + 2 * a for a in (0, 1)}
        for a in (0, 1):
            bl, bh, rl, rh = bounds(N, b, r, di, dj, a)
            if tight:
                lam = min(Lam[i], Lam[j])
                if a == 1: rl = max(rl, r - lam)
                else: bl = max(bl, b - lam)
                bl = max(bl, rl - L[a]); rl = max(rl, bl + L[a]); bh = min(bh, rh - L[a]); rh = min(rh, bh + L[a])
            cond = -A if a == 1 else A                                  # literal false under the condition
            if bl > bh or rl > rh: enc.add([cond]); continue           # colour a for ij is impossible
            if bl >= 1: enc.add([cond, Ry[(i, j)][(M, bl)]])
            if bh + 1 <= M: enc.add([cond, -Ry[(i, j)][(M, bh + 1)]])
            if rl >= 1: enc.add([cond, Rz[(i, j)][(M, rl)]])
            if rh + 1 <= M: enc.add([cond, -Rz[(i, j)][(M, rh + 1)]])
    if channel:      # explicit channeling of the two codegree counters through the complement identity (sound: R = L + C)
        for i, j in itertools.combinations(range(1, N + 1), 2):
            A = var(i, j, 2); di, dj = D[i - 1], D[j - 1]
            for a in (0, 1):
                L = (N - 2) - di - dj + 2 * a; cond = -A if a == 1 else A
                for q in range(1, min(M, b + 1) + 1):
                    if (M, q) not in Ry[(i, j)]: continue
                    lhs = Ry[(i, j)][(M, q)]; qq = q + L
                    if qq <= 0: enc.add([cond, lhs])                                   # R >= qq always true -> C >= q
                    elif qq > M or (M, qq) not in Rz[(i, j)]: enc.add([cond, -lhs])    # R >= qq impossible -> C < q
                    else: enc.add([cond, -lhs, Rz[(i, j)][(M, qq)]]); enc.add([cond, lhs, -Rz[(i, j)][(M, qq)]])
    enc.Ry = Ry; enc.Rz = Rz
    counts['intervals'] = len(enc.cls) - n0 - counts['degree']
    if budget:                                                   # (B): exact deficit sum per vertex
        for v in range(1, N + 1):
            lam = Lam[v]
            if lam < 0: enc.add([]); continue                      # impossible degree: empty clause
            Es = []
            for u in range(1, N + 1):
                if u == v: continue
                key = (min(u, v), max(u, v)); A = var(u, v, 2)
                for l in range(1, min(lam, max(r, b)) + 1):
                    # P <-> A and c_red <= r-l ; Q <-> not A and c_blue <= b-l ; E <-> P or Q
                    P = enc.new(); Q = enc.new(); E = enc.new()
                    if r - l < 0: enc.add([-P])
                    else:
                        lit = -Rz[key][(M, r - l + 1)] if r - l + 1 <= M else None      # None: c_red <= r-l always true
                        if lit is None: enc.add([-P, A]); enc.add([P, -A])
                        else: enc.add([-P, A]); enc.add([-P, lit]); enc.add([P, -A, -lit])
                    if b - l < 0: enc.add([-Q])
                    else:
                        lit = -Ry[key][(M, b - l + 1)] if b - l + 1 <= M else None
                        if lit is None: enc.add([-Q, -A]); enc.add([Q, A])
                        else: enc.add([-Q, -A]); enc.add([-Q, lit]); enc.add([Q, A, -lit])
                    enc.add([-E, P, Q]); enc.add([E, -P]); enc.add([E, -Q]); Es.append(E)
            if not Es:
                if lam > 0: enc.add([])
                continue
            Rb = enc.bidir_counter(Es, min(len(Es), lam + 1))
            if lam >= 1:
                if lam <= len(Es): enc.add([Rb[(len(Es), lam)]])
                else: enc.add([])
            if lam + 1 <= len(Es): enc.add([-Rb[(len(Es), lam + 1)]])
        counts['budget'] = len(enc.cls) - n0 - counts['degree'] - counts['intervals']
    if classcounts:                                              # exact class edge counts and total edge count
        before = len(enc.cls); cl = cl or classes_of(D)
        def exact(xs, k):
            if not xs:
                if k != 0: enc.add([])
                return
            R = enc.bidir_counter(xs, min(len(xs), k + 1))
            if k >= 1:
                if k <= len(xs): enc.add([R[(len(xs), k)]])
                else: enc.add([])
            if k + 1 <= len(xs): enc.add([-R[(len(xs), k + 1)]])
        allblue = [var(i, j, 2) for i, j in itertools.combinations(range(1, N + 1), 2)]
        exact(allblue, sum(D) // 2)
        for (lo, hi) in cl:                                      # sum of degrees over a class = 2 e(inside) + e(class, outside)
            inside = [var(i, j, 2) for i in range(lo, hi + 1) for j in range(i + 1, hi + 1)]
            out = [var(i, j, 2) for i in range(lo, hi + 1) for j in range(1, N + 1) if not (lo <= j <= hi)]
            exact(inside + inside + out, sum(D[lo - 1:hi]))
        counts['classcounts'] = len(enc.cls) - before
    return counts

def typed_formula(N, colors, D, tight=False, budget=False, allpairs=False, classcounts=False):
    """Returns (clauses, nvars, comments). colors = ['K2xs', 'K2xt']; colour 2 (second) is 'blue', its degree is typed.
    tight: pair intervals sharpened by the per-vertex budget (each deficit <= Lambda_v of both endpoints).
    budget: exact per-vertex deficit sum (B) via threshold indicators (implies tight).
    allpairs: lex constraints for ALL within-class transpositions, not only adjacent ones (same Gamma-min).
    classcounts: exact class edge-count equations and the total edge count (consequences of the exact degrees)."""
    assert len(D) == N and all(D[i] <= D[i + 1] for i in range(N - 1)), 'type must be nondecreasing'
    if budget: tight = True
    s = int(colors[0].split('x')[1]); t = int(colors[1].split('x')[1]); r = s - 1; b = t - 1
    cl = classes_of(D)
    if allpairs: trans = [(u, w) for (lo, hi) in cl for u in range(lo, hi + 1) for w in range(u + 1, hi + 1)]
    else: trans = [(v, v + 1) for (lo, hi) in cl for v in range(lo, hi)]
    cls, nv, com = build(N, colors, vertex_lex=trans if trans else [])
    eidx = edge_index(N)
    def var(i, j, c): return eidx[(min(i, j), max(i, j))] * 2 + c
    enc = Enc(nv); Lam = {v: budget_of(N, b, r, D[v - 1]) for v in range(1, N + 1)}
    counts = add_counting(enc, N, b, r, D, var, tight=tight, budget=budget, classcounts=classcounts, cl=cl)
    com = com + [f"c typed_encode: type {','.join(map(str, D))} classes {cl}; within-class {'all-pairs' if allpairs else 'adjacent'} lex ({len(trans)} transpositions)"
                 f"; options tight={tight} budget={budget} classcounts={classcounts}; budgets {sorted(set(Lam.values()))}",
                 f"c appended clauses {counts}; {enc.nv - nv} new vars"]
    return cls + enc.cls, enc.nv, com

def write(path, cls, nv, com):
    with open(path, 'w') as f:
        f.write('\n'.join(com) + '\n'); f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls: f.write(' '.join(map(str, c)) + ' 0\n')

OPTS = [dict(), dict(tight=True), dict(budget=True), dict(budget=True, allpairs=True), dict(budget=True, classcounts=True)]
def selftest():
    import random
    def good(N, col, s, t, eidx):       # col: dict edge -> 1 (red) / 2 (blue)
        for i, j in itertools.combinations(range(1, N + 1), 2):
            cb = sum(1 for w in range(1, N + 1) if w not in (i, j) and col[(min(i, w), max(i, w))] == 2 and col[(min(j, w), max(j, w))] == 2)
            cr = sum(1 for w in range(1, N + 1) if w not in (i, j) and col[(min(i, w), max(i, w))] == 1 and col[(min(j, w), max(j, w))] == 1)
            if cb > t - 1 or cr > s - 1: return False
        return True
    def relabel(N, col, perm):          # perm: new label -> old label
        return {(i, j): col[(min(perm[i], perm[j]), max(perm[i], perm[j]))] for i, j in itertools.combinations(range(1, N + 1), 2)}
    def valseq(N, col): return tuple(col[e] for e in sorted(col))
    fails = 0; tested = 0
    for (N, colors) in ((5, ['K2x2', 'K2x3']), (6, ['K2x2', 'K2x3']), (6, ['K2x3', 'K2x3'])):
        s = int(colors[0][3:]); t = int(colors[1][3:]); eidx = edge_index(N); edges = sorted(eidx)
        canon = {}      # type -> set of canonical colourings
        for bits in itertools.product((1, 2), repeat=len(edges)):
            col = dict(zip(edges, bits))
            if not good(N, col, s, t, eidx): continue
            deg = {v: sum(1 for u in range(1, N + 1) if u != v and col[(min(u, v), max(u, v))] == 2) for v in range(1, N + 1)}
            order = sorted(range(1, N + 1), key=lambda v: deg[v]); D = tuple(deg[v] for v in order)
            cl = classes_of(D); best = None
            groups = [list(range(lo, hi + 1)) for lo, hi in cl]
            for perms in itertools.product(*[itertools.permutations(g) for g in groups]):
                pos = {}
                for g, p in zip(groups, perms):
                    for slot, newpos in zip(g, p): pos[slot] = newpos
                perm = {newpos: order[slot - 1] for slot, newpos in pos.items()}     # new label -> old vertex
                c2 = relabel(N, col, perm); vs = valseq(N, c2)
                if best is None or vs < best[0]: best = (vs, c2)
            canon.setdefault(D, set()).add(best[0])
        types = sorted(canon)
        for D in types:
          for opts in OPTS:
            cls, nv, com = typed_formula(N, colors, list(D), **opts); base = f"/tmp/typed_selftest_{N}_{'_'.join(colors)}.cnf"
            for vs in sorted(canon[D]):        # completeness: the canonical colouring satisfies the typed formula
                units = [[eidx[e] * 2 + c] for e, c in zip(edges, vs)]
                write(base, cls + units, nv, com); rc = subprocess.run([CAD, '-q', base], capture_output=True).returncode; tested += 1
                if rc != 10: fails += 1; print('FAIL completeness', N, colors, D, vs, opts)
            write(base, cls, nv, com); p = subprocess.run([CAD, '-q', base], capture_output=True, text=True); tested += 1
            if p.returncode != 10: fails += 1; print('FAIL: typed formula UNSAT for occurring type', N, colors, D, opts)
            else:                                # soundness: the model is a good colouring of type D
                lits = set(int(x) for l in p.stdout.splitlines() if l.startswith('v') for x in l.split()[1:])
                col = {e: (2 if eidx[e] * 2 + 2 in lits else 1) for e in edges}
                deg = sorted(sum(1 for u in range(1, N + 1) if u != v and col[(min(u, v), max(u, v))] == 2) for v in range(1, N + 1))
                if not good(N, col, s, t, eidx) or tuple(deg) != D: fails += 1; print('FAIL soundness', N, colors, D, deg, opts)
        # non-occurring types must be UNSAT
        allD = set(itertools.combinations_with_replacement(range(N), N)) - set(types)
        for D in random.Random(1).sample(sorted(allD), min(12, len(allD))):
          for opts in OPTS:
            cls, nv, com = typed_formula(N, colors, list(D), **opts); write(base, cls, nv, com); tested += 1
            if subprocess.run([CAD, '-q', base], capture_output=True).returncode != 20: fails += 1; print('FAIL: non-occurring type SAT', N, colors, D, opts)
        print(f"N={N} {colors}: {len(types)} occurring types, {sum(len(v) for v in canon.values())} canonical good colourings checked")
    print(f"SELFTEST {'PASS' if fails == 0 else 'FAIL'}: {tested} SAT checks, {fails} failures")
    return fails == 0

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('N', type=int, nargs='?'); ap.add_argument('colors', nargs='?'); ap.add_argument('--type'); ap.add_argument('-o', '--out')
    ap.add_argument('--selftest', action='store_true'); ap.add_argument('--tight', action='store_true'); ap.add_argument('--budget', action='store_true')
    ap.add_argument('--allpairs', action='store_true'); ap.add_argument('--classcounts', action='store_true'); a = ap.parse_args()
    if a.selftest: sys.exit(0 if selftest() else 1)
    D = [int(x) for x in a.type.split(',')]; cls, nv, com = typed_formula(a.N, a.colors.split(','), D, tight=a.tight, budget=a.budget, allpairs=a.allpairs, classcounts=a.classcounts); write(a.out, cls, nv, com)
    print(f"{a.out}: {nv} vars, {len(cls)} clauses; {com[-2]}; {com[-1]}")
