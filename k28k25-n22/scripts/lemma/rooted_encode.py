#!/usr/bin/env python3
"""Rooted census formulas for two-colour codegree cells (written 2026-09-09 ~06:20 UTC for K2x8,K2x5 at N=22, after
Astra round 3: the neighbour-first canonical form).

Setting. Histogram = the multiset of blue degrees (for the 2003 cell: 8^a 9^b 10^c). Root degree k (present in the
histogram) and a COMPOSITION (n_8, n_9, n_10) of N(1): how many neighbours of the root have each degree. Cells in
vertex order: {1}, N_8, N_9, N_10 (the root's neighbours, degree-sorted), W_8, W_9, W_10 (the non-neighbours,
degree-sorted); H = G[N(1)].
Canonical form (Astra round 3, PROVED): among the labellings of a good graph with root of degree k and this cell
structure, minimise the pair (word(H), valseq(G)) lexicographically, word(H) = the colour values of the edges
inside N(1) in valseq order, minimised over the degree-coloured group Gamma_N = prod S_{|N_d|}; then valseq(G)
over the residual group Gamma_H = Aut_deg(H) x prod S_{|W_d|}. Consequences used here:
  - row 1 = blue on N(1), red on W (units);
  - exact degrees per vertex (cells fix them);
  - COVER MODE (H free): word(H) <=lex word(H o s) for adjacent transpositions s inside each N cell (necessary for
    the Gamma_N-min of word(H)); blocking clauses for already-listed H; SAT -> a new admissible H, UNSAT -> the
    list covers every canonical H (LRAT-checkable);
  - CUBE MODE (H fixed by units): valseq(G) <=lex valseq(G o s) for adjacent transpositions s inside each W cell
    (elements of Gamma_H); no transposition inside N(1) unless it is an automorphism of H (not added here).
  - counting families from typed_encode.add_counting (exact degrees, tightened identity intervals, exact deficit
    sums (B)) - invariant properties of good graphs, sound in any labelling.
Cover argument: a good graph with this histogram has a vertex of degree k; root it there; its neighbours realise
some composition; the canonical form for that composition has an H in the (complete) list; so the union over
compositions and listed H of the cube formulas is satisfiable iff a good graph with the histogram exists.
usage:
  rooted_encode.py N K2xs,K2xt --hist a,b,c --root k --comp n8,n9,n10 [--budget] --cube 'i-j,i-j,...' -o out.cnf
  rooted_encode.py N K2xs,K2xt --hist a,b,c --root k --comp n8,n9,n10 [--budget] --cover LISTFILE -o out.cnf
  rooted_encode.py --selftest
Edge lists name vertices by their position in the cell order (2..k+1 are the neighbours). For the 2003 cell degrees
are 8,9,10; for the selftest cells the histogram is given as the sorted degree sequence via --degs.
"""
import argparse, itertools, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.abspath(os.path.join(HERE, '..', '..'))); sys.path.insert(0, HERE)
from gen_ramsey import build, edge_index
from lemma_encode import Enc
from typed_encode import add_counting, budget_of, bounds
CAD = os.environ.get('CADICAL', 'cadical')

def lex_leq(enc, pairs, var, r=2):
    """valseq restricted to the given (edge, image) pairs, in order: value(e) <= value(f) lexicographically, with an
    equality chain; same encoding as gen_ramsey.build's vertex-lex (colour values 1 < 2 < ... < r)."""
    eqch = None
    for t, (e, f) in enumerate(pairs):
        prem = [] if eqch is None else [-eqch]
        for cf in range(1, r + 1):
            for ce in range(cf + 1, r + 1): enc.add(prem + [-var(e, ce), -var(f, cf)])
        if t == len(pairs) - 1: break
        q = enc.new()
        for c in range(1, r + 1): enc.add([-q, -var(e, c), var(f, c)]); enc.add([q, -var(e, c), -var(f, c)])
        newch = enc.new()
        if eqch is None: enc.add([-newch, q]); enc.add([newch, -q])
        else: enc.add([-newch, eqch]); enc.add([-newch, q]); enc.add([newch, -eqch, -q])
        eqch = newch

def moved_pairs(edges, s):
    """(e, f) for edges e moved by the transposition s = (va, vb), in the given edge order."""
    va, vb = s
    def sig(x): return vb if x == va else (va if x == vb else x)
    out = []
    for e in edges:
        f = tuple(sorted((sig(e[0]), sig(e[1]))))
        if f != e: out.append((e, f))
    return out

def cells_of(N, degs_sorted, k, comp):
    """degs_sorted: the histogram as a sorted list of degree values (the distinct values in increasing order matter);
    comp: dict degree -> count among the neighbours. Returns (D list per vertex 1..N, ncells, wcells) with cells as
    (lo, hi, degree)."""
    vals = sorted(set(degs_sorted)); count = {d: degs_sorted.count(d) for d in vals}
    assert count.get(k, 0) >= 1, 'root degree not present'
    rest = dict(count); rest[k] -= 1
    for d, c in comp.items(): assert rest.get(d, 0) >= c, f'composition needs {c} neighbours of degree {d}, only {rest.get(d,0)} available'
    assert sum(comp.values()) == k, 'composition must sum to the root degree'
    D = [k]; ncells = []; wcells = []; pos = 2
    for d in vals:
        c = comp.get(d, 0)
        if c: ncells.append((pos, pos + c - 1, d)); D += [d] * c; pos += c
    for d in vals:
        c = rest[d] - comp.get(d, 0)
        if c: wcells.append((pos, pos + c - 1, d)); D += [d] * c; pos += c
    assert len(D) == N
    return D, ncells, wcells


def pair_shortfall(enc, N, b, r, D, var, k, Hs, wcells):
    """Corollary 4.3 (PROVED in LEMMAS_draft): the TOTAL blue-codegree shortfall over pairs inside the
    root's neighbourhood is at most sigma, a number fixed by H alone.

    Write X for the N-by-W blue incidence, s_ij = U_ij - C_ij for i,j in N. Then (4.7) gives s_ij >= 0,
    and C_ij = 1 + q_ij + (X^T X)_ij, so s_ij = k_ij - (X^T X)_ij with k_ij = U_ij - 1 - q_ij. Summing
    and applying the convexity bound of (4.8),

        sum_{i<j in N} s_ij  =  sum k_ij - sum_w C(z_w, 2)  <=  sum k_ij - (m*C(q,2) + rho*q)  =  sigma,

    with T_N = sum_{i in N}(D_i - 1 - h_i) = m*q + rho and m = |W|.

    WHY THIS IS WORTH A CLAUSE. Resolution cannot perform a quadratic double count, so CDCL cannot
    derive this however long it runs; it instead explores X-assignments whose total shortfall is far
    above sigma, each of which is globally impossible, and refutes them one at a time through the
    W-side of the formula. Measured 2026-09-16 on 526 cubes: the capped fraction runs 0% -> 7% ->
    43% -> 68% -> 87-100% as (F, sigma) worsens, monotonically and independently of |H|.

    WHAT IS EMITTED. s_ij >= v is exactly ~Ry[(i,j)][(M, U_ij - v + 1)], since Ry[(i,j)][(M,t)] <-> C_ij >= t.
    Collecting v = 1..max(sigma,1) over all pairs and asserting that at most sigma of those indicators
    hold encodes sum_ij min(s_ij, sigma) <= sigma, which is IMPLIED by the corollary because
    min(s,sigma) <= s. It is therefore a weakening of a proved statement: sound, and strictly weaker
    than the lemma itself.

    Returns a provenance dict. Adds no variables or clauses when sigma is large enough to be vacuous.
    """
    M = N - 2
    S = list(range(2, k + 2))
    W = [v for (lo, hi, d) in wcells for v in range(lo, hi + 1)]
    h = {u: sum(1 for e in Hs if u in e) for u in S}
    sumk = 0
    caps = {}
    for i, j in itertools.combinations(S, 2):
        A = 1 if (min(i, j), max(i, j)) in Hs else 0
        bh = bounds(N, b, r, D[i - 1], D[j - 1], A)[1]
        q_ij = sum(1 for u in S if u not in (i, j)
                   and (min(i, u), max(i, u)) in Hs and (min(j, u), max(j, u)) in Hs)
        caps[(i, j)] = bh
        sumk += bh - 1 - q_ij
    T = sum(D[i - 1] - 1 - h[i] for i in S)
    m = len(W)
    q, rho = divmod(T, m)
    sigma_raw = sumk - (m * q * (q - 1) // 2 + rho * q)
    # sigma < 0 means the corollary already refutes this H. Do NOT emit the empty clause on that: a
    # disagreement with the generator's filter is a bug signal before it is a refutation, and the
    # generator deliberately uses a WEAKER cap on some red pairs (Proposition 4.1). Clamp to 0, which
    # asserts the strictly weaker "every pair is exactly at its cap" and is implied by sigma < 0.
    sigma = max(sigma_raw, 0)
    lits = []
    for i, j in itertools.combinations(S, 2):
        bh = caps[(i, j)]
        for t in range(max(1, bh - max(sigma, 1) + 1), bh + 1):
            lits.append(-enc.Ry[(i, j)][(M, t)])
    n0 = len(enc.cls)
    # Emit only when the bound can bite. bidir_counter builds R[(i,j)] for j <= min(i, kmax), so
    # R[(len(lits), sigma+1)] does not exist when len(lits) <= sigma -- and in exactly that case the
    # constraint is vacuous anyway, since fewer than sigma+1 indicators cannot exceed sigma. Asking
    # for the missing key raised KeyError(1, 2) on the first small-cell selftest.
    if len(lits) > sigma:
        Rsf = enc.bidir_counter(lits, sigma + 1)
        enc.add([-Rsf[(len(lits), sigma + 1)]])
    return dict(sigma=sigma, sigma_raw=sigma_raw, sumk=sumk, T=T, m=m, q=q, rho=rho,
                lits=len(lits), clauses=len(enc.cls) - n0)

def rooted_formula(N, colors, degs_sorted, k, comp, H=None, cover=None, tight=True, budget=False, channel=False, wallpairs=False, auth=False, base_codegree=True, shortfall=False):
    """H: iterable of (i,j) blue edges inside N(1) (cube mode). cover: list of H edge-sets to block (cover mode)."""
    s = int(colors[0].split('x')[1]); t = int(colors[1].split('x')[1]); r = s - 1; b = t - 1
    D, ncells, wcells = cells_of(N, degs_sorted, k, comp)
    if base_codegree:
        cls, nv, com = build(N, colors)                # base only, no lex
    else:
        # Astra round 24 A1: gen_ramsey.build's codegree machinery (upper indicators + one-directional counters) is
        # duplicated by add_counting's exact indicators and bidirectional counters, which impose the same caps through
        # their conditional intervals. Dropping it removes ~42% of the variables. SAFE, BUT NOT BY PURE DELETION:
        # the reduced formula is NOT the full one minus clauses with numbering preserved: dropping the base layer also SHIFTS every subsequent auxiliary by 57,519 (round 27, item 3, which ruled the pure-deletion claim WRONG).
        # Edge variables keep their numbering; auxiliaries do not.
        # The UNSAT implication still holds, but via the uniform substitution phi mapping each reduced auxiliary v to v+57519 with signs preserved, under which phi(F_reduced) is a subset of F_full -- so UNSAT of the reduced formula implies UNSAT of the full one.
        # See LEMMAS_draft.md line ~1248.
        # Edge variables alone keep var(e,c) = eidx[e]*r + c.
        _eidx0 = edge_index(N); _r = len(colors); nv = len(_eidx0) * _r; cls = []
        for e in _eidx0:
            cls.append([_eidx0[e] * _r + c for c in range(1, _r + 1)])
            for c1 in range(1, _r + 1):
                for c2 in range(c1 + 1, _r + 1):
                    cls.append([-(_eidx0[e] * _r + c1), -(_eidx0[e] * _r + c2)])
        com = [f"c R({','.join(colors)}) at n={N}: SAT iff R > n",
               f"c {len(_eidx0)} edges x {_r} colors = {nv} edge vars",
               "c BASE CODEGREE OMITTED (duplicated by add_counting); a refutation of this weaker formula refutes the full one"]
    eidx = edge_index(N); edges = sorted(eidx, key=lambda e: eidx[e])
    def var(i, j, c=None):
        if c is None: i, j, c = i[0], i[1], j        # var(edge, colour)
        return eidx[(min(i, j), max(i, j))] * 2 + c
    enc = Enc(nv)
    nb = set(range(2, k + 2))
    for u in range(2, N + 1): enc.add([var(1, u, 2 if u in nb else 1)])          # row 1
    counts = add_counting(enc, N, b, r, D, var, tight=tight, budget=budget, channel=channel)
    hedges = [e for e in edges if e[0] in nb and e[1] in nb]
    if H is not None:                                  # cube mode
        Hs = set(tuple(sorted(e)) for e in H)
        for e in hedges: enc.add([var(e, 2 if e in Hs else 1)])
        for (lo, hi, d) in wcells:
            for v in range(lo, hi):
                lex_leq(enc, moved_pairs(edges, (v, v + 1)), var)
        if wallpairs:      # every transposition (p q) inside a W cell as the exact 20-position comparison D_p <= D_q (Astra round 7 §4)
            for (lo, hi, d) in wcells:
                for p_ in range(lo, hi + 1):
                    for q_ in range(p_ + 1, hi + 1):
                        pairs = [((min(p_, x), max(p_, x)), (min(q_, x), max(q_, x))) for x in range(1, N + 1) if x not in (p_, q_)]
                        lex_leq(enc, pairs, var)
        nauts = 0
        if auth:           # valseq comparisons against every non-identity degree-preserving automorphism of H, identity on W (sound)
            cells = [list(range(lo, hi + 1)) for (lo, hi, d) in ncells]
            for parts in itertools.product(*[itertools.permutations(c) for c in cells]):
                pi = {}
                for c, part in zip(cells, parts):
                    for src, dst in zip(c, part): pi[src] = dst
                if all(pi[v] == v for v in pi): continue
                if any(tuple(sorted((pi[i], pi[j]))) not in Hs for (i, j) in Hs): continue
                img = lambda e: tuple(sorted((pi.get(e[0], e[0]), pi.get(e[1], e[1]))))
                pairs = [(e, img(e)) for e in edges if img(e) != e]
                if pairs: lex_leq(enc, pairs, var); nauts += 1
        sf = pair_shortfall(enc, N, b, r, D, var, k, Hs, wcells) if shortfall else None
        mode = f'cube H={sorted(Hs)} W-lex adjacent in {wcells}; wallpairs={wallpairs} auth={auth} ({nauts} automorphisms) channel={channel}{"; shortfall=" + str(sf) if sf else ""}'
    else:
        raise ValueError('cover mode is local_cover_formula')
    com += [f"c rooted_encode: root degree {k}, composition {comp}, cells N {ncells} W {wcells}; D={D}",
            f"c {mode}; counting {counts}; tight={tight} budget={budget}; {enc.nv - nv} new vars"]
    return cls + enc.cls, enc.nv, com, hedges, D

def local_cover_formula(N, colors, degs_sorted, k, comp, cover=None, tight=True, rowmin=False, hdeg=None):
    """The LOCAL admissibility formula on H = G[N(1)] and X = the N(1)-W incidence: only constraints whose variables
    avoid Y = G[W] (so a SAT answer is an admissible H, not a full graph). Necessary conditions for a good graph:
      row 1 fixed; exact blue degree of every neighbour (root + H + X column); blue/red codegree caps for pairs inside
      N(1) (root counts as a blue common neighbour; caps from the tightened intervals given the degrees and H_ij);
      C_{1w} = row_w(X) within its interval for every non-neighbour w; (X X^T)_wz <= blue cap for w,z in W (ignoring
      Y); (X H)_wi <= blue cap for w in W, i in N(1) (ignoring Y); the H-word lex for adjacent transpositions inside
      each N cell (necessary for the Gamma_N-min word); blocking clauses for the listed H.
    Enumerating H by blocking until UNSAT gives a complete list of the H-words that pass these conditions; every
    canonical H of a good graph with this root/composition is among them."""
    s_ = int(colors[0].split('x')[1]); t_ = int(colors[1].split('x')[1]); r = s_ - 1; b = t_ - 1
    D, ncells, wcells = cells_of(N, degs_sorted, k, comp)
    eidx = edge_index(N); edges = sorted(eidx, key=lambda e: eidx[e]); E = len(eidx)
    def var(i, j, c=None):
        if c is None: i, j, c = i[0], i[1], j
        return eidx[(min(i, j), max(i, j))] * 2 + c
    enc = Enc(E * 2)
    for e in edges: enc.add([var(e, 1), var(e, 2)]); enc.add([-var(e, 1), -var(e, 2)])     # exactly one colour
    nb = list(range(2, k + 2)); W = list(range(k + 2, N + 1))
    for u in range(2, N + 1): enc.add([var(1, u, 2 if u in nb else 1)])
    Lam = {v: budget_of(N, b, r, D[v - 1]) for v in range(1, N + 1)}
    def caps(i, j, A):        # (blue_hi, red_hi, blue_lo, red_lo) for the pair given degrees and blue adjacency A
        from typed_encode import bounds
        bl, bh, rl, rh = bounds(N, b, r, D[i - 1], D[j - 1], A)
        if tight:
            lam = min(Lam[i], Lam[j]); L = (N - 2) - D[i - 1] - D[j - 1] + 2 * A
            if A == 1: rl = max(rl, r - lam)
            else: bl = max(bl, b - lam)
            bl = max(bl, rl - L); rl = max(rl, bl + L); bh = min(bh, rh - L); rh = min(rh, bh + L)
        return bl, bh, rl, rh
    def at_most(xs, cap, cond=None):
        """sum xs <= cap, optionally only when literal cond is true (cond given as the literal that is FALSE when the
        condition holds, i.e. the clause literal)."""
        if cap >= len(xs): return
        if cap < 0: enc.add([cond] if cond is not None else []); return
        R = enc.bidir_counter(xs, cap + 1); enc.add(([cond] if cond is not None else []) + [-R[(len(xs), cap + 1)]])
    def at_least(xs, lo, cond=None):
        if lo <= 0: return
        if lo > len(xs): enc.add([cond] if cond is not None else []); return
        R = enc.bidir_counter(xs, lo); enc.add(([cond] if cond is not None else []) + [R[(len(xs), lo)]])
    def conj(a_, b_):
        y = enc.new(); enc.add([-a_, -b_, y]); enc.add([-y, a_]); enc.add([-y, b_]); return y
    for i in nb:                                                   # exact degree of each neighbour (all its edges are local)
        xs = [var(i, u, 2) for u in range(1, N + 1) if u != i]; d = D[i - 1]
        R = enc.bidir_counter(xs, min(len(xs), d + 1))
        if d >= 1: enc.add([R[(len(xs), d)]])
        if d + 1 <= len(xs): enc.add([-R[(len(xs), d + 1)]])
    for i in nb:                                                   # pairs (1,i), blue: C_{1i} = h_i (i's H-neighbours), R_{1i} = |W| - col_i(X)
        bl, bh, rl, rh = caps(1, i, 1)
        hv = [var(i, j, 2) for j in nb if j != i]; at_most(hv, bh); at_least(hv, bl)
        col = [var(w, i, 2) for w in W]; at_most(col, len(W) - rl); at_least(col, len(W) - rh)
    for i, j in itertools.combinations(nb, 2):                     # pairs inside N(1): all common neighbours are local
        A = var(i, j, 2)
        blue = [conj(var(i, u, 2), var(j, u, 2)) for u in range(2, N + 1) if u not in (i, j)]       # root adds 1
        red = [conj(var(i, u, 1), var(j, u, 1)) for u in range(2, N + 1) if u not in (i, j)]        # root is blue to both
        for a_ in (0, 1):
            bl, bh, rl, rh = caps(i, j, a_); cond = -A if a_ == 1 else A
            at_most(blue, bh - 1, cond); at_least(blue, bl - 1, cond); at_most(red, rh, cond); at_least(red, rl, cond)
    for w in W:                                                    # C_{1w} = row_w(X); (1,w) is red
        bl, bh, rl, rh = caps(1, w, 0); row = [var(w, i, 2) for i in nb]
        at_most(row, bh); at_least(row, bl)
    for w, z in itertools.combinations(W, 2):                      # (X X^T)_wz <= blue cap (Y ignored: necessary only)
        A = var(w, z, 2); xs = [conj(var(w, i, 2), var(z, i, 2)) for i in nb]
        for a_ in (0, 1):
            bl, bh, rl, rh = caps(w, z, a_); at_most(xs, bh, -A if a_ == 1 else A)
    for w in W:                                                    # (X H)_wi <= blue cap (Y ignored)
        for i in nb:
            A = var(w, i, 2); xs = [conj(var(w, j, 2), var(i, j, 2)) for j in nb if j != i]
            for a_ in (0, 1):
                bl, bh, rl, rh = caps(w, i, a_); at_most(xs, bh, -A if a_ == 1 else A)
    hedges = [e for e in edges if e[0] in nb and e[1] in nb]
    for (lo, hi, d) in ncells:
        for v in range(lo, hi): lex_leq(enc, moved_pairs(hedges, (v, v + 1)), var)
    if rowmin or hdeg is not None:
        Hdeg = {}
        for u in nb:
            xs = [var(u, j, 2) for j in nb if j != u]; Hdeg[u] = (enc.bidir_counter(xs, len(xs)), len(xs))
    if rowmin:           # the first vertex of the (single) N cell has minimal H-degree (lex-min word: row 1 minimal). With several
        # N cells the lex order prioritises the earlier cell segments and does NOT minimise the total H-degree (Astra round 5
        # counter-example, N=7): unsound there, hence the assertion.
        assert len(ncells) == 1, 'rowmin is only sound with a single N cell'
        lo, hi, d = ncells[0]
        for u in range(lo + 1, hi + 1):
            R2, m2 = Hdeg[lo]; Ru, mu = Hdeg[u]
            for l in range(1, m2 + 1): enc.add([-R2[(m2, l)], Ru[(mu, l)]])      # h_lo >= l -> h_u >= l
    if hdeg is not None:  # hdeg: dict vertex -> exact H-degree (a split case)
        for u, h in hdeg.items():
            R, m = Hdeg[u]
            if h >= 1: enc.add([R[(m, h)]])
            if h + 1 <= m: enc.add([-R[(m, h + 1)]])
    for Hs in (cover or []):
        Hs = set(tuple(sorted(e)) for e in Hs); enc.add([var(e, 1 if e in Hs else 2) for e in hedges])
    com = [f"c rooted_encode LOCAL cover formula: root degree {k}, composition {comp}, cells N {ncells} W {wcells}; D={D}",
           f"c {len(cover or [])} blocked H; {enc.nv - 2 * E} aux vars"]
    return enc.cls, enc.nv, com, hedges, D

def write(path, cls, nv, com):
    with open(path, 'w') as f:
        f.write('\n'.join(com) + '\n'); f.write(f"p cnf {nv} {len(cls)}\n")
        for c in cls: f.write(' '.join(map(str, c)) + ' 0\n')

def solve(cls, nv, com, path, limit=None):
    write(path, cls, nv, com)
    args = [CAD, '-q'] + (['-c', str(limit)] if limit else []) + [path]
    p = subprocess.run(args, capture_output=True, text=True)
    lits = set(int(x) for l in p.stdout.splitlines() if l.startswith('v') for x in l.split()[1:]) if p.returncode == 10 else None
    return p.returncode, lits

def enumerate_cover(N, colors, degs_sorted, k, comp, tmp, budget=False, limit=None, log=print, found=None):
    """Cover mode loop: returns the list of H (edge sets) found until UNSAT (complete), and the final rc. The local
    formula is built once; only the blocking clauses change per iteration. `found` seeds the list (resume)."""
    found = list(found or [])
    base, nv, com, hedges, D = local_cover_formula(N, colors, degs_sorted, k, comp, cover=None)
    eidx = edge_index(N)
    def var(e, c): return eidx[e] * 2 + c
    while True:
        block = [[var(e, 1 if e in Hs else 2) for e in hedges] for Hs in found]
        rc, lits = solve(base + block, nv, com + [f"c {len(found)} blocked H"], tmp, limit)
        if rc != 10: return found, rc
        Hs = frozenset(e for e in hedges if var(e, 2) in lits)
        assert Hs not in found; found.append(Hs); log(f'  H #{len(found)}: {len(Hs)} edges {sorted(Hs)}')

def selftest():
    """Brute force on tiny cells: for every good colouring, root at its FIRST vertex of the chosen degree k (the
    minimum degree present), compute the canonical form (min (word(H), valseq)) over all rooted degree-sorted
    labellings, and check (1) the cube formula for that H is satisfied by the canonical colouring (completeness),
    (2) every cube model is a good colouring with the right cells (soundness), (3) the cover enumeration returns a
    list containing every canonical H (and each listed H satisfies the adjacent H-word lex by construction)."""
    fails = 0; tested = 0
    for (N, colors) in ((5, ['K2x2', 'K2x3']), (6, ['K2x2', 'K2x3']), (6, ['K2x3', 'K2x3'])):
        s = int(colors[0][3:]); t = int(colors[1][3:]); eidx = edge_index(N); edges = sorted(eidx, key=lambda e: eidx[e])
        def good(col):
            for i, j in itertools.combinations(range(1, N + 1), 2):
                cb = sum(1 for w in range(1, N + 1) if w not in (i, j) and col[(min(i, w), max(i, w))] == 2 and col[(min(j, w), max(j, w))] == 2)
                cr = sum(1 for w in range(1, N + 1) if w not in (i, j) and col[(min(i, w), max(i, w))] == 1 and col[(min(j, w), max(j, w))] == 1)
                if cb > t - 1 or cr > s - 1: return False
            return True
        def relabel(col, perm):      # perm: new label -> old label
            return {(i, j): col[(min(perm[i], perm[j]), max(perm[i], perm[j]))] for i, j in itertools.combinations(range(1, N + 1), 2)}
        canon = {}                   # (degs, k, comp) -> {H: set of canonical valseqs}
        for bits in itertools.product((1, 2), repeat=len(edges)):
            col = dict(zip(edges, bits))
            if not good(col): continue
            deg = {v: sum(1 for u in range(1, N + 1) if u != v and col[(min(u, v), max(u, v))] == 2) for v in range(1, N + 1)}
            degs = tuple(sorted(deg.values())); k = degs[0]
            best = None
            for root in [v for v in range(1, N + 1) if deg[v] == k]:
                nbrs = [u for u in range(1, N + 1) if u != root and col[(min(u, root), max(u, root))] == 2]
                others = [u for u in range(1, N + 1) if u != root and u not in nbrs]
                comp = {}
                for u in nbrs: comp[deg[u]] = comp.get(deg[u], 0) + 1
                D, ncells, wcells = cells_of(N, list(degs), k, comp)
                # slots per cell: vertices with the right degree, neighbours in N cells, others in W cells
                slots = [(lo, hi, [u for u in nbrs if deg[u] == d]) for (lo, hi, d) in ncells] + [(lo, hi, [u for u in others if deg[u] == d]) for (lo, hi, d) in wcells]
                for perms in itertools.product(*[itertools.permutations(us) for (_, _, us) in slots]):
                    perm = {1: root}
                    for (lo, hi, us), p in zip(slots, perms):
                        for pos, u in zip(range(lo, hi + 1), p): perm[pos] = u
                    c2 = relabel(col, perm)
                    hword = tuple(c2[e] for e in edges if 2 <= e[0] <= k + 1 and 2 <= e[1] <= k + 1)
                    key = (hword, tuple(c2[e] for e in edges))
                    if best is None or key < best[0]: best = (key, c2, tuple(sorted(comp.items())))
            (hword, vs), c2, compt = best
            H = frozenset(e for e in edges if 2 <= e[0] <= k + 1 and 2 <= e[1] <= k + 1 and c2[e] == 2)
            canon.setdefault((degs, k, compt), {}).setdefault(H, set()).add(vs)
        tmp = f"/tmp/rooted_selftest_{N}.cnf"
        for (degs, k, compt), byH in sorted(canon.items()):
            comp = dict(compt)
            for H, vss in byH.items():
              # shortfall=True is in the option set deliberately: the selftest is a COMPLETENESS
              # check -- every good colouring must satisfy the cube formula for its canonical H --
              # so an unsound added constraint shows up here as a failure. N=5,6 with (b,r) other
              # than (4,7) also exercises Corollary 4.3 away from the production cell's numbers.
              for opts in (dict(budget=True), dict(budget=True, channel=True, wallpairs=True, auth=True),
                           dict(budget=True, channel=True, wallpairs=True, auth=True, shortfall=True)):
                  cls, nv, com, hedges, D = rooted_formula(N, colors, list(degs), k, comp, H=H, **opts)
                  for vs in vss:                                   # completeness
                      units = [[eidx[e] * 2 + c] for e, c in zip(edges, vs)]
                      rc, _ = solve(cls + units, nv, com, tmp); tested += 1
                      if rc != 10: fails += 1; print('FAIL completeness', N, colors, degs, k, comp, sorted(H))
                  rc, lits = solve(cls, nv, com, tmp); tested += 1        # soundness of a model
                  if rc != 10: fails += 1; print('FAIL cube UNSAT for occurring H', N, colors, degs, k, comp, sorted(H))
                  else:
                      col = {e: (2 if eidx[e] * 2 + 2 in lits else 1) for e in edges}
                      dv = [sum(1 for u in range(1, N + 1) if u != v and col[(min(u, v), max(u, v))] == 2) for v in range(1, N + 1)]
                      if not good(col) or dv != D: fails += 1; print('FAIL soundness', N, colors, degs, k, comp, dv, D)
            found, rc = enumerate_cover(N, colors, list(degs), k, comp, tmp, budget=True, log=lambda *a: None); tested += 1
            missing = [H for H in byH if H not in found]
            if rc != 20 or missing: fails += 1; print('FAIL cover', N, colors, degs, k, comp, 'rc', rc, 'missing', [sorted(H) for H in missing], 'found', len(found))
        print(f"N={N} {colors}: {len(canon)} (histogram, root, composition) cases, {sum(len(v) for v in canon.values())} canonical H, {sum(len(vs) for v in canon.values() for vs in v.values())} canonical colourings")
    print(f"SELFTEST {'PASS' if fails == 0 else 'FAIL'}: {tested} checks, {fails} failures")
    return fails == 0

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('N', type=int, nargs='?'); ap.add_argument('colors', nargs='?')
    ap.add_argument('--hist', help='a,b,c for degrees 8,9,10'); ap.add_argument('--degs', help='explicit sorted degree list (alternative to --hist)')
    ap.add_argument('--root', type=int); ap.add_argument('--comp', help='n8,n9,n10 (with --hist) or d:count,... (with --degs)')
    ap.add_argument('--cube', help='H edge list i-j,i-j,... (vertices 2..k+1)'); ap.add_argument('--cover', help='file with one H edge list per line to block (may be empty/nonexistent)')
    ap.add_argument('--enumerate', action='store_true', help='cover loop: enumerate all H until UNSAT, append to --cover file')
    ap.add_argument('--budget', action='store_true'); ap.add_argument('--limit', type=int); ap.add_argument('-o', '--out', default='/tmp/rooted.cnf')
    ap.add_argument('--selftest', action='store_true'); a = ap.parse_args()
    if a.selftest: sys.exit(0 if selftest() else 1)
    if a.hist:
        h = [int(x) for x in a.hist.split(',')]; degs = [8] * h[0] + [9] * h[1] + [10] * h[2]
        c = [int(x) for x in a.comp.split(',')]; comp = {8: c[0], 9: c[1], 10: c[2]}
    else:
        degs = sorted(int(x) for x in a.degs.split(',')); comp = {int(p.split(':')[0]): int(p.split(':')[1]) for p in a.comp.split(',')}
    comp = {d: c for d, c in comp.items() if c}
    def parse_H(line): return [tuple(int(x) for x in e.split('-')) for e in line.strip().split(',') if e.strip()]
    if a.enumerate:
        found = []
        if a.cover and os.path.exists(a.cover):
            found = [frozenset(tuple(sorted(e)) for e in parse_H(l)) for l in open(a.cover) if l.strip()]
        found, rc = enumerate_cover(a.N, a.colors.split(','), degs, a.root, comp, a.out, budget=a.budget, limit=a.limit, found=found)
        with open(a.cover, 'w') as f:
            for H in found: f.write(','.join(f'{i}-{j}' for i, j in sorted(H)) + '\n')
        print(f"COVER {'COMPLETE (UNSAT)' if rc == 20 else 'INCOMPLETE rc ' + str(rc)}: {len(found)} H in {a.cover}")
    elif a.cube:
        cls, nv, com, hedges, D = rooted_formula(a.N, a.colors.split(','), degs, a.root, comp, H=parse_H(a.cube), budget=a.budget); write(a.out, cls, nv, com); print(f"{a.out}: {nv} vars, {len(cls)} clauses")
    else:
        cover = [parse_H(l) for l in open(a.cover)] if a.cover and os.path.exists(a.cover) else []
        cls, nv, com, hedges, D = local_cover_formula(a.N, a.colors.split(','), degs, a.root, comp, cover=cover); write(a.out, cls, nv, com); print(f"{a.out}: {nv} vars, {len(cls)} clauses (local cover formula, {len(cover)} blocked)")
