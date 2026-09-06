#!/usr/bin/env python3
"""
gen_variant.py -- stronger, provably sound formulas for two-colour K_{2,t1} vs K_{2,t2} cells.

Starts from gen_ramsey.build (codegree encoding, NO vertex-lex) and adds, by variant:
  D   per-vertex colour-1 degree unaries   o[v][k] <-> deg1(v) >= k   (bidirectional sequential counter)
  O   degree ordering                      deg1(1) >= deg1(2) >= ... >= deg1(n)
  L   conditional vertex-lex               (deg1(v) == deg1(v+1)) -> valseq(x) <=lex valseq(x o (v v+1))
  I   implied bounds (theorems about every colouring, derivations in SOUNDNESS.md):
        window on the number of colour-1 edges (Jensen on the two codegree sums),
        bounds on deg1(1) (the maximum) and deg1(n) (the minimum),
        per-vertex bounds relative to deg1(1) and deg1(n) from the pair codegree constraints.
  --variant base | lex | DO | DOL | DOLI      ('lex' reproduces gen_ramsey --vertex-lex exactly)
Soundness of D+O+L: any colouring has a relabelling with non-increasing colour-1 degrees; among
those take the lex-min value sequence; swapping two adjacent equal-degree vertices stays in that
set, so every single-transposition constraint holds at the minimum. I adds only implied facts.
"""
import argparse, itertools, math, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
from gen_ramsey import build, edge_index, copies  # the deposited encoder (same file as ramsey-cells/tools/gen_ramsey.py)

def build_base(n, colors, enc='sinz'):
    """Base encoding with a selectable codegree encoding. enc='sinz' reproduces gen_ramsey.build(n, colors)
    clause for clause (asserted by test_variants.py). 'tot': pysat totalizer instead of the Sinz counter.
    'bi': bidirectional indicators y <-> AND (plus Sinz). 'c4direct': K_{2,2} sides by direct 4-clauses
    (every pair of vertices and every pair of candidate common neighbours), other sides as 'sinz'."""
    r = len(colors); eidx = edge_index(n); E = len(eidx)
    def var(e, c): return eidx[e] * r + c
    nvars = E * r; cls = []
    comments = [f"c R({','.join(colors)}) at n={n}: SAT iff R > n", f"c {E} edges x {r} colors = {E*r} edge vars"]
    for e in eidx:
        cls.append([var(e, c) for c in range(1, r + 1)])
        for c1, c2 in itertools.combinations(range(1, r + 1), 2): cls.append([-var(e, c1), -var(e, c2)])
    for c, g in enumerate(colors, start=1):
        if "x" in g and g.startswith("K"):
            s_, t = (int(x) for x in g[1:].split("x")); k = t - 1; nsets = 0
            if enc == 'c4direct' and (s_, t) == (2, 2):
                for S in itertools.combinations(range(1, n + 1), 2):
                    nsets += 1; others = [w for w in range(1, n + 1) if w not in S]
                    for w, x in itertools.combinations(others, 2):
                        cls.append([-var(tuple(sorted((v, y))), c) for v in S for y in (w, x)])
                comments.append(f"c color {c} forbids {g} (direct 4-clauses): {nsets} 2-sets"); continue
            for S in itertools.combinations(range(1, n + 1), s_):
                nsets += 1; ys = []
                for w in range(1, n + 1):
                    if w in S: continue
                    nvars += 1; y = nvars
                    cls.append([-var(tuple(sorted((v, w))), c) for v in S] + [y])
                    if enc == 'bi':
                        for v in S: cls.append([-y, var(tuple(sorted((v, w))), c)])
                    ys.append(y)
                m = len(ys); assert m > k
                if enc == 'tot':
                    from pysat.card import CardEnc, EncType
                    e_ = CardEnc.atmost(lits=ys, bound=k, top_id=nvars, encoding=EncType.totalizer)
                    cls += e_.clauses; nvars = max(nvars, e_.nv); continue
                R = {}
                for i in range(1, m):
                    for j in range(1, k + 1): nvars += 1; R[(i, j)] = nvars
                cls.append([-ys[0], R[(1, 1)]])
                for i in range(2, m):
                    cls.append([-ys[i - 1], R[(i, 1)]])
                    for j in range(1, k + 1): cls.append([-R[(i - 1, j)], R[(i, j)]])
                    for j in range(2, k + 1): cls.append([-ys[i - 1], -R[(i - 1, j - 1)], R[(i, j)]])
                for i in range(2, m + 1): cls.append([-ys[i - 1], -R[(i - 1, k)]])
            comments.append(f"c color {c} forbids {g} (codegree, {enc}): {nsets} {s_}-sets, <= {k} common nbrs each"); continue
        cps = copies(n, g); comments.append(f"c color {c} forbids {g}: {len(cps)} copies")
        for es in cps: cls.append([-var(e, c) for e in sorted(es)])
    return cls, nvars, comments

def C2(x): return x * (x - 1) / 2.0

def parse_cell(colors):
    ks = []
    for g in colors:
        assert g.startswith('K') and 'x' in g, 'variants need K_{s,t} on both sides'
        s, t = (int(x) for x in g[1:].split('x'))
        assert s == 2, 'implied bounds are derived for s = 2 only'
        ks.append(t - 1)                      # codegree bound: <= t-1 common neighbours
    assert len(ks) == 2
    return ks

class Gen:
    def __init__(self, n, colors, enc='sinz', lexorder='fwd'):
        self.n = n; self.m = n - 1; self.colors = colors; self.r = len(colors); self.lexorder = lexorder
        self.cls, self.nvars, self.comments = build_base(n, colors, enc)
        self.eidx = edge_index(n)
        self.o = {}                           # o[v][k]  (colour-1 degree unaries)
        self.o2 = {}                          # colour-2 degree unaries (pair ordering)
        self.eq = {}; self.eq2 = {}

    def var(self, e, c): return self.eidx[e] * self.r + c
    def new(self):
        self.nvars += 1; return self.nvars

    def degree_unaries(self, colour=1, into=None):
        n, m = self.n, self.m
        if into is None: into = self.o
        for v in range(1, n + 1):
            xs = [self.var(tuple(sorted((v, w))), colour) for w in range(1, n + 1) if w != v]
            s = {}                            # s[(i,j)] <-> sum_{t<=i} xs[t] >= j ; s[(i,j)] false for j>i
            for i in range(1, m + 1):
                for j in range(1, i + 1):
                    s[(i, j)] = self.new()
            add = self.cls.append
            for i in range(1, m + 1):
                x = xs[i - 1]
                for j in range(1, i + 1):
                    sij = s[(i, j)]
                    prev_j = s.get((i - 1, j))          # None means false
                    prev_j1 = s.get((i - 1, j - 1)) if j - 1 >= 1 else True   # True means the constant true
                    # ->: s_ij -> prev_j or x ;  s_ij -> prev_j or prev_{j-1}
                    add([-sij] + ([prev_j] if prev_j else []) + [x])
                    if prev_j1 is not True:
                        add([-sij] + ([prev_j] if prev_j else []) + [prev_j1])
                    # <-: prev_j -> s_ij ;  x and prev_{j-1} -> s_ij
                    if prev_j: add([-prev_j, sij])
                    if prev_j1 is True: add([-x, sij])
                    else: add([-x, -prev_j1, sij])
            into[v] = {k: s[(m, k)] for k in range(1, m + 1)}
        self.comments.append(f'c D: colour-{colour} degree unaries, {n} vertices x {m*(m+1)//2} counter vars')

    def ordering(self):
        for v in range(1, self.n):
            for k in range(1, self.m + 1):
                self.cls.append([-self.o[v + 1][k], self.o[v][k]])
        self.comments.append('c O: deg1(1) >= deg1(2) >= ... >= deg1(n)')

    def eq_var(self, v, o, store):
        """store[v] <-> (degree(v) == degree(v+1)) in the unaries o; forced true when equal."""
        m = self.m; eq = self.new(); diffs = []
        for k in range(1, m + 1):
            d = self.new(); diffs.append(d)
            self.cls.append([-d, o[v][k]]); self.cls.append([-d, -o[v + 1][k]])
        self.cls.append([eq] + diffs); store[v] = eq; return eq, 1 + m

    def lex_transposition(self, a, b, prem_lits):
        """valseq(x) <=lex valseq(x o (a b)) under the premise literals; returns aux count."""
        edges_in_order = sorted(self.eidx, key=lambda e: self.eidx[e])
        if self.lexorder == 'rev': edges_in_order = edges_in_order[::-1]
        sig = lambda x: b if x == a else (a if x == b else x)
        moved = []
        for e in edges_in_order:
            f = tuple(sorted((sig(e[0]), sig(e[1]))))
            if f != e: moved.append((e, f))
        eqch = None; naux = 0
        for t, (e, f) in enumerate(moved):
            prem = list(prem_lits) + ([] if eqch is None else [-eqch])
            for cf in range(1, self.r + 1):
                for ce in range(cf + 1, self.r + 1):
                    self.cls.append(prem + [-self.var(e, ce), -self.var(f, cf)])
            if t == len(moved) - 1: break
            q = self.new(); naux += 1
            for c in range(1, self.r + 1):
                self.cls.append([-q, -self.var(e, c), self.var(f, c)])
                self.cls.append([q, -self.var(e, c), -self.var(f, c)])
            newch = self.new(); naux += 1
            if eqch is None: self.cls += [[-newch, q], [newch, -q]]
            else: self.cls += [[-newch, eqch], [-newch, q], [newch, -eqch, -q]]
            eqch = newch
        return naux

    def conditional_lex(self, vs=None, extra=None, dist2=False):
        n, m = self.n, self.m
        naux = 0
        vs = list(vs if vs is not None else range(1, n))
        for v in vs:
            eq, k_ = self.eq_var(v, self.o, self.eq); naux += k_
            prem = [-eq] + (extra(v) if extra else []) + ([-self.eq2[v]] if v in self.eq2 else [])
            naux += self.lex_transposition(v, v + 1, prem)
        if dist2:
            for v in vs:
                if v + 1 in self.eq and v + 2 <= n:
                    prem = [-self.eq[v], -self.eq[v + 1]] + (extra(v) + extra(v + 1) if extra else [])
                    naux += self.lex_transposition(v, v + 2, prem)
        self.comments.append(f'c L: conditional vertex-lex on {len(vs)} adjacent transpositions' + (' + distance-2' if dist2 else '') + f', {naux} aux vars, order {self.lexorder}')

    def pair_ordering(self):
        """P: order vertices by (deg1, deg2) lexicographically; needs O already applied to deg1."""
        n, m = self.n, self.m
        self.degree_unaries(colour=2, into=self.o2)
        for v in range(1, n):
            eq1, _ = self.eq_var(v, self.o, self.eq) if v not in self.eq else (self.eq[v], 0)
            for k in range(1, m + 1): self.cls.append([-eq1, -self.o2[v + 1][k], self.o2[v][k]])
            self.eq_var(v, self.o2, self.eq2)
        self.comments.append('c P: (deg1, deg2) lexicographic ordering')

    def _old_conditional_lex_unused(self, vs=None, extra=None):
        n, m = self.n, self.m
        edges_in_order = sorted(self.eidx, key=lambda e: self.eidx[e])
        naux = 0
        for v in (vs if vs is not None else range(1, n)):
            eq = self.new(); naux += 1
            diffs = []
            for k in range(1, m + 1):
                d = self.new(); naux += 1; diffs.append(d)
                self.cls.append([-d, self.o[v][k]]); self.cls.append([-d, -self.o[v + 1][k]])
            self.cls.append([eq] + diffs)     # equal degrees (no witness of difference) -> eq
            sig = lambda x: v + 1 if x == v else (v if x == v + 1 else x)
            moved = []
            for e in edges_in_order:
                f = tuple(sorted((sig(e[0]), sig(e[1]))))
                if f != e: moved.append((e, f))
            eqch = None
            for t, (e, f) in enumerate(moved):
                prem = [-eq] + (extra(v) if extra else []) + ([] if eqch is None else [-eqch])
                for cf in range(1, self.r + 1):
                    for ce in range(cf + 1, self.r + 1):
                        self.cls.append(prem + [-self.var(e, ce), -self.var(f, cf)])
                if t == len(moved) - 1: break
                q = self.new(); naux += 1
                for c in range(1, self.r + 1):
                    self.cls.append([-q, -self.var(e, c), self.var(f, c)])
                    self.cls.append([q, -self.var(e, c), -self.var(f, c)])
                newch = self.new(); naux += 1
                if eqch is None: self.cls += [[-newch, q], [newch, -q]]
                else: self.cls += [[-newch, eqch], [-newch, q], [newch, -eqch, -q]]
                eqch = newch
        self.comments.append(f'c L: conditional vertex-lex on {len(list(vs)) if vs is not None else n-1} adjacent transpositions, {naux} aux vars')

    def nbhd_first(self):
        """N: vertex 1 has maximum red degree, N_red(1) = {2..d_1+1}, and each of the two blocks
        {2..d_1+1}, {d_1+2..n} is sorted by non-increasing red degree. Sound: pick a max-degree vertex,
        relabel its red neighbours first, sort within blocks. same[u] <-> (u, u+1 have equal colour to 1)."""
        n, m = self.n, self.m; o = self.o; R = lambda j: self.var((1, j), 1)
        for j in range(3, n + 1): self.cls.append([-R(j), R(j - 1)])            # row 1 monotone
        for u in range(2, n + 1):
            for k in range(1, m + 1): self.cls.append([-o[u][k], o[1][k]])       # d_u <= d_1
        self.same = {}
        for u in range(2, n):
            sm = self.new(); self.same[u] = sm
            self.cls.append([sm, R(u), R(u + 1)]); self.cls.append([sm, -R(u), -R(u + 1)])   # same block -> sm
            for k in range(1, m + 1):
                self.cls.append([-sm, -o[u + 1][k], o[u][k]])                     # same block -> ordered
        self.comments.append('c N: deg1(1) maximal, N_red(1) = {2..d_1+1}, blocks sorted by degree')

    def count_swap(self, c1, c2):
        """S: for identical forbidden graphs in colours c1, c2 require #edges(c1) >= #edges(c2).
        Sound: swap the two colours if needed; edge counts are label-invariant, so this commutes with D/O/N."""
        assert self.colors[c1 - 1] == self.colors[c2 - 1]
        from pysat.card import CardEnc, EncType
        P = len(self.eidx); a = [self.var(e, c1) for e in self.eidx]; b = [self.var(e, c2) for e in self.eidx]
        # sum(a) >= sum(b)  <=>  sum(a) + sum(~b) >= P
        enc = CardEnc.atleast(lits=a + [-x for x in b], bound=P, top_id=self.nvars, encoding=EncType.seqcounter)
        self.cls += enc.clauses; self.nvars = max(self.nvars, enc.nv)
        self.comments.append(f'c S: #edges(colour {c1}) >= #edges(colour {c2})')

    def fix_d1(self, D):
        R = lambda j: self.var((1, j), 1)
        for j in range(2, D + 2): self.cls.append([R(j)])
        if D + 2 <= self.n: self.cls.append([-R(D + 2)])
        self.comments.append(f'c fix-d1: deg1(1) = {D}')

    def implied(self, k1, k2, minside=True):
        n, m = self.n, self.m
        P = n * (n - 1) // 2
        K1, K2 = k1 * P, k2 * P             # sum_v C(d_v,2) <= K1 ; sum_v C(m-d_v,2) <= K2
        E_hi = max(E for E in range(P + 1) if n * C2(2 * E / n) <= K1)
        E_lo = min(E for E in range(P + 1) if n * C2(2 * (P - E) / n) <= K2)
        # max degree D feasible?  others: d_u <= min(D, k1 + n - D)  =>  blue sum >= (n-1)*C(m - that, 2)
        def max_ok(D):
            cap = min(D, k1 + n - D)
            return cap >= 0 and (n - 1) * C2(m - cap) + C2(m - D) <= K2
        def min_ok(D):
            flo = max(D, 2 * m - k2 - n - D)
            return flo <= m and (n - 1) * C2(flo) + C2(D) <= K1
        Dmax = max(D for D in range(m + 1) if max_ok(D))
        Dmin = min(D for D in range(m + 1) if min_ok(D))
        d1_lo = math.ceil(2 * E_lo / n); dn_hi = math.floor(2 * E_hi / n)
        o = self.o
        if Dmax + 1 <= m: self.cls.append([-o[1][Dmax + 1]])
        if d1_lo >= 1: self.cls.append([o[1][d1_lo]])
        if minside and dn_hi + 1 <= m: self.cls.append([-o[n][dn_hi + 1]])
        if minside and Dmin >= 1: self.cls.append([o[n][Dmin]])
        rel = 0
        for u in range(2, n + 1):               # d_1 >= k  ->  d_u <= k1 + n - k
            for k in range(1, m + 1):
                j = k1 + n - k + 1
                if 1 <= j <= m: self.cls.append([-o[1][k], -o[u][j]]); rel += 1
        for u in (range(1, n) if minside else []):   # d_n <= k-1  ->  d_u >= 2m - k2 - n - (k-1)
            for k in range(1, m + 1):
                j = 2 * m - k2 - n - (k - 1)
                if 1 <= j <= m: self.cls.append([o[n][k], o[u][j]]); rel += 1
        from pysat.card import CardEnc, EncType
        lits = [self.var(e, 1) for e in self.eidx]
        for bound, kind in ((E_lo, 'atleast'), (E_hi, 'atmost')):
            enc = (CardEnc.atleast if kind == 'atleast' else CardEnc.atmost)(lits=lits, bound=bound, top_id=self.nvars, encoding=EncType.seqcounter)
            self.cls += enc.clauses; self.nvars = max(self.nvars, enc.nv)
        self.comments.append(f'c I: colour-1 edges in [{E_lo},{E_hi}], {d1_lo} <= deg1(1) <= {Dmax}' + (f', {Dmin} <= deg1(n) <= {dn_hi}' if minside else ' (min-side bounds off)') + f', {rel} relative-bound clauses')
        return dict(E_lo=E_lo, E_hi=E_hi, d1_lo=d1_lo, Dmax=Dmax, Dmin=Dmin, dn_hi=dn_hi)

def generate_lexDB(n, colors):
    """Deposited vertex-lex (all adjacent transpositions, unconditional) + degree unaries + the implied
    degree window applied to every vertex (theorems: every vertex has Dmin <= deg <= Dmax; no ordering,
    so the lex-leader argument of the deposited encoder is untouched). Sound: lex-leader + definitional
    counters + implied units."""
    cls, nv, com = build(n, colors, None, None, True)
    g = Gen(n, colors); g.cls, g.nvars, g.comments = list(cls), nv, list(com)
    g.degree_unaries()
    k1, k2 = parse_cell(colors); m = n - 1; P = n * (n - 1) // 2; K1, K2 = k1 * P, k2 * P
    def max_ok(D): cap = min(D, k1 + n - D); return cap >= 0 and (n - 1) * C2(m - cap) + C2(m - D) <= K2
    def min_ok(D): flo = max(D, 2 * m - k2 - n - D); return flo <= m and (n - 1) * C2(flo) + C2(D) <= K1
    Dmax = max(D for D in range(m + 1) if max_ok(D)); Dmin = min(D for D in range(m + 1) if min_ok(D))
    for v in range(1, n + 1):
        if Dmax + 1 <= m: g.cls.append([-g.o[v][Dmax + 1]])
        if Dmin >= 1: g.cls.append([g.o[v][Dmin]])
    g.comments.append(f'c lexDB: deposited lex + degree unaries + {Dmin} <= deg(v) <= {Dmax} for every v')
    return g.cls, g.nvars, g.comments

def generate(n, colors, variant, fix_d1=None, enc='sinz', lexorder='fwd'):
    """variant letters: D degree unaries, O ordering, L conditional lex, 2 distance-2 transpositions,
    P (deg1,deg2) pair ordering (3+ colours), N neighbourhood-first, I implied bounds, S edge-count swap.
    'lex' = deposited gen_ramsey --vertex-lex; 'base' = no breaking. enc: sinz|tot|bi|c4direct."""
    if variant == 'lex':
        cls, nv, com = build(n, colors, None, None, True); return cls, nv, com
    if variant == 'lexDB': return generate_lexDB(n, colors)
    g = Gen(n, colors, enc=enc, lexorder=lexorder)
    if variant == 'base': return g.cls, g.nvars, g.comments
    k1, k2 = parse_cell(colors) if 'I' in variant else (None, None)
    g.degree_unaries()
    if 'N' in variant:
        g.nbhd_first()
        if 'L' in variant: g.conditional_lex(vs=range(2, n), extra=lambda u: [-g.same[u]])
        if 'I' in variant: g.implied(k1, k2, minside=False)
    else:
        if 'O' in variant: g.ordering()
        if 'P' in variant: g.pair_ordering()
        if 'L' in variant: g.conditional_lex(dist2=('2' in variant))
        if 'I' in variant: g.implied(k1, k2)
    if 'S' in variant:
        same = [(i, j) for i in range(1, g.r + 1) for j in range(i + 1, g.r + 1) if colors[i - 1] == colors[j - 1]]
        for c1, c2 in same[:1]: g.count_swap(c1, c2)
    if fix_d1 is not None: g.fix_d1(fix_d1)
    return g.cls, g.nvars, g.comments

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('n', type=int); ap.add_argument('colors'); ap.add_argument('--variant', default='DOL'); ap.add_argument('--fix-d1', type=int); ap.add_argument('--enc', default='sinz'); ap.add_argument('--lexorder', default='fwd')
    ap.add_argument('-o', '--out', default='/dev/stdout')
    a = ap.parse_args()
    cls, nv, com = generate(a.n, a.colors.split(','), a.variant, a.fix_d1, a.enc, a.lexorder)
    with open(a.out, 'w') as f:
        for c in com: f.write(c + '\n')
        f.write(f'c variant {a.variant} enc {a.enc} lexorder {a.lexorder}\np cnf {nv} {len(cls)}\n')
        for c in cls: f.write(' '.join(map(str, c)) + ' 0\n')
    print(f'wrote {a.out}: variant {a.variant}, {nv} vars, {len(cls)} clauses', file=sys.stderr)

if __name__ == '__main__': main()
