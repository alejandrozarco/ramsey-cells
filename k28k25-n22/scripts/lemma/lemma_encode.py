#!/usr/bin/env python3
"""Append PROVED consequences of the codegree bounds to a two-colour K_{2,s},K_{2,t} formula.

Families (all consequences of "blue codegree <= b, red codegree <= r", hence sound to add to ANY formula for
the cell, including one with static symmetry breaking; nothing here is a symmetry-breaking choice):
  F1  per vertex v: blue degree in [LO, HI]  (LO, HI must be JUSTIFIED separately - for K2x8,K2x5 at N=22 the
      window [8,10] is the degree lemma machine-checked by scripts/lemma/deg_lemma.py), with exact-degree
      indicators D[v][k] <-> "blue degree of v = k" from a bidirectional sequential counter.
  F2  per pair {i,j}: from the identity  c_red(i,j) = (N-2) - d_i - d_j + 2*A_ij + c_blue(i,j)
      (count the vertices w outside {i,j} joined to neither i nor j in blue), the caps
         c_blue(i,j) <= r - (N-2) + d_i + d_j - 2*A_ij   and   c_red(i,j) <= (N-2) - d_i - d_j + 2*A_ij + b,
      emitted only where strictly tighter than b resp. r, conditioned on the degree indicators and A_ij.
      Fresh upper indicators y_w >= blue(i,w) AND blue(j,w) (z_w for red) with forward-only counters; a
      conditional cap "<= q" is the clause  (not Cnd) OR (not S_{m,q+1}), which forbids q+1 true indicators
      under Cnd and never forces an indicator, so the family is sound (set the indicators to the exact ANDs).
  F3  class sizes (N=22, K2x8,K2x5 only, from the external analysis's Cauchy-Schwarz argument, itself
      reproduced by scripts/astra/task1.py): at most 7 vertices of blue degree 8, at most 10 of degree 10.
      Emitted only when --classes is given; off by default because it is the least independently checked.

Layout (gen_ramsey.py): vertices 1..N, edges row-major over pairs i<j from index 0, var(e,c) = eidx*2 + c,
colour 2 = blue, colour 1 = red. New variables are numbered from the base header's count + 1.

usage: lemma_encode.py BASE.cnf N LO HI OUT.cnf [--b 4 --r 7] [--classes]
       lemma_encode.py --check EDGELIST N LO HI [--b 4 --r 7]     semantic check of F1/F2 on a graph (0-based edges)
       lemma_encode.py --selftest                                    tiny-cell soundness test with CaDiCaL
"""
import itertools, os, subprocess, sys, tempfile

def edge_index(n):
    idx = {}; k = 0
    for i in range(1, n + 1):
        for j in range(i + 1, n + 1):
            idx[(i, j)] = k; k += 1
    return idx

class Enc:
    def __init__(self, nv): self.nv = nv; self.cls = []
    def new(self): self.nv += 1; return self.nv
    def add(self, c): self.cls.append(c)
    def bidir_counter(self, xs, kmax):
        """R[(i,j)] <-> at least j of xs[:i] are true, for 1<=i<=m, 1<=j<=min(i,kmax). Returns R."""
        m = len(xs); R = {}
        for i in range(1, m + 1):
            for j in range(1, min(i, kmax) + 1):
                R[(i, j)] = self.new()
        for i in range(1, m + 1):
            x = xs[i - 1]
            for j in range(1, min(i, kmax) + 1):
                prev_j = R.get((i - 1, j)); prev_jm1 = R.get((i - 1, j - 1)) if j > 1 else 'T'
                # forward: R(i-1,j) -> R(i,j);  x_i & R(i-1,j-1) -> R(i,j)
                if prev_j is not None: self.add([-prev_j, R[(i, j)]])
                if prev_jm1 == 'T': self.add([-x, R[(i, j)]])
                elif prev_jm1 is not None: self.add([-x, -prev_jm1, R[(i, j)]])
                # backward: R(i,j) -> R(i-1,j) or x_i ;  R(i,j) -> R(i-1,j) or R(i-1,j-1)
                c1 = [-R[(i, j)], x]; c2 = [-R[(i, j)]]
                if prev_j is not None: c1.append(prev_j); c2.append(prev_j)
                if prev_jm1 == 'T': c2 = None
                elif prev_jm1 is not None: c2.append(prev_jm1)
                else: pass  # R(i-1,j-1) is false (j-1 > i-1): R(i,j) -> R(i-1,j), already in c2
                self.add(c1)
                if c2 is not None: self.add(c2)
        return R
    def fwd_counter(self, ys, qmax):
        """S[(i,q)] is forced true when at least q of ys[:i] are true (one direction only). Returns S."""
        m = len(ys); S = {}
        for i in range(1, m + 1):
            for q in range(1, min(i, qmax) + 1):
                S[(i, q)] = self.new()
        for i in range(1, m + 1):
            y = ys[i - 1]
            for q in range(1, min(i, qmax) + 1):
                if (i - 1, q) in S: self.add([-S[(i - 1, q)], S[(i, q)]])
                if q == 1: self.add([-y, S[(i, 1)]])
                elif (i - 1, q - 1) in S: self.add([-y, -S[(i - 1, q - 1)], S[(i, q)]])
        return S

def caps(N, b, r, a, c, adj):
    """(blue_cap, red_cap) for degree pair (a,c) and adjacency adj in {0,1}; None if not tighter."""
    blue = r - (N - 2) + a + c - 2 * adj
    red = (N - 2) - a - c + 2 * adj + b
    return (blue if blue < b else None), (red if red < r else None)

def encode(base, N, LO, HI, out, b=4, r=7, classes=False):
    lines = open(base).read().splitlines()
    hdr = next(l for l in lines if l.startswith('p')).split(); V, C = int(hdr[2]), int(hdr[3])
    body = [l for l in lines if l and l[0] not in 'cp']
    eidx = edge_index(N); E = len(eidx)
    def var(i, j, c): return eidx[(min(i, j), max(i, j))] * 2 + c
    enc = Enc(V); counts = {}
    # F1
    D = {}
    for v in range(1, N + 1):
        xs = [var(v, u, 2) for u in range(1, N + 1) if u != v]
        R = enc.bidir_counter(xs, HI + 1)
        m = len(xs)
        if LO >= 1: enc.add([R[(m, LO)]])                        # at least LO
        if HI + 1 <= m: enc.add([-R[(m, HI + 1)]])                # not at least HI+1 (vacuous if HI = m)
        D[v] = {}
        for k in range(LO, HI + 1):
            d = enc.new(); D[v][k] = d
            ge_k = R.get((m, k)) if k >= 1 else 'T'                # R(m,0) is true
            ge_k1 = R.get((m, k + 1))                              # None = false (k+1 > m)
            # d <-> ge_k and not ge_k1
            if ge_k == 'T':
                if ge_k1 is None: enc.add([d])
                else: enc.add([-d, -ge_k1]); enc.add([d, ge_k1])
            else:
                enc.add([-d, ge_k])
                if ge_k1 is None: enc.add([d, -ge_k])
                else: enc.add([-d, -ge_k1]); enc.add([d, -ge_k, ge_k1])
    counts['F1'] = len(enc.cls)
    # F2
    n_caps = 0
    for i, j in itertools.combinations(range(1, N + 1), 2):
        ws = [w for w in range(1, N + 1) if w not in (i, j)]
        A = var(i, j, 2)
        need_blue = any(caps(N, b, r, a, c, adj)[0] is not None for a in range(LO, HI + 1) for c in range(LO, HI + 1) for adj in (0, 1))
        need_red = any(caps(N, b, r, a, c, adj)[1] is not None for a in range(LO, HI + 1) for c in range(LO, HI + 1) for adj in (0, 1))
        Sb = Sr = None
        if need_blue:
            ys = []
            for w in ws:
                y = enc.new(); ys.append(y); enc.add([-var(i, w, 2), -var(j, w, 2), y])
            Sb = enc.fwd_counter(ys, b)                       # need S(m, q+1) for q <= b-1
        if need_red:
            zs = []
            for w in ws:
                z = enc.new(); zs.append(z); enc.add([-var(i, w, 1), -var(j, w, 1), z])
            Sr = enc.fwd_counter(zs, r)
        m = len(ws)
        for a in range(LO, HI + 1):
            for c in range(LO, HI + 1):
                for adj in (0, 1):
                    cb, cr = caps(N, b, r, a, c, adj)
                    cond = [-D[i][a], -D[j][c], (-A if adj else A)]   # clause literals that are false when Cnd holds
                    if cb is not None:
                        if cb < 0: enc.add(cond)                        # the condition itself is impossible
                        else: enc.add(cond + [-Sb[(m, cb + 1)]]); n_caps += 1
                    if cr is not None:
                        if cr < 0: enc.add(cond)
                        else: enc.add(cond + [-Sr[(m, cr + 1)]]); n_caps += 1
    counts['F2'] = len(enc.cls) - counts['F1']; counts['F2_caps'] = n_caps
    # F3
    if classes:
        assert N == 22 and LO <= 8 and HI >= 10, "class-size bounds are specific to K2x8,K2x5 at N=22"
        for k, lim in ((8, 7), (10, 10)):
            xs = [D[v][k] for v in range(1, N + 1)]
            R = enc.bidir_counter(xs, lim + 1); enc.add([-R[(len(xs), lim + 1)]])
        counts['F3'] = len(enc.cls) - counts['F1'] - counts['F2']
    with open(out, 'w') as f:
        f.write(f"c lemma_encode: base {os.path.basename(base)} (V={V}, C={C}) + F1 degree window [{LO},{HI}] on {N} vertices"
                f" + F2 identity caps (b={b}, r={r}; {n_caps} conditional caps){' + F3 class sizes' if classes else ''}\n")
        f.write(f"c appended clauses by family: {counts}; new variables {enc.nv - V}\n")
        f.write(f"p cnf {enc.nv} {C + len(enc.cls)}\n")
        f.write("\n".join(body) + "\n")
        for cl in enc.cls: f.write(" ".join(map(str, cl)) + " 0\n")
    print(f"{out}: {enc.nv} vars ({enc.nv - V} new), {C + len(enc.cls)} clauses ({len(enc.cls)} appended) {counts}")

def check(edgelist, N, LO, HI, b=4, r=7):
    import ast
    g = ast.literal_eval(open(edgelist).read().strip().splitlines()[0]) if not edgelist.startswith('[') else ast.literal_eval(edgelist)
    adj = {v: set() for v in range(N)}
    for u, v in g: adj[u].add(v); adj[v].add(u)
    deg = {v: len(adj[v]) for v in range(N)}
    ok1 = all(LO <= deg[v] <= HI for v in range(N))
    ok2 = True; worst = None
    for i, j in itertools.combinations(range(N), 2):
        A = 1 if j in adj[i] else 0
        cb = len(adj[i] & adj[j]); cr = sum(1 for w in range(N) if w not in (i, j) and w not in adj[i] and w not in adj[j])
        ident = (N - 2) - deg[i] - deg[j] + 2 * A + cb
        if ident != cr: ok2 = False; worst = ('identity', i, j, ident, cr); break
        capb, capr = caps(N, b, r, deg[i], deg[j], A)
        if capb is not None and cb > capb: ok2 = False; worst = ('blue cap', i, j, cb, capb); break
        if capr is not None and cr > capr: ok2 = False; worst = ('red cap', i, j, cr, capr); break
        if cb > b or cr > r: ok2 = False; worst = ('base bound', i, j, cb, cr); break
    print(f"check N={N}: degrees {sorted(set(deg.values()))} F1[{LO},{HI}] {'PASS' if ok1 else 'FAIL'} | F2 identity+caps {'PASS' if ok2 else 'FAIL ' + str(worst)}")
    return ok1 and ok2

def selftest():
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
    import gen_ramsey as g
    CAD = os.environ.get('CADICAL', 'cadical')
    for cell, N, b, r in (('K2x2,K2x2', 5, 1, 1), ('K2x3,K2x2', 6, 1, 2), ('K2x3,K2x3', 9, 2, 2)):
        cls, nv, _ = g.build(N, cell.split(','), None, None, False)
        eidx = g.edge_index(N); E = len(eidx)
        t = tempfile.mkdtemp(); base = f"{t}/base.cnf"; aug = f"{t}/aug.cnf"
        with open(base, 'w') as f:
            f.write(f"p cnf {nv} {len(cls)}\n"); f.writelines(" ".join(map(str, c)) + " 0\n" for c in cls)
        encode(base, N, 0, N - 1, aug, b=b, r=r)
        # every good colouring (found by enumerating solutions of the base with CaDiCaL, blocking clauses) must
        # remain satisfiable in the augmented formula when its edge colours are fixed
        good = 0; kept = 0; blocked = []
        while True:
            with open(f"{t}/enum.cnf", 'w') as f:
                f.write(f"p cnf {nv} {len(cls) + len(blocked)}\n"); f.writelines(" ".join(map(str, c)) + " 0\n" for c in cls + blocked)
            rr = subprocess.run([CAD, '-q', f"{t}/enum.cnf"], capture_output=True, text=True)
            if rr.returncode != 10: break
            model = [int(x) for l in rr.stdout.splitlines() if l.startswith('v') for x in l.split()[1:] if int(x) != 0]
            edge_lits = [x for x in model if abs(x) <= 2 * E]
            good += 1; blocked.append([-x for x in edge_lits if x > 0])
            aug_lines = open(aug).read().splitlines(); h = next(l for l in aug_lines if l.startswith('p')).split()
            with open(f"{t}/fix.cnf", 'w') as f:
                f.write(f"p cnf {h[2]} {int(h[3]) + len(edge_lits)}\n"); f.write("\n".join(l for l in aug_lines if l and l[0] not in 'cp') + "\n")
                f.writelines(f"{x} 0\n" for x in edge_lits)
            r2 = subprocess.run([CAD, '-q', f"{t}/fix.cnf"], capture_output=True, text=True)
            kept += (r2.returncode == 10)
            if good >= 400: break
        print(f"selftest {cell} N={N}: good colourings enumerated {good}, still satisfiable under the appended clauses {kept} -> {'PASS' if good == kept else 'FAIL'}")

if __name__ == '__main__':
    a = sys.argv[1:]
    if a and a[0] == '--selftest': selftest()
    elif a and a[0] == '--check':
        opt = {'b': 4, 'r': 7}
        for k in ('b', 'r'):
            if f'--{k}' in a: opt[k] = int(a[a.index(f'--{k}') + 1])
        check(a[1], int(a[2]), int(a[3]), int(a[4]), **opt)
    else:
        opt = {'b': 4, 'r': 7, 'classes': '--classes' in a}
        for k in ('b', 'r'):
            if f'--{k}' in a: opt[k] = int(a[a.index(f'--{k}') + 1])
        encode(a[0], int(a[1]), int(a[2]), int(a[3]), a[4], **opt)
