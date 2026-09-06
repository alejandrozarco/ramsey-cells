#!/usr/bin/env python3
"""Empirical soundness test: on small cells, every variant must have the same SAT/UNSAT status as base,
and every model must decode to a valid colouring. Uses pysat's bundled CaDiCaL. Run at nice 19."""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_variant import generate
from gen_ramsey import edge_index
from pysat.solvers import Cadical153

def status(cls):
    with Cadical153(bootstrap_with=cls) as s:
        ok = s.solve(); return ok, (s.get_model() if ok else None)

from gen_ramsey import GRAPHS
def check_model(n, colors, model):
    r = len(colors); eidx = edge_index(n); pos = set(l for l in model if l > 0)
    col = {}
    for e, k in eidx.items():
        c = [c for c in range(1, r + 1) if (r * k + c) in pos]; assert len(c) == 1, e; col[e] = c[0]
    for c, g in enumerate(colors, 1):
        if 'x' in g:
            s, t = (int(x) for x in g[1:].split('x'))
            for S in itertools.combinations(range(1, n + 1), s):
                common = sum(1 for w in range(1, n + 1) if w not in S and all(col[tuple(sorted((v, w)))] == c for v in S))
                assert common < t, (g, S, common)
        else:
            k, ges = GRAPHS[g]
            for sub in itertools.combinations(range(1, n + 1), k):
                for perm in itertools.permutations(sub):
                    if all(col[tuple(sorted((perm[u], perm[v])))] == c for u, v in ges): raise AssertionError((g, sub))

cases = [(7, 'K2x2,K2x3', True), (8, 'K2x2,K2x3', False), (8, 'K2x2,K2x4', True), (9, 'K2x2,K2x4', False),
         (10, 'K2x2,K2x5', True), (11, 'K2x2,K2x5', False), (9, 'K2x3,K2x3', True), (10, 'K2x3,K2x3', False),
         (9, 'K2x4,K2x2', False), (10, 'K2x5,K2x2', True), (11, 'K2x3,K2x4', True)]
for n, cell, expect in cases:
    colors = cell.split(','); res = {}
    for variant in ('base', 'lex', 'DO', 'DOL', 'DOLI', 'N', 'NL', 'NLI'):
        cls, nv, com = generate(n, colors, variant)
        ok, model = status(cls); res[variant] = ok
        if ok: check_model(n, colors, model)
    line = ' '.join(f'{k}={"SAT" if v else "UNSAT"}' for k, v in res.items())
    flag = 'OK' if len(set(res.values())) == 1 else 'MISMATCH'; flag += '' if res['base'] == expect else ' (expectation table wrong, variants agree)'
    print(f'n={n:2d} {cell:12s} expect={"SAT" if expect else "UNSAT"}  {line}  {flag}', flush=True)
    if flag != 'OK': sys.exit(1)
print('all variants agree with base on all cases')
cases3 = [(10, 'C4,C4,C4', True), (11, 'C4,C4,C4', False), (6, 'K3,C4', True), (7, 'K3,C4', False), (9, 'K3,J4', True), (8, 'C4,C4,K3', True)]
for n, cell, expect in cases3:
    colors = cell.split(','); res = {}
    for variant in ('base', 'DO', 'DOL', 'DOS', 'DOLS'):
        if 'S' in variant and len({c for c in colors if colors.count(c) > 1}) == 0: continue
        cls, nv, com = generate(n, colors, variant)
        ok, model = status(cls); res[variant] = ok
        if ok: check_model(n, colors, model)
    line = ' '.join(f'{k}={"SAT" if v else "UNSAT"}' for k, v in res.items())
    flag = 'OK' if len(set(res.values())) == 1 else 'MISMATCH'
    print(f'n={n:2d} {cell:12s} expect={"SAT" if expect else "UNSAT"}  {line}  {flag}', flush=True)
    assert flag == 'OK'
print('three-colour and clique cases agree with base')
# fix-d1 union: for every case, OR over d of NLI+fix_d1(d) must equal base status
import re
for n, cell, expect in cases:
    colors = cell.split(','); base_ok, _ = status(generate(n, colors, 'base')[0])
    cls, nv, com = generate(n, colors, 'NLI'); bnd = [c for c in com if c.startswith('c I:')][0]
    lo, hi = map(int, re.search(r'(\d+) <= deg1\(1\) <= (\d+)', bnd).groups())
    any_sat = False
    for d in range(lo, hi + 1):
        ok, model = status(generate(n, colors, 'NLI', fix_d1=d)[0])
        if ok: check_model(n, colors, model); any_sat = True
    print(f'n={n:2d} {cell:12s} fix-d1 over [{lo},{hi}]: {"SAT" if any_sat else "UNSAT"} base={"SAT" if base_ok else "UNSAT"}', 'OK' if any_sat == base_ok else 'MISMATCH', flush=True)
    assert any_sat == base_ok
print('fix-d1 union agrees with base on all cases')
