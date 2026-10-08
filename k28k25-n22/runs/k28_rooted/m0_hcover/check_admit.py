#!/usr/bin/python3
"""M0 over-restriction check: for every blocked class word C of a family, the cover CNF WITHOUT blockers
(degree caps + window + all LL(p)) must be satisfiable with x fixed to C. A failure would mean the base/LL
encoding wrongly excludes a canonical graph (soundness bug). Uses the perms recorded in cert_<tag>.json.
usage: check_admit.py TAG [TAG ...] | --all"""
import glob, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import cnfgen
from pysat.solvers import Solver

tags = sys.argv[1:]
if tags == ['--all']:
    tags = sorted(os.path.basename(d) for d in glob.glob(os.path.join(HERE, 'data', 'k*')) if os.path.isdir(d))
tot = bad = 0
for tag in tags:
    c = json.load(open(os.path.join(HERE, 'data', tag, f'cert_{tag}.json')))
    k, comp = c['family']['k'], tuple(c['family']['comp'])
    b = cnfgen.Builder(k, comp)
    s = Solver(name='cadical195')
    for cl in b.base: s.add_clause(cl)
    for p in c['perms']:
        for cl in b.ll_clauses(tuple(p)): s.add_clause(cl)
    nb = 0
    for blk in c['blockers']:
        w = blk['word']
        ok = s.solve(assumptions=[(n + 1) if ch == '1' else -(n + 1) for n, ch in enumerate(w)])
        if not ok:
            nb += 1; print(f'  {tag}: class {w} ({blk["kind"]}) EXCLUDED by base+LL', flush=True)
    s.delete()
    tot += len(c['blockers']); bad += nb
    print(f'{tag}: {len(c["blockers"])} classes, {nb} excluded by base+LL', flush=True)
print(f'TOTAL {tot} classes checked, {bad} excluded')
