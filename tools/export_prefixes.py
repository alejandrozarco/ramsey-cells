#!/usr/bin/env python3
"""export_prefixes.py BASE.cnf TOP.icnf close_DIR OUT.tsv [NEGCUBES.cnf]
Walk the closed cube tree on disk (top icnf + close_DIR/splits/<id>_d8.icnf) and write one row per
leaf: <id> TAB "p cnf NV NC+k|<lit> 0|...", the prefix format cert_pass.py reconstructs leaves from
(prefix ++ base body). A leaf is a cube id with a verified UNSAT ledger row and no split file."""
import json, os, sys
base, top, d, out = sys.argv[1:5]; neg = sys.argv[5] if len(sys.argv) > 5 else None
hdr = next(l for l in open(base) if l.startswith('p')).split(); nv, nc = int(hdr[2]), int(hdr[3])
rows = {}
for l in open(f'{d}/ledger.jsonl'):
    if l.strip(): r = json.loads(l); rows[str(r['id'])] = r
splits = {f[:-len('_d8.icnf')] for f in os.listdir(f'{d}/splits') if f.endswith('_d8.icnf')}
def cubes_of(path): return [l.split()[1:-1] for l in open(path) if l.startswith('a')]
leaves = []
def walk(cid, lits):
    if cid in splits:
        for j, c in enumerate(cubes_of(f'{d}/splits/{cid}_d8.icnf')): walk(f'{cid}.{j}', lits + c)
    else:
        r = rows.get(cid); assert r and r['result'] == 'UNSAT' and r.get('verified'), ('leaf without verified UNSAT row', cid)
        leaves.append((cid, lits))
for i, c in enumerate(cubes_of(top)): walk(str(i), c)
with open(out, 'w') as f:
    for cid, lits in leaves: f.write(f'{cid}\tp cnf {nv} {nc + len(lits)}|' + '|'.join(f'{x} 0' for x in lits) + '\n')
if neg:   # cover formula: every leaf cube negated; UNSAT <=> the leaves cover the whole space
    with open(neg, 'w') as f:
        f.write(f'p cnf {nv} {len(leaves)}\n')
        for cid, lits in leaves: f.write(' '.join(str(-int(x)) for x in lits) + ' 0\n')
print(f'{len(leaves)} leaves written to {out}; ledger rows {len(rows)}; splits {len(splits)}' + (f'; cover formula {neg}' if neg else ''))
