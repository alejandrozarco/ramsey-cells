#!/usr/bin/env python3
"""make_bench.py OUTDIR : generate the benchmark bundle (CNFs + manifest.json).
Instance set: two-colour K_{2,t}/K_{3,t} refutations at n = R (survey values), three-colour cells, the open targets.
Variants: lex (deposited), base, DO, DOL, DOL2, DOL-rev, DOL-tot, DOL-bi, DOL-c4direct (C4 sides), DOPL (3 colours), DO-swap (colours swapped)."""
import sys, os, json, hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_variant import generate
out = sys.argv[1]; os.makedirs(out, exist_ok=True)
SMALL = [('k23k24_n12', 12, 'K2x3,K2x4'), ('k24k24_n14', 14, 'K2x4,K2x4'), ('k25k23_n13', 13, 'K2x5,K2x3'), ('k25k24_n16', 16, 'K2x5,K2x4'),
         ('k25k25_n18', 18, 'K2x5,K2x5'), ('k26k24_n17', 17, 'K2x6,K2x4'), ('k26k25_n20', 20, 'K2x6,K2x5'),
         ('k33k24_n16', 16, 'K3x3,K2x4'), ('k33k25_n18', 18, 'K3x3,K2x5'), ('k33k33_n18', 18, 'K3x3,K3x3'),
         ('k3k3k3_n17', 17, 'K3,K3,K3'), ('c4c4c4_n11', 11, 'C4,C4,C4'), ('k3c4c4_n12', 12, 'K3,C4,C4'), ('k3k3c4_n12', 12, 'K3,K3,C4')]
LARGE = [('k28k25_n22', 22, 'K2x8,K2x5'), ('c4c4k4_n20', 20, 'C4,C4,K4'), ('k3j4j4_n21', 21, 'K3,J4,J4'), ('k35k25_n22', 22, 'K3x5,K2x5')]
def variants(colors):
    v = [('lex', 'lex', {}), ('base', 'base', {}), ('DO', 'DO', {}), ('DOL', 'DOL', {}), ('DOL2', 'DOL2', {}), ('DOLrev', 'DOL', {'lexorder': 'rev'}),
         ('DOLtot', 'DOL', {'enc': 'tot'}), ('DOLbi', 'DOL', {'enc': 'bi'})]
    if any(c == 'C4' or c == 'K2x2' for c in colors): v.append(('DOLc4d', 'DOL', {'enc': 'c4direct'}))
    if len(colors) >= 3: v += [('DOPL', 'DOPL', {}), ('DOPL2', 'DOPL2', {})]
    return v
manifest = []
def emit(iid, n, cell, large):
    colors = cell.split(',')
    for name, var, kw in variants(colors):
        cls, nv, com = generate(n, colors, var, **kw); path = f'{out}/{iid}_{name}.cnf'
        with open(path, 'w') as f:
            for c in com: f.write(c + '\n')
            f.write(f'c bench {iid} variant {name}\np cnf {nv} {len(cls)}\n')
            for c in cls: f.write(' '.join(map(str, c)) + ' 0\n')
        manifest.append({'id': f'{iid}_{name}', 'cnf': os.path.basename(path), 'march': ['-d', '10'], 'single': not large, 'cell': cell, 'n': n, 'large': large})
    if not large and colors[0] != colors[-1]:   # swapped colour order for the strongest variant
        sw = colors[::-1]; cls, nv, com = generate(n, sw, 'DOL'); path = f'{out}/{iid}_DOLswap.cnf'
        with open(path, 'w') as f:
            for c in com: f.write(c + '\n')
            f.write(f'c bench {iid} variant DOLswap\np cnf {nv} {len(cls)}\n')
            for c in cls: f.write(' '.join(map(str, c)) + ' 0\n')
        manifest.append({'id': f'{iid}_DOLswap', 'cnf': os.path.basename(path), 'march': ['-d', '10'], 'single': True, 'cell': ','.join(sw), 'n': n, 'large': False})
    print(iid, 'done', flush=True)
for iid, n, cell in SMALL: emit(iid, n, cell, False)
for iid, n, cell in LARGE: emit(iid, n, cell, True)
# cubing-config arms on the deposited breaking and on DOL for two mid-size cells
for iid in ('k25k25_n18', 'k33k33_n18', 'k26k25_n20'):
    for name in ('lex', 'DOL'):
        for tag, args in (('d8', ['-d', '8']), ('d12', ['-d', '12']), ('dyn', ['-e', '0.4', '-f', '0.03']), ('nogah', ['-d', '10', '-gah'])):
            manifest.append({'id': f'{iid}_{name}_m{tag}', 'cnf': f'{iid}_{name}.cnf', 'march': args, 'single': False, 'cell': '', 'n': 0, 'large': False})
json.dump(manifest, open(f'{out}/manifest.json', 'w'), indent=0)
print('manifest items', len(manifest))
