#!/usr/bin/env python3
"""One-line (or per-class) grade report for the rooted census. Denominator = the generator's list files
H_*_r*_c*.txt (781 lists, 23,886 cubes), NEVER the ledgers, and never a loose H_*.txt glob: a leftover
duplicate H_0_22_0_astra47.txt inflated that by 47 on 2026-09-10 (CLAUDE.md rule 1).
Grades: 3 = cake_lpr VERIFIED, 2 = lrat-trim + lrat-check, 1 = rc 20 only.  usage: census_grades.py [--by-class]"""
import collections, glob, json, os, sys
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'runs', 'k28_rooted')
ALIAS = {'0_22_0_root9_astra47_2M': '0_22_0_r9_c090', '0_22_0_root9_astra47_PROOF': '0_22_0_r9_c090',
         '0_22_0_astra47': '0_22_0_r9_c090'}

def cubes(path):
    s = set()
    for l in open(path):
        l = l.split('#')[0].strip()
        if l: s.add(tuple(sorted(tuple(int(x) for x in e.split('-')) for e in l.split(','))))
    return s

own = {os.path.basename(f)[2:-4]: cubes(f) for f in sorted(glob.glob(f'{D}/H_*_r*_c*.txt'))}
best = {}
for fl in glob.glob(f'{D}/ledger_*.jsonl'):
    tag = os.path.basename(fl)[7:-6]; tag = ALIAS.get(tag, tag)
    if tag not in own: continue
    for l in open(fl):
        try: r = json.loads(l)
        except Exception: continue
        if r.get('rc') != 20: continue
        k = tuple(sorted(tuple(e) for e in r['H']))
        if k not in own[tag]: continue                     # a decided row must belong to its own list
        g = 3 if r.get('cake_verified') else (2 if r.get('verified') else 1)
        best[(tag, k)] = max(best.get((tag, k), 0), g)
listed = sum(len(v) for v in own.values()); gr = collections.Counter(best.values())
mon = set(json.load(open(f'{D}/monster_lists.json')))
if '--by-class' in sys.argv:
    per = collections.defaultdict(lambda: [0, 0, 0])
    for t, s in own.items(): per[int(t.split('_')[0])][0] += len(s)
    for (t, k), g in best.items():
        a = int(t.split('_')[0]); per[a][1] += 1; per[a][2] += (g == 3)
    print(f"{'a':>3s} {'cubes':>7s} {'decided':>8s} {'%':>6s} {'cake':>7s}")
    for a, (tot, dec, ck) in sorted(per.items()):
        print(f"{a:3d} {tot:7d} {dec:8d} {100*dec/tot:5.1f}% {ck:7d}")
print(f"census {len(best)}/{listed} decided ({100*len(best)/listed:.1f}%) | cake {gr[3]} lrat {gr[2]} rc20 {gr[1]} | "
      f"remaining {listed - len(best)} | monster lists {len(mon)} = {sum(len(own[t]) for t in own if t in mon)} cubes | "
      f"{len(own)} lists")
