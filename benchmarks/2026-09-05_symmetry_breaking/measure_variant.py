#!/usr/bin/env python3
"""measure_variant.py CNF TAG [--depth 10] [--sample 40] [--cap 120] [--par 5] [--seed 1]
Cube CNF with march_cu at a static depth, sample cubes uniformly, solve each with cadical -t CAP
(no proof), write TAG.sample.jsonl and a one-line summary comparable with the closer ledger:
  N cubes, solved fraction at CAP, mean of min(secs,CAP), N*mean = level-0 core-seconds estimate."""
import argparse, json, os, random, subprocess, time, statistics as st
from concurrent.futures import ThreadPoolExecutor
MARCH = os.path.expanduser('~/sat/CnC/march_cu/march_cu'); CAD = os.path.expanduser('~/sat/cadical/build/cadical')
ap = argparse.ArgumentParser(); ap.add_argument('cnf'); ap.add_argument('tag')
ap.add_argument('--depth', type=int, default=10); ap.add_argument('--sample', type=int, default=40)
ap.add_argument('--cap', type=int, default=120); ap.add_argument('--par', type=int, default=5); ap.add_argument('--seed', type=int, default=1)
a = ap.parse_args()
icnf = f'{a.tag}_d{a.depth}.icnf'
t0 = time.time()
if not os.path.exists(icnf):
    subprocess.run([MARCH, a.cnf, '-d', str(a.depth), '-o', icnf], stdout=open(f'{a.tag}_march.log', 'w'), stderr=subprocess.STDOUT)
tcube = time.time() - t0
cubes = [l.split()[1:-1] for l in open(icnf) if l.startswith('a')]
hdr = None; body = []
for l in open(a.cnf):
    if l.startswith('c'): continue
    if l.startswith('p'): hdr = l.split(); continue
    body.append(l)
nv, nc = int(hdr[2]), int(hdr[3]); body = ''.join(body)
random.seed(a.seed); idx = sorted(random.sample(range(len(cubes)), min(a.sample, len(cubes))))
def one(i):
    f = f'{a.tag}_cube{i}.cnf'
    with open(f, 'w') as h:
        h.write(f'p cnf {nv} {nc + len(cubes[i])}\n'); h.write(''.join(f'{x} 0\n' for x in cubes[i])); h.write(body)
    t = time.time(); r = subprocess.run([CAD, '-q', '-t', str(a.cap), f], capture_output=True, text=True); secs = time.time() - t
    os.remove(f)
    res = 'UNSAT' if 's UNSATISFIABLE' in r.stdout else 'SAT' if 's SATISFIABLE' in r.stdout else 'CAP'
    return {'cube': i, 'result': res, 'secs': round(secs, 1), 'nlits': len(cubes[i])}
with ThreadPoolExecutor(a.par) as ex: rows = list(ex.map(one, idx))
with open(f'{a.tag}.sample.jsonl', 'w') as h:
    for r in rows: h.write(json.dumps(r) + '\n')
capped = [min(r['secs'], a.cap) for r in rows]; solved = sum(r['result'] == 'UNSAT' for r in rows); sat = sum(r['result'] == 'SAT' for r in rows)
mean = st.mean(capped)
print(json.dumps({'tag': a.tag, 'cubes': len(cubes), 'cube_secs': round(tcube), 'sample': len(rows), 'solved_frac': round(solved / len(rows), 3),
                  'sat': sat, 'mean_capped_secs': round(mean, 1), 'est_L0_core_s': round(len(cubes) * mean), 'est_caps': round(len(cubes) * (1 - solved / len(rows)))}), flush=True)
