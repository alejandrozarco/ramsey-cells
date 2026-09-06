#!/usr/bin/env python3
"""bench.py MANIFEST.json OUTDIR [--par P] [--cap CAP] [--single SECS] [--budget SECS] [--only REGEX]
For every manifest item {id, cnf, march (list of args), single (bool)}:
  1. march_cu <march args> -> cubes (time, count)
  2. every cube solved by cadical -q -t CAP (no proof), pool of P workers; per-cube rows to OUTDIR/<id>.cubes.jsonl
  3. capped cubes resplit with march -d 8 and their children solved (cap CAP) while the per-item budget lasts
  4. optional single-shot cadical -q -t SINGLE on the plain formula
Summary row per item appended to OUTDIR/summary.jsonl (flushed immediately)."""
import argparse, json, os, re, subprocess, sys, time, statistics as st
from concurrent.futures import ThreadPoolExecutor
MARCH = os.environ.get('MARCH', os.path.expanduser('~/sat/CnC/march_cu/march_cu')); CAD = os.environ.get('CADICAL', os.path.expanduser('~/sat/cadical/build/cadical'))
ap = argparse.ArgumentParser(); ap.add_argument('manifest'); ap.add_argument('out')
ap.add_argument('--par', type=int, default=os.cpu_count()); ap.add_argument('--cap', type=int, default=300); ap.add_argument('--single', type=int, default=1800)
ap.add_argument('--budget', type=int, default=7200); ap.add_argument('--only', default=None)
a = ap.parse_args(); os.makedirs(a.out, exist_ok=True)
items = json.load(open(a.manifest))
if a.only: items = [it for it in items if re.search(a.only, it['id'])]
done = set()
if os.path.exists(f'{a.out}/summary.jsonl'):
    for l in open(f'{a.out}/summary.jsonl'):
        if l.strip(): done.add(json.loads(l)['id'])
def read_cnf(path):
    hdr = None; body = []
    for l in open(path):
        if l.startswith('c'): continue
        if l.startswith('p'): hdr = l.split(); continue
        body.append(l)
    return int(hdr[2]), int(hdr[3]), ''.join(body)
def solve(nv, nc, body, lits, tag, cap):
    f = f'{a.out}/tmp_{tag}.cnf'
    with open(f, 'w') as h: h.write(f'p cnf {nv} {nc+len(lits)}\n'); h.write(''.join(f'{x} 0\n' for x in lits)); h.write(body)
    t = time.time(); r = subprocess.run([CAD, '-q', '-t', str(cap), f], capture_output=True, text=True); s = time.time() - t
    os.remove(f); res = 'UNSAT' if 's UNSATISFIABLE' in r.stdout else 'SAT' if 's SATISFIABLE' in r.stdout else 'CAP'
    return res, round(s, 1)
def cube_file(path, lits, depth, tag):
    f = f'{a.out}/tmp_{tag}_split.cnf'; ic = f'{a.out}/tmp_{tag}_split.icnf'
    nv, nc, body = read_cnf(path)
    with open(f, 'w') as h: h.write(f'p cnf {nv} {nc+len(lits)}\n'); h.write(''.join(f'{x} 0\n' for x in lits)); h.write(body)
    subprocess.run([MARCH, f, '-d', str(depth), '-o', ic], capture_output=True, timeout=3600); os.remove(f)
    kids = [l.split()[1:-1] for l in open(ic) if l.startswith('a ')] if os.path.exists(ic) else []
    if os.path.exists(ic): os.remove(ic)
    return kids
for it in items:
    if it['id'] in done: continue
    t_item = time.time(); cnf = it['cnf']; nv, nc, body = read_cnf(cnf)
    row = {'id': it['id'], 'cnf': os.path.basename(cnf), 'vars': nv, 'clauses': nc, 'march': it.get('march', ['-d', '10'])}
    icnf = f'{a.out}/{it["id"]}.icnf'; t0 = time.time()
    subprocess.run([MARCH, cnf] + it.get('march', ['-d', '10']) + ['-o', icnf], capture_output=True, timeout=7200)
    cubes = [l.split()[1:-1] for l in open(icnf) if l.startswith('a ')] if os.path.exists(icnf) else []
    row['cube_secs'] = round(time.time() - t0, 1); row['cubes'] = len(cubes)
    if not cubes: cubes = [[]]; row['cubes'] = 0
    import random; random.seed(1)
    idx = sorted(random.sample(range(len(cubes)), it['sample'])) if it.get('sample') and it['sample'] < len(cubes) else list(range(len(cubes)))
    row['sampled'] = len(idx)
    tasks = [(i, cubes[i], a.cap) for i in idx] + ([(-1, [], a.single)] if it.get('single', True) else [])
    with ThreadPoolExecutor(a.par) as ex:
        allrows = list(ex.map(lambda t: (t[0], *solve(nv, nc, body, t[1], f'{it["id"]}_{t[0]}', t[2])), tasks))
    single = [r for r in allrows if r[0] == -1]; rows = [r for r in allrows if r[0] >= 0]
    if single: row.update(single_result=single[0][1], single_secs=single[0][2])
    with open(f'{a.out}/{it["id"]}.cubes.jsonl', 'w') as h:
        for i, res, s in rows: h.write(json.dumps({'cube': i, 'result': res, 'secs': s, 'nlits': len(cubes[i])}) + '\n')
    secs = [s for _, _, s in rows]; caps = [i for i, res, _ in rows if res == 'CAP']; sat = [i for i, res, _ in rows if res == 'SAT']
    row.update(l0_core_s=round(sum(secs)), l0_solved=len(rows) - len(caps) - len(sat), l0_caps=len(caps), l0_sat=len(sat),
               l0_mean=round(st.mean(secs), 2), l0_median=round(st.median(secs), 2), l0_max=round(max(secs), 1))
    # tail: resplit caps at depth 8 within budget
    tail_core = 0; tail_children = 0; tail_caps = 0; tail_done = 0
    for i in caps[:it.get('tail_max', 10)]:
        if time.time() - t_item > a.budget: break
        kids = cube_file(cnf, cubes[i], 8, f'{it["id"]}_{i}')
        if not kids: continue
        with ThreadPoolExecutor(a.par) as ex:
            krows = list(ex.map(lambda j: solve(nv, nc, body, cubes[i] + kids[j], f'{it["id"]}_{i}_{j}', a.cap), range(len(kids))))
        tail_children += len(kids); tail_core += sum(s for _, s in krows); tail_caps += sum(r == 'CAP' for r, _ in krows); tail_done += 1
    row.update(tail_parents_split=tail_done, tail_children=tail_children, tail_core_s=round(tail_core), tail_caps=tail_caps,
               est_total_core_s=round((sum(secs) + (tail_core / tail_done * len(caps) if tail_done else 0)) * (len(cubes) / max(1, len(rows)))))
    row['wall_secs'] = round(time.time() - t_item)
    with open(f'{a.out}/summary.jsonl', 'a') as h: h.write(json.dumps(row) + '\n')
    print(json.dumps(row), flush=True)
print('BENCH DONE', flush=True)
