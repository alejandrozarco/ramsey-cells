#!/usr/bin/env python3
"""bench_report.py summary.jsonl : per-instance table of variants (est. total core-s, caps, single-shot) and
geometric-mean ratios vs the deposited breaking ('lex'). Cubing arms (ids with _m<tag>) reported separately."""
import sys, json, math, collections
rows = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
inst = collections.defaultdict(dict); arms = collections.defaultdict(dict)
for r in rows:
    iid, var = r['id'].rsplit('_', 1)
    if var.startswith('m') and var[1:] in ('d8', 'd12', 'dyn', 'nogah'):
        base, form = iid.rsplit('_', 1); arms[(base, form)][var] = r
    else:
        inst[iid][var] = r
def cost(r): return r['est_total_core_s'] + (0.0 if r['l0_caps'] == 0 else 0)
order = ['lex', 'base', 'DO', 'DOL', 'DOL2', 'DOLrev', 'DOLtot', 'DOLbi', 'DOLc4d', 'DOPL', 'DOPL2', 'DOLswap']
print(f'{"instance":14s} ' + ' '.join(f'{v:>9s}' for v in order))
ratios = collections.defaultdict(list)
for iid, vs in inst.items():
    line = f'{iid:14s} '
    for v in order:
        r = vs.get(v)
        if not r: line += f'{"-":>9s} '; continue
        c = cost(r); flag = ('*' if r['l0_caps'] else '') + ('S' if r['l0_sat'] or r.get('single_result') == 'SAT' else '')
        line += f'{c:>8.0f}{flag:1s} '
        if 'lex' in vs and cost(vs['lex']) > 0 and c > 0: ratios[v].append(cost(vs['lex']) / c)
    print(line)
print('\nspeedup vs lex, geometric mean over instances (n): ' + ', '.join(f'{v} {math.exp(sum(map(math.log, xs))/len(xs)):.1f}x ({len(xs)})' for v, xs in ratios.items() if xs))
print('\nsingle-shot secs (S = SAT, cap = time limit):')
for iid, vs in inst.items():
    print(f'{iid:14s} ' + ' '.join(f'{v}={vs[v].get("single_secs","-")}{"S" if vs[v].get("single_result")=="SAT" else ("?" if vs[v].get("single_result")=="CAP" else "")}' for v in order if v in vs and 'single_secs' in vs[v]))
if arms:
    print('\ncubing arms (est. total core-s | cubes | caps):')
    for (base, form), vs in arms.items():
        ref = inst.get(base, {}).get(form)
        print(f'{base}_{form:4s} d10={cost(ref) if ref else "-":>7} ' + ' '.join(f'{k}={cost(r):.0f}|{r["cubes"]}|{r["l0_caps"]}' for k, r in vs.items()))
