#!/usr/bin/python3
"""M0 step 2: H-only cover instance for one family, lazy lex-leader refinement, final CNF + certificates,
CaDiCaL LRAT proof, lrat-trim, cake_lpr; optional negative controls.
Runs under /usr/bin/python3 (3.9, has pysat). canon() is taken from scripts/astra/census_gen.py by source
extraction (ast); the only in-memory change is that it also returns the labelling p, and every p is re-checked
here (out == g o p) so nothing rests on that change.
usage: hcover.py K C8 C9 C10 [--p0 none|transp] [--controls N] [--noproof]"""
import ast, argparse, json, os, re, subprocess, sys, time, hashlib, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cnfgen
from pysat.solvers import Solver

SAT = os.path.expanduser('~/claude_projects/sat')
CAD = f'{SAT}/cadical/build/cadical'
TRIM = f'{SAT}/lrat-trim/lrat-trim'
LCHK = f'{SAT}/drat-trim/lrat-check'
CAKE = f'{SAT}/cake_lpr/cake_wrap.sh'
CG = os.path.join(HERE, '..', '..', '..', 'scripts', 'astra', 'census_gen.py')


def load_canon():
    src = open(CG).read()
    tree = ast.parse(src)
    fn = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'canon')
    seg = ast.get_source_segment(src, fn)
    assert seg.count('return word, out, aut') == 1
    seg = seg.replace('return word, out, aut', 'return word, out, aut, p')
    ns = {}
    exec(seg, ns)
    return ns['canon'], hashlib.sha256(src.encode()).hexdigest()


canon, CG_SHA = load_canon()


def log(f, msg):
    line = time.strftime('%H:%M:%S ') + msg
    print(line, flush=True)
    f.write(line + '\n'); f.flush()


def relabel(g, p):
    n = len(g)
    return tuple(sum(((g[p[i]] >> p[j]) & 1) << j for j in range(n)) for i in range(n))


def run(cmd, **kw):
    t = time.time()
    r = subprocess.run(['nice', '-n', '10'] + cmd, capture_output=True, text=True, **kw)
    return r, time.time() - t


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('k', type=int); ap.add_argument('c', type=int, nargs=3)
    ap.add_argument('--p0', default='transp'); ap.add_argument('--controls', type=int, default=0)
    ap.add_argument('--noproof', action='store_true'); ap.add_argument('--maxrounds', type=int, default=10**7)
    a = ap.parse_args()
    k, comp = a.k, tuple(a.c)
    tag = f"k{k}_c{comp[0]}{comp[1]}{comp[2]}"
    od = os.path.join(HERE, 'data', tag); os.makedirs(od, exist_ok=True)
    lf = open(os.path.join(HERE, 'logs', f'hcover_{tag}.log'), 'a')
    cls = json.load(open(os.path.join(HERE, 'data', f'classes_{tag}.json')))
    assert cls['k'] == k and tuple(cls['comp']) == comp
    blocked = [c['word'] for c in cls['classes']]
    bset = set(blocked)
    b = cnfgen.Builder(k, comp)
    assert tuple(cls['window']) == (b.lo, b.hi) and tuple(cls['caps']) == b.caps
    degrees = b.degrees
    perms = []
    if a.p0 == 'transp':
        for cell in cnfgen.cells(degrees):
            for i in range(len(cell)):
                for j in range(i + 1, len(cell)):
                    p = list(range(k)); p[cell[i]], p[cell[j]] = cell[j], cell[i]
                    perms.append(tuple(p))
    log(lf, f"=== {tag} degrees={degrees} caps={b.caps} window=({b.lo},{b.hi}) E={b.E} blockers={len(blocked)} "
            f"(listed {cls['listed']}, filter_iii {cls['filtered']}) p0={a.p0}:{len(perms)} census_gen sha256={CG_SHA[:16]}")
    t0 = time.time()
    s = Solver(name='cadical195')
    for c in b.base: s.add_clause(c)
    ll = []
    for p in perms:
        c = b.ll_clauses(p); ll.append(c)
        for cl in c: s.add_clause(cl)
    for w in blocked: s.add_clause(b.blocker(w))
    rounds = 0
    while True:
        if rounds >= a.maxrounds:
            log(lf, f"STOP maxrounds {rounds}"); return 2
        if not s.solve():
            break
        mod = s.get_model()
        w = ''.join('1' if mod[n] > 0 else '0' for n in range(b.E))
        g = cnfgen.graph_of(w, k)
        word, out, aut, p = canon(g, degrees)
        cw = ''.join(map(str, word))
        assert relabel(g, p) == out and cnfgen.word_of(out, k) == cw and cnfgen.is_cell_perm(p, degrees)
        if cw not in bset:
            log(lf, f"DISCREPANCY: model {w} has canonical form {cw} which is NOT among the generator's classes")
            json.dump(dict(model=w, canon=cw), open(os.path.join(od, 'DISCREPANCY.json'), 'w'))
            return 3
        assert cw < w, 'unblocked model equals its own canonical form (impossible: it is blocked)'
        p = tuple(p)
        perms.append(p)
        c = b.ll_clauses(p); ll.append(c)
        for cl in c: s.add_clause(cl)
        rounds += 1
        if rounds % 500 == 0:
            log(lf, f"  round {rounds} perms {len(perms)} vars {b.nv} t={time.time()-t0:.0f}s")
    s.delete()
    tloop = time.time() - t0
    log(lf, f"refinement UNSAT after {rounds} rounds, {len(perms)} LL perms, {tloop:.1f}s")
    # final artefacts (rebuilt from scratch: deterministic in perm order)
    b2, text = cnfgen.build_full(k, comp, perms, blocked, comments=[f"M0 H-only cover {tag}", f"census_gen sha256 {CG_SHA}"])
    cnf = os.path.join(od, f'cover_{tag}.cnf')
    open(cnf, 'w').write(text)
    sha = hashlib.sha256(text.encode()).hexdigest()
    hdr = next(l for l in text.splitlines() if l.startswith('p cnf')).split()
    cert = dict(family=dict(k=k, comp=comp, degrees=degrees, caps=b.caps, window=(b.lo, b.hi), m=21 - k),
                census_gen_sha256=CG_SHA, cnf=os.path.basename(cnf), cnf_sha256=sha,
                nvars=int(hdr[2]), nclauses=int(hdr[3]), base_clauses=len(b2.base),
                perms=[list(p) for p in perms], p0=a.p0, n_p0=len(perms) - rounds, rounds=rounds,
                blockers=cls['classes'], list_files=cls['list_files'])
    json.dump(cert, open(os.path.join(od, f'cert_{tag}.json'), 'w'))
    res = dict(tag=tag, k=k, comp=comp, before=cls['before'], listed=cls['listed'], filtered=cls['filtered'],
               rounds=rounds, perms=len(perms), loop_secs=round(tloop, 1), nvars=cert['nvars'],
               nclauses=cert['nclauses'], cnf_bytes=len(text), cnf_sha256=sha)
    log(lf, f"CNF {cnf}: {cert['nvars']} vars {cert['nclauses']} clauses {len(text)} bytes sha {sha[:16]}")
    if not a.noproof:
        lrat, tl = cnf[:-4] + '.lrat', cnf[:-4] + '.trim.lrat'
        for f in (lrat, tl):
            if os.path.exists(f): os.remove(f)
        r, dt = run([CAD, '-q', '--lrat', '--binary=false', cnf, lrat])
        verdict = 'UNSAT' if r.returncode == 20 and 's UNSATISFIABLE' in r.stdout else f'rc{r.returncode}'
        res.update(cadical=verdict, cadical_secs=round(dt, 2), lrat_bytes=os.path.getsize(lrat) if os.path.exists(lrat) else None)
        log(lf, f"cadical {verdict} {dt:.2f}s lrat {res['lrat_bytes']} B")
        r, dt = run([TRIM, cnf, lrat, tl, "--ascii"])
        res.update(trim_rc=r.returncode, trim_secs=round(dt, 2), trim_bytes=os.path.getsize(tl) if os.path.exists(tl) else None)
        log(lf, f"lrat-trim rc{r.returncode} {dt:.2f}s -> {res['trim_bytes']} B")
        if r.returncode in (0, 20) and res['trim_bytes']:
            r, dt = run([LCHK, cnf, tl])
            res.update(lrat_check='VERIFIED' if 'c VERIFIED' in r.stdout else 'FAIL:' + r.stdout[-200:], lrat_check_secs=round(dt, 2))
            r, dt = run(['/bin/bash', CAKE, cnf, tl])
            res.update(cake='VERIFIED' if 's VERIFIED UNSAT' in r.stdout else 'FAIL:' + (r.stdout + r.stderr)[-200:], cake_secs=round(dt, 2))
            log(lf, f"lrat-check {res['lrat_check']} {res['lrat_check_secs']}s; cake_lpr {res['cake']} {dt:.2f}s")
        if os.path.exists(lrat) and os.path.getsize(lrat) > 50_000_000: os.remove(lrat)  # untrimmed copy only
    # negative controls: drop one blocker, the CNF must be SAT with the dropped graph as its ONLY graph model
    ctl = []
    rng = random.Random(20261006)
    listed = [c['word'] for c in cls['classes'] if c['kind'] == 'listed']
    filt = [c['word'] for c in cls['classes'] if c['kind'] == 'filter_iii']
    picks = []
    for i in range(a.controls):
        pool = listed if (i % 2 == 0 and listed) or not filt else filt
        if pool: picks.append(rng.choice(pool))
    for w in picks:
        kind = 'listed' if w in listed else 'filter_iii'
        _, t2 = cnfgen.build_full(k, comp, perms, [x for x in blocked if x != w])
        cf = os.path.join(od, 'control.cnf'); open(cf, 'w').write(t2)
        r, dt = run([CAD, '-q', cf])
        vals = [int(x) for l in r.stdout.splitlines() if l.startswith('v ') for x in l.split()[1:]]
        mw = ''.join('1' if v > 0 else '0' for v in vals[:b.E]) if r.returncode == 10 else None
        # uniqueness: with the model's own blocker re-added (i.e. the original CNF) it is UNSAT -- shown above;
        # additionally check that no OTHER graph model exists: block mw and solve again
        uniq = None
        if mw is not None:
            open(cf, 'w').write(t2.replace(f"p cnf {b2.nv} {cert['nclauses']-1}", f"p cnf {b2.nv} {cert['nclauses']}") + ' '.join(map(str, b2.blocker(mw))) + ' 0\n')
            r2, _ = run([CAD, '-q', cf]); uniq = (r2.returncode == 20)
        row = dict(dropped=w, kind=kind, rc=r.returncode, model_equals_dropped=(mw == w), unique=uniq, secs=round(dt, 2))
        ctl.append(row)
        log(lf, f"control drop {kind} {w}: rc{r.returncode} model==dropped {mw == w} unique {uniq} {dt:.2f}s")
        os.remove(cf)
    res['controls'] = ctl
    json.dump(res, open(os.path.join(od, f'result_{tag}.json'), 'w'), indent=1)
    log(lf, 'RESULT ' + json.dumps(res))
    return 0


if __name__ == '__main__':
    sys.exit(main())
