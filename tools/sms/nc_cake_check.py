#!/usr/bin/env python3
"""Machine-check every non-canonicity certificate of an smsg symmetry-clause dump with cake_lpr.

Each entry of the dump is a pair (clause, permutation). The clause is sound to add iff the
permutation is a valid non-canonicity witness for the partial assignment the clause forbids, over
ALL completions; nc_sat_reduction.build() turns that statement into a propositional formula whose
UNSAT-ness is exactly the validity of the witness. Each formula is refuted by CaDiCaL with an LRAT
proof, trimmed by lrat-trim, and checked by cake_lpr (a CakeML-verified checker). No new trusted
code beyond nc_sat_reduction.build(), which two independent decision procedures (checker_A.py,
checker_C.py in the campaign repository) agree with.

WHAT THIS DOES NOT SHOW: that appending the whole set of clauses preserves satisfiability. That
step, the composition of individually valid certificates, is a mathematical argument stated in
tools/sms/README.md and is not machine-checked. Do not describe the output of this script as
"verified symmetry breaking".

usage: nc_cake_check.py SIGMA.json N LEDGER.jsonl [--limit K]
env:   CADICAL, LRAT_TRIM, CAKE_LPR (paths; defaults assume ~/sat/...)
Verdicts are taken from EXIT CODES (CaDiCaL 20, lrat-trim 20) and from cake_lpr's "s VERIFIED UNSAT"
line, which is the checker's documented success output.
"""
import json, os, subprocess, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nc_sat_reduction import build, pairs_of

def main():
    a = sys.argv[1:]
    path, n, ledger = a[0], int(a[1]), a[2]
    limit = int(a[a.index('--limit') + 1]) if '--limit' in a else None
    CAD = os.environ.get('CADICAL', os.path.expanduser('~/sat/cadical/build/cadical'))
    TRIM = os.environ.get('LRAT_TRIM', os.path.expanduser('~/sat/lrat-trim/lrat-trim'))
    CAKE = os.environ.get('CAKE_LPR', os.path.expanduser('~/sat/cake_lpr/cake_lpr'))
    data = json.load(open(path))['sym_clauses']
    if limit: data = data[:limit]
    pairs = pairs_of(n); idx = {p: i for i, p in enumerate(pairs)}
    tmp = os.environ.get('TMPDIR', '/tmp'); tag = os.getpid()
    led = open(ledger, 'w'); ok = cakeok = 0; bad = []; t0 = time.time()
    for i, (clause, perm) in enumerate(data):
        nv, cls = build(clause, perm, n, pairs, idx)
        c, p, t = (f"{tmp}/nc_{tag}_{i}.{ext}" for ext in ('cnf', 'lrat', 't.lrat'))
        with open(c, 'w') as f:
            f.write(f"p cnf {nv} {len(cls)}\n")
            for cl in cls: f.write(" ".join(map(str, cl)) + " 0\n")
        r = subprocess.run([CAD, '-q', '--lrat', '--binary=false', c, p], capture_output=True)
        row = {'clause': i, 'rc': r.returncode}
        if r.returncode == 20:
            ok += 1
            tr = subprocess.run([TRIM, c, p, t, '--ascii'], capture_output=True); row['trim_rc'] = tr.returncode
            ck = subprocess.run([CAKE, c, t], capture_output=True, text=True)
            row['cake'] = 'VERIFIED' if (tr.returncode == 20 and 's VERIFIED UNSAT' in ck.stdout) else ck.stdout.strip()[:50]
            if row['cake'] == 'VERIFIED': cakeok += 1
            else: bad.append(i)
        else:
            bad.append(i)
        for f_ in (c, p, t):
            try: os.remove(f_)
            except FileNotFoundError: pass
        led.write(json.dumps(row) + "\n")
        if i % 500 == 0: print(f"  {i}/{len(data)} unsat={ok} cake={cakeok}", flush=True)
    led.close()
    print(f"NC-CAKE SUMMARY clauses={len(data)} UNSAT={ok} cake_VERIFIED={cakeok} bad={len(bad)} "
          f"first_bad={bad[:5]} secs={time.time()-t0:.0f}", flush=True)
    sys.exit(0 if not bad else 1)

if __name__ == '__main__':
    main()
