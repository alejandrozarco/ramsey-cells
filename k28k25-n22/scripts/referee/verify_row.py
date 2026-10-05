#!/usr/bin/env python3
"""Rebuild the CNF a ledger row describes, and check it against the row's recorded `cnf_sha256`.

This is the check that lets a reviewer confirm they are looking at the same formula the campaign
solved, WITHOUT downloading proofs or trusting the solver. It reads only the row, the list file and
the generator json -- all of which are in the repository.

THE SUBTLETY. Two drivers wrote these rows and they build the `comp` dict differently:

    rooted_pool.py:94       comp = {dd: n for dd, n in zip(DEG, g['composition'])}
    rooted_pool_new.py:38   comp = {dd: n for dd, n in zip(DEG, g['composition']) if n}

The second drops degree classes with a zero count. The resulting formulas are IDENTICAL as clause
sets -- same variables, same clauses, verified by direct comparison -- but the clauses come out in a
different ORDER, so the files differ byte-for-byte and their sha256 differs. Nothing in a row says
which driver produced it, but `encoding.base_codegree` discriminates perfectly: the monster lane
(`rooted_pool_new.py`) never passes the flag, so its rows record True, while the census lanes run
it False or predate it.

    base_codegree True            -> zero-filtered comp
    base_codegree False / absent  -> unfiltered comp

An earlier version of this script INFERRED which convention a row used from `encoding.base_codegree`
(True -> filtered, False/absent -> unfiltered). Astra round 35 disproved that rule with a
counterexample: `ledger_2_12_8_r8_c044.jsonl` row 19 has `base_codegree` ABSENT and reproduces only
under the FILTERED convention. The inference was measured on a random sample that happened to miss
such rows.

So this script no longer infers. It tries BOTH conventions and accepts only an exact match against
the recorded hash. That is strictly better: a row reproduces or it does not, and no rule has to be
trusted.

usage:  verify_row.py --tag 0_12_10_r10_c0100 [--all] [--sample N]
"""
import time
import argparse, collections, glob, hashlib, json, os, random, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'scripts', 'lemma'))
sys.path.insert(0, ROOT)                       # gen_ramsey.py lives at the REPO ROOT, not scripts/lemma
from rooted_encode import rooted_formula, write

D = os.path.join(ROOT, 'runs', 'k28_rooted')
ap = argparse.ArgumentParser()
ap.add_argument('--tag'); ap.add_argument('--all', action='store_true')
ap.add_argument('--sample', type=int, default=0)
a = ap.parse_args()

def rebuild(tag, r):
    """Return (matched_convention, last_hash). Tries BOTH comp conventions; never infers.

    An earlier version inferred the convention from `encoding.base_codegree`. Astra round 35
    disproved that with ledger_2_12_8_r8_c044 row 19, where the field is ABSENT yet only the
    FILTERED convention reproduces. Trying both is strictly better: a row reproduces or it does
    not, and no rule has to be trusted."""
    g = json.load(open(f'{D}/gen_{tag}.json'))
    DEG = tuple(g.get('degrees', (8, 9, 10))); hist = tuple(g['hist'])
    degs = [dd for dd, c in zip(DEG, hist) for _ in range(c)]
    enc = dict(r['encoding']); enc.pop('budget', None)
    last = None
    for label, filt in (('filtered', True), ('unfiltered', False)):
        comp = {dd: n for dd, n in zip(DEG, g['composition']) if (n or not filt)}
        cls, nv, com, _h, _D = rooted_formula(r['N'], r['colors'], degs, g['root'], comp,
                                              H=[tuple(e) for e in r['H']], budget=True, **enc)
        fd, tmp = tempfile.mkstemp(suffix='.cnf'); os.close(fd)
        try:
            write(tmp, cls, nv, com)
            h = hashlib.sha256(open(tmp, 'rb').read()).hexdigest()
        finally:
            os.unlink(tmp)
        last = h
        if h == r['cnf_sha256']:
            return label, h
    return None, last

files = ([f'{D}/ledger_{a.tag}.jsonl'] if a.tag else sorted(glob.glob(f'{D}/ledger_*.jsonl')))
# A sorted prefix is not a sample: with --sample 100 it drew all 100 rows from ONE tag and hid a
# whole failing convention (Astra round 35). Shuffle, with a fixed seed so runs are comparable.
if not a.tag: random.seed(20260914); random.shuffle(files)
res = collections.Counter(); bad = []


def checked_count(c):
    """Rows actually checked.

    The keys this counter carries are decorated -- 'REPRODUCED (filtered composition)',
    'MISMATCH (neither convention)' -- so c['REPRODUCED'] and c['MISMATCH'] are ALWAYS zero and
    a stop condition written on them never fires. That is what --sample did: it looked like a
    sample, ran the entire census, and the only visible symptom was that it took an hour. Match
    by prefix, exactly as the final tally below does."""
    return sum(v for k, v in c.items() if k.startswith(('REPRODUCED', 'MISMATCH', 'ERROR')))


_t0 = time.time()
_last = [0.0]


def tick(force=False):
    """Progress to stderr. A referee running this over a few hundred rows gets no output at all
    until it exits -- stdout is block-buffered when redirected -- so a working run and a hung one
    look identical for the whole hour."""
    now = time.time()
    if not force and now - _last[0] < 15:
        return
    _last[0] = now
    n = checked_count(res)
    goal = f'/{a.sample}' if a.sample else ''
    print(f'  ... {n}{goal} rows checked, {int(now - _t0)}s elapsed', file=sys.stderr, flush=True)


for f in files:
    tag = os.path.basename(f)[7:-6]
    if not os.path.exists(f'{D}/gen_{tag}.json'): continue
    for L in open(f):
        try: r = json.loads(L)
        except Exception: continue
        if not all(k in r for k in ('encoding', 'cnf_sha256', 'H', 'N', 'colors')):
            res['skipped: row predates the fields needed'] += 1; continue
        try: conv, got = rebuild(tag, r)
        except Exception as e:
            res['ERROR'] += 1; bad.append((tag, f'{type(e).__name__}: {e}')); continue
        tick()
        if conv:
            res[f'REPRODUCED ({conv} composition)'] += 1
        else:
            res['MISMATCH (neither convention)'] += 1
            bad.append((tag, f'recorded {r["cnf_sha256"][:16]} got {got[:16]}'))
        if a.sample and checked_count(res) >= a.sample: break
    if a.sample and checked_count(res) >= a.sample: break

print()
for k, v in res.most_common(): print(f"  {v:7,}  {k}")
checked = sum(v for k, v in res.items() if k.startswith(('REPRODUCED', 'MISMATCH', 'ERROR')))
if checked == 0:
    print("  !! CHECKED NOTHING -- an exit 0 here would be a false success")
    sys.exit(2)
for t, m in bad[:10]: print(f"     ! {t}: {m}")
sys.exit(1 if any(k.startswith(('MISMATCH', 'ERROR')) for k in res) else 0)
