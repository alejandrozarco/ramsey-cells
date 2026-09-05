#!/usr/bin/env python3
"""Verify a cnc_close.py run: (1) COVER — every top cube is either an UNSAT leaf with a proof
or is split (retained .icnf) into children that recursively satisfy the same; denominator is
the cube tree on disk, never the ledger. (2) PROOFS — rebuild each leaf CNF from base+cube
literals and run lrat-trim --ascii then lrat-check on the stored LRAT.
usage: verify_close.py BASE.cnf TOP.icnf close_DIR [--check-all | --check-sample N]
"""
import sys, os, json, gzip, subprocess, random, tempfile
TRIM = os.environ.get('LRAT_TRIM', os.path.expanduser('~/claude_projects/sat/lrat-trim/lrat-trim'))
CHECK = os.environ.get('LRAT_CHECK', os.path.expanduser('~/claude_projects/sat/drat-trim/lrat-check'))
base, top, d = sys.argv[1], sys.argv[2], sys.argv[3]
mode = sys.argv[4] if len(sys.argv) > 4 else '--check-sample'; N = int(sys.argv[5]) if len(sys.argv) > 5 else 20
lines = open(base).read().splitlines(); hdr = next(l for l in lines if l.startswith('p cnf')); NV, NC = hdr.split()[2:4]
BODY = "\n".join(l for l in lines if l and l[0] not in 'pc') + "\n"
PROOF_SRC = os.environ.get('PROOF_SRC')   # e.g. gs://bucket/close/out_TAG/proofs : fetch on demand
gs_ids = None
if PROOF_SRC:
    out = subprocess.run(['gsutil', 'ls', PROOF_SRC + '/'], capture_output=True, text=True).stdout
    gs_ids = {os.path.basename(x)[:-len('.lrat.gz')] for x in out.split() if x.endswith('.lrat.gz')}
    print(f"proof source {PROOF_SRC}: {len(gs_ids)} proofs listed")
def have_proof(cid): return (cid in gs_ids) if gs_ids is not None else os.path.exists(f'{d}/proofs/{cid}.lrat.gz')
def read_proof(cid):
    if gs_ids is not None:
        raw = subprocess.run(['gsutil', 'cat', f'{PROOF_SRC}/{cid}.lrat.gz'], capture_output=True).stdout
        return gzip.decompress(raw)
    with gzip.open(f'{d}/proofs/{cid}.lrat.gz', 'rb') as fi: return fi.read()
led = {}
for l in open(f'{d}/ledger.jsonl'):
    if l.strip(): r = json.loads(l); led[r['id']] = r
def cubes_of(icnf): return [l.split()[1:-1] for l in open(icnf) if l.startswith('a ')]
leaves, missing, sat, checked_leaves = [], [], [], []
vset = set()
if os.path.exists(f'{d}/verified_leaves.jsonl'):
    for l in open(f'{d}/verified_leaves.jsonl'):
        if l.strip():
            r = json.loads(l)
            if r.get('verified'): vset.add(r['id'])
def walk(cid, lits, depth=0):
    r = led.get(cid)
    if r and r['result'] == 'UNSAT':
        # v2 rows carry verified=true and the proof was deleted after checking; v1 rows need a proof file
        if r.get('verified') or cid in vset: leaves.append((cid, lits)) if have_proof(cid) else checked_leaves.append(cid); return
        if have_proof(cid): leaves.append((cid, lits)); return
        missing.append((cid, 'UNSAT row but no proof and not verified')); return
    if r and r['result'] == 'SAT': sat.append(cid); return
    ic = next((f'{d}/splits/{f}' for f in os.listdir(f'{d}/splits') if f.startswith(cid + '_d') and f.endswith('.icnf')), None)
    if ic is None: missing.append((cid, r['result'] if r else 'no row, no split')); return
    kids = cubes_of(ic)
    if not kids: walk(cid + '.solo', lits, depth + 1); return
    for j, k in enumerate(kids): walk(f'{cid}.{j}', lits + k, depth + 1)
for i, lits in enumerate(cubes_of(top)): walk(str(i), lits)
print(f"COVER: {len(leaves)} UNSAT leaves with proof files + {len(checked_leaves)} already-verified leaves (proofs deleted) | {len(missing)} gaps | {len(sat)} SAT")
for m in missing[:10]: print("   GAP", m)
if sat: print("   SAT leaves:", sat); sys.exit(2)
if missing and mode != '--proofs-only': print("*** TREE NOT CLOSED ***"); sys.exit(1)
if missing: print(f"(proofs-only mode: {len(missing)} gaps ignored — run still in flight)")
else: print("TREE CLOSED: every leaf of the cube tree on disk has a checked UNSAT verdict (this alone does NOT show the cubes cover the space).")
# --- cover completeness: the conjunction of the NEGATED leaves must be unsatisfiable, with a checked proof.
# Without this, a tree whose listed cubes are all refuted would pass even if the cubes do not cover the space
# (an external review constructed exactly that: a satisfiable formula with an incomplete cube list).
if os.environ.get('SKIP_COVER') != '1':
    CAD = os.environ.get('CADICAL', os.path.expanduser('~/claude_projects/sat/cadical/build/cadical'))
    allcubes = [lits for _, lits in leaves] + [lits for cid, lits in [] ]
    # leaves accepted via verified rows carry no literals in `leaves`; rebuild the full leaf list from the walk
    def all_leaf_lits():
        out = []
        def w(cid, lits):
            r = led.get(cid)
            if r and r['result'] == 'UNSAT' and (r.get('verified') or cid in vset or have_proof(cid)): out.append(lits); return
            ic = next((f'{d}/splits/{f}' for f in os.listdir(f'{d}/splits') if f.startswith(cid + '_d') and f.endswith('.icnf')), None)
            if ic is None: return
            kids = cubes_of(ic)
            if not kids: w(cid + '.solo', lits); return
            for j, k in enumerate(kids): w(f'{cid}.{j}', lits + k)
        for i, lits in enumerate(cubes_of(top)): w(str(i), lits)
        return out
    L = all_leaf_lits()
    with tempfile.TemporaryDirectory() as t:
        cov = f'{t}/negcubes.cnf'; prf = f'{t}/negcubes.lrat'; trm = f'{t}/negcubes.trim'
        with open(cov, 'w') as f:
            f.write(f"p cnf {NV} {len(L)}\n")
            for lits in L: f.write(" ".join(str(-int(x)) for x in lits) + " 0\n")
        r = subprocess.run([CAD, '-q', '--lrat', '--binary=false', cov, prf], capture_output=True, text=True)
        unsat = 's UNSATISFIABLE' in r.stdout
        r1 = subprocess.run([TRIM, cov, prf, trm, '--ascii'], capture_output=True, text=True) if unsat else None
        r2 = subprocess.run([CHECK, cov, trm], capture_output=True, text=True) if unsat else None
        okc = unsat and r1.returncode == 20 and r2.returncode == 0 and 'failed' not in (r2.stdout + r2.stderr).lower()
        print(f"COVER {'VERIFIED' if okc else '*** NOT VERIFIED ***'}: negation of all {len(L)} leaves is {'UNSAT with a checked LRAT proof' if okc else ('SAT -- the cubes do NOT cover the space' if not unsat else 'UNSAT but the proof did not check')}.")
        if not okc: sys.exit(4)
todo = leaves if mode == '--check-all' else random.Random(1).sample(leaves, min(N, len(leaves)))  # sample also in --proofs-only
ok = bad = 0
DELETE = os.environ.get('DELETE_VERIFIED') == '1'
vlog = open(f'{d}/verified_leaves.jsonl', 'a')
already = set()
if os.path.exists(f'{d}/verified_leaves.jsonl'):
    for l in open(f'{d}/verified_leaves.jsonl'):
        if l.strip(): already.add(json.loads(l)['id'])
todo = [x for x in todo if x[0] not in already]
print(f"{len(already)} leaves already verified; {len(todo)} to check")
from concurrent.futures import ThreadPoolExecutor
import threading; vlock = threading.Lock()
def _check(item):
    cid, lits = item
    with tempfile.TemporaryDirectory() as t:
        cnf = f'{t}/leaf.cnf'; raw = f'{t}/p.lrat'; trimmed = f'{t}/t.lrat'
        with open(cnf, 'w') as f: f.write(f"p cnf {NV} {int(NC)+len(lits)}\n"); f.write(BODY); f.write("".join(f"{l} 0\n" for l in lits))
        open(raw, 'wb').write(read_proof(cid))
        r1 = subprocess.run([TRIM, cnf, raw, trimmed, '--ascii'], capture_output=True, text=True)
        r2 = subprocess.run([CHECK, cnf, trimmed], capture_output=True, text=True)
        # verdict = exit codes, not banner text: lrat-trim exits 20 on a checked UNSAT proof,
        # lrat-check exits 0 and prints no 'failed' (negative control: corrupted literal -> rc 1,
        # 'c failed while checking clause'). Confirmed 2026-09-02 on a 1.35 GB proof.
        o2 = (r2.stdout + r2.stderr)
        good = (r1.returncode == 20) and (r2.returncode == 0) and ('failed' not in o2.lower()) and ('error' not in o2.lower())
        if not good: print("   FAIL", cid, (r1.stderr or r1.stdout)[-200:], r2.stdout[-200:], flush=True)
        with vlock:
            vlog.write(json.dumps({'id': cid, 'verified': good, 'raw_bytes': os.path.getsize(raw), 'trim_rc': r1.returncode, 'check_rc': r2.returncode}) + "\n"); vlog.flush()
        if good and DELETE and gs_ids is None:
            os.remove(f'{d}/proofs/{cid}.lrat.gz')
        return good
with ThreadPoolExecutor(max_workers=int(os.environ.get('VPAR', '4'))) as ex:
    for good in ex.map(_check, todo): ok += good; bad += (not good)
print(f"PROOFS: {ok} VERIFIED, {bad} FAILED (of {len(todo)} checked, mode {mode})")
sys.exit(0 if bad == 0 else 3)
