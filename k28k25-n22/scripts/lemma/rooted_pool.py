#!/usr/bin/env python3
"""Global cube pool for the rooted census (2026-09-09 ~11:00 UTC): one thread pool over EVERY cube of every given list
file, so that a single hard cube never idles the other workers (the per-composition pools of rooted_census.py did).
Each cube: build the CNF (rooted_encode.rooted_formula, budget), CaDiCaL (--lrat when PROOF=1), lrat-trim, lrat-check,
one ledger row appended to <ledger-dir>/ledger_<tag>.jsonl (resume-safe: verified H are skipped at start). The case
parameters (hist, root, comp) of a list come from its gen_<tag>.json.
usage: rooted_pool.py N COLORS --lists H_a.txt H_b.txt ... [--ledger-dir DIR] [--workers W] [--limit C] [--tmp DIR]"""
import re
import argparse, glob, hashlib, json, os, shutil, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.abspath(os.path.join(HERE, '..', '..')))
from rooted_encode import rooted_formula, write
ap = argparse.ArgumentParser(); ap.add_argument('N', type=int); ap.add_argument('colors'); ap.add_argument('--lists', nargs='+', required=True)
ap.add_argument('--ledger-dir'); ap.add_argument('--channel', action='store_true'); ap.add_argument('--wallpairs', action='store_true'); ap.add_argument('--auth', action='store_true'); ap.add_argument('--require-provenance', action='store_true', help='a cube counts as done only with cake_verified AND a non-empty encoder commit AND cnf_sha256, so one pass brings every row to full provenance (rows from before those fields existed are re-solved)')
ap.add_argument('--require-cake', action='store_true', help='treat a cube as done only if a row has cake_verified true (regeneration pass for the formally verified grade)'); ap.add_argument('--workers', type=int, default=8); ap.add_argument('--limit', type=int, default=0); ap.add_argument('--no-base-codegree', action='store_true', help='drop the codegree layer duplicated by add_counting. SAFE, BUT NOT A PURE DELETION: it also shifts every auxiliary by 57,519 (round 27 item 3). The UNSAT implication holds via the substitution v -> v+57519 on auxiliaries, not by clause removal alone. Recorded per row so a mixed census stays auditable.')
ap.add_argument('--tlimit', type=int, default=0, help='wall-clock seconds per cube (cadical -t). The right unit for bounding worker occupancy: the conflict rate varies by more than 2x across cubes, so a conflict cap of 3M was 26 min on one cube and 55 min on another.'); ap.add_argument('--tmp', default='/private/tmp/rooted_pool'); a = ap.parse_args()
import shutil
RETAIN_URI = os.environ.get('RETAIN_URI')   # where to keep proofs whose cake run did not succeed
PROOF = os.environ.get('PROOF', '0') == '1'
CAD = os.environ.get('CADICAL', 'cadical')
CAKE = os.environ.get('CAKE')   # optional cake_lpr (formally verified LRAT checker) on the trimmed proof
TRIM = os.environ.get('TRIM', 'lrat-trim'); CHECK = os.environ.get('CHECK', 'lrat-check')
os.makedirs(a.tmp, exist_ok=True); lock = threading.Lock(); leds = {}

def _sha_file(p_):
    """sha256 of a file, or None if it is not there."""
    try:
        h = hashlib.sha256()
        with open(p_, 'rb') as f:
            for c in iter(lambda: f.read(1 << 20), b''): h.update(c)
        return h.hexdigest()
    except OSError:
        return None

def _cake_binary(w):
    """CAKE may be the checker itself or a shell wrapper that execs it; identify the real BINARY either way
    (round 21 B1). Reading a wrapper as text is fine; reading the binary as text is not, so decode errors are
    expected and mean 'this is already the binary'."""
    if not w: return None, None
    try:
        with open(w, 'rb') as f: head = f.read(2)
        if head != b'#!': return w, _sha_file(w)      # not a script: CAKE is the executable itself
        with open(w, 'r', errors='replace') as f:
            for l in f:
                l = l.split('#')[0]                   # a comment naming the binary is not the binary
                for tok in l.split():
                    if '/' in tok and os.path.isfile(tok) and os.access(tok, os.X_OK): return tok, _sha_file(tok)
    except OSError: pass
    return w, _sha_file(w)

TOOLS = dict(solver=dict(path=CAD, sha256=_sha_file(CAD),
                         version=subprocess.run([CAD, '--version'], capture_output=True, text=True).stdout.strip() or None),
             trim=dict(path=TRIM, sha256=_sha_file(TRIM)), check=dict(path=CHECK, sha256=_sha_file(CHECK)))
_cb, _cs = _cake_binary(CAKE)
TOOLS['cake'] = dict(wrapper=CAKE, wrapper_sha256=_sha_file(CAKE) if CAKE else None, binary=_cb, binary_sha256=_cs)
PYVER = sys.version.split()[0]
def log(*x): print(time.strftime('%H:%M'), *x, flush=True)
_HEX7 = re.compile(r'^[0-9a-f]{7,40}$'); _SHA256 = re.compile(r'^[0-9a-f]{64}$')

def full_provenance(r):
    """cake_lpr certificate + a well-formed formula hash + a well-formed commit: the top per-cube grade.
    The fields are VALIDATED, not merely non-empty: Astra round 21 reproduced the old predicate accepting
    {"encoder": "garbage"} and any non-empty string as a hash."""
    src = r.get('encoder_sources_sha256') or {}
    identified = bool(_HEX7.match(str(r.get('encoder') or '').split('@')[-1])) or (
        isinstance(src, dict) and bool(_SHA256.match(str(src.get('rooted_encode.py') or ''))))
    return (bool(r.get('cake_verified'))
            and bool(_SHA256.match(str(r.get('cnf_sha256') or '')))
            and identified)      # a commit stamp OR the encoder's own source hash: the boxes are not git checkouts

ENCODER_STAMP = 'rooted_encode.py@' + subprocess.run(['git', '-C', os.path.dirname(os.path.abspath(__file__)),
                'rev-parse', '--short', 'HEAD'], capture_output=True, text=True).stdout.strip()   # once, BEFORE any solve
# The commit stamp is EMPTY on any host that is not a git checkout - which is both cloud boxes, since they run from a
# tarball unpack. Every row there recorded 'rooted_encode.py@' with nothing after it, making the formula
# non-reconstructible exactly where the work happens. Hash the encoder sources themselves: self-identifying anywhere.
import rooted_encode as _re
try: import typed_encode as _te
except Exception: _te = None
try: import lemma_encode as _le
except Exception: _le = None
try:
    import gen_ramsey as _gr          # emits the edge and base-codegree clauses; r27 item 6b
except Exception: _gr = None
ENCODER_SOURCES = {}
for _m in (_re, _te, _le, _gr):
    if _m is None: continue
    try: ENCODER_SOURCES[os.path.basename(_m.__file__)] = _sha_file(os.path.abspath(_m.__file__))
    except Exception: pass
tasks = []; skipped = 0; capped_skipped = 0
for lst in a.lists:
    tag = os.path.basename(lst)[2:-4]; d = os.path.dirname(os.path.abspath(lst)); led_dir = a.ledger_dir or d
    g = json.load(open(f"{d}/gen_{tag}.json")); hist = tuple(g['hist']); k = g['root']; DEG = tuple(g.get('degrees', (8, 9, 10))); comp = {dd: n for dd, n in zip(DEG, g['composition']) if n}
    if 'N' in g: assert g['N'] == a.N and g.get('colors', a.colors) == a.colors, f"list {tag} is for N={g['N']} {g.get('colors')}, not {a.N} {a.colors}"
    degs = [dd for dd, c in zip(DEG, hist) for _ in range(c)]; hist_s = ','.join(map(str, hist)); comp_s = ','.join(map(str, g['composition']))
    led = f"{led_dir}/ledger_{tag}.jsonl"; have = set(); capped_seen = set()
    lsha = _sha_file(lst); gsha = _sha_file(f"{d}/gen_{tag}.json")
    if os.path.exists(led):
        for l in open(led):
            try:
                r = json.loads(l)
                same_case = r.get('hist') == hist_s and r.get('root') == k and r.get('comp') == comp_s
                if r['rc'] in (10, 20) and (not PROOF or r.get('verified') or r.get('cake_verified')) and (not a.require_cake or r.get('cake_verified')) and (not a.require_provenance or full_provenance(r)) and same_case: have.add(json.dumps(r['H']))
                # a cube already capped at this limit or higher is not worth re-burning the cap on at every restart; it
                # belongs to the split lane (scripts/lemma/split_certify.py). Only skip when we are running capped.
                if r['rc'] == 0 and same_case and (
                        (a.limit and (r.get('limit') or 0) >= a.limit) or
                        (a.tlimit and (r.get('tlimit') or 0) >= a.tlimit)):
                    capped_seen.add(json.dumps(r['H']))
            except Exception: pass
    for l in open(lst):
        l = l.split('#')[0].strip()
        if not l: continue
        H = sorted(tuple(int(x) for x in e.split('-')) for e in l.split(','))
        if json.dumps(H) in have: skipped += 1; continue
        if json.dumps(H) in capped_seen: capped_skipped += 1; continue
        tasks.append((tag, led, hist_s, k, comp_s, degs, comp, H, lsha, gsha))
log(f"pool: {len(a.lists)} lists, {len(tasks)} cubes to do, {skipped} already verified, {capped_skipped} left to the split lane (capped at >= {a.limit} conflicts / {a.tlimit}s), {a.workers} workers, PROOF={int(PROOF)}, limit={a.limit}, tlimit={a.tlimit}")
done = [0]; t_start = time.time()
def one(t):
    tag, led, hist_s, k, comp_s, degs, comp, H, lsha, gsha = t
    try:        # skip if another machine certified this cube meanwhile (ledgers are merged by sync_ledgers.py)
        for l in open(led):
            r = json.loads(l)
            if (r.get('verified') or r.get('cake_verified')) and r['H'] == H and (not a.require_cake or r.get('cake_verified')) and (not a.require_provenance or full_provenance(r)):
                with lock: done[0] += 1
                return
    except Exception: pass
    while shutil.disk_usage(a.tmp).free < float(os.environ.get('MIN_FREE_GB', '3')) * 2**30: time.sleep(60)   # MIN_FREE_GB: raise on small disks (hard cubes write multi-GB proofs)
    p = f"{a.tmp}/cube_{os.getpid()}_{threading.get_ident()}.cnf"; pr = p + '.lrat'; tr = p + '.trim'
    cls, nv, com, hedges, D = rooted_formula(a.N, a.colors.split(','), degs, k, comp, H=H, budget=True, channel=a.channel, wallpairs=a.wallpairs, auth=a.auth, base_codegree=not a.no_base_codegree); write(p, cls, nv, com); sha = hashlib.sha256(open(p, 'rb').read()).hexdigest()
    t0 = time.time(); args = ['nice', '-n', '5', CAD, '-q'] + (['-c', str(a.limit)] if a.limit else []) + (['-t', str(a.tlimit)] if a.tlimit else []) + (['--lrat', '--binary=' + ('true' if os.environ.get('PROOF_BINARY', '0') == '1' else 'false'), p, pr] if PROOF else [p])   # PROOF_BINARY=1 halves the raw proof on disk; lrat-trim reads both
    r = subprocess.run(args, capture_output=True, text=True)
    row = {'hist': hist_s, 'root': k, 'comp': comp_s, 'H': H, 'nedges': len(H), 'rc': r.returncode, 'secs': round(time.time() - t0, 1), 'verified': False, 'limit': a.limit, 'tlimit': a.tlimit, 'host': os.uname().nodename, 'pool': True, 'cnf_sha256': sha, 'encoding': {'budget': True, 'channel': a.channel, 'wallpairs': a.wallpairs, 'auth': a.auth, 'base_codegree': not a.no_base_codegree}, 'encoder': ENCODER_STAMP, 'encoder_sources_sha256': ENCODER_SOURCES, 'schema_version': 2, 'tag': tag, 'N': a.N, 'colors': a.colors.split(','), 'list_sha256': lsha, 'gen_sha256': gsha, 'python': PYVER, 'tools': TOOLS, 'started_at_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(t0))}
    if PROOF and r.returncode == 20:
        tt = subprocess.run([TRIM, p, pr, tr, '--ascii'], capture_output=True); kk = subprocess.run([CHECK, p, tr], capture_output=True, text=True)
        row['trim_rc'] = tt.returncode; row['check_rc'] = kk.returncode; row['verified'] = (tt.returncode == 20 and kk.returncode == 0); row['proof_bytes'] = os.path.getsize(pr) if os.path.exists(pr) else None
        # cake_lpr reads binary LPR directly ("The LPR proof file can optionally be in binary format"), so trimming is not a
        # logical prerequisite for the top grade. Measured 2026-09-10 on three cubes (0.5, 10.5, 27.6 MB raw): raw binary and
        # trimmed ASCII both give 's VERIFIED UNSAT' in comparable time. So when lrat-trim fails - which is what put 80 lists in
        # the monster bucket - fall back to checking the RAW proof, instead of losing the cube's grade entirely.
        if CAKE:
            src = tr if row['verified'] else pr
            cap = float(os.environ.get('CAKE_MAX_GIB', '4')) * 2**30      # cake_lpr needs heap ~ proof size; skip what cannot fit
            if os.path.exists(src) and os.path.getsize(src) <= cap:
                ck = subprocess.run([CAKE, p, src], capture_output=True, text=True)
                row['cake_rc'] = ck.returncode; row['cake_verified'] = ('s VERIFIED UNSAT' in ck.stdout)
                row['cake_input'] = 'trimmed' if row['verified'] else 'raw'
            else:
                row['cake_verified'] = False; row['cake_input'] = 'skipped_too_large'
    if r.returncode == 10:
        open(led + f'.SAT_{int(time.time())}.txt', 'w').write(r.stdout)
        if a.no_base_codegree:
            # The reduced formula has clauses REMOVED, so its models are a superset: rc 10 here proves nothing about the
            # cell until it is confirmed against the FULL formula. Re-solve with base_codegree=True before claiming it.
            log(f'SAT under the reduced encoding in {tag} H={H}: revalidating against the FULL formula before any claim')
            cls2, nv2, com2, _h2, _D2 = rooted_formula(a.N, a.colors.split(','), degs, k, comp, H=H, budget=True,
                                                       channel=a.channel, wallpairs=a.wallpairs, auth=a.auth, base_codegree=True)
            p2 = p + '.full.cnf'; write(p2, cls2, nv2, com2)
            r2 = subprocess.run(['nice', '-n', '5', CAD, '-q', p2], capture_output=True, text=True)
            row['sat_revalidation_rc'] = r2.returncode
            row['sat_confirmed'] = (r2.returncode == 10)
            if r2.returncode == 10:
                open(led + f'.SAT_CONFIRMED_{int(time.time())}.txt', 'w').write(r2.stdout)
                log(f'!!! SAT CONFIRMED against the full formula in {tag} H={H}')
            else:
                log(f'SAT under the reduced encoding did NOT survive the full formula (rc {r2.returncode}) in {tag}: NOT a witness')
            try: os.remove(p2)
            except FileNotFoundError: pass
        else:
            log(f'!!! SAT in {tag} H={H}')
    # RETAIN BEFORE DELETE. Astra r24: this cleanup removed the CNF and both proofs
    # unconditionally, and did so BEFORE the ledger row was written, so a cube whose cake_lpr run
    # was OOM-killed could never reach grade 3 again except by a full re-solve. Eleven cubes are
    # already in that state, 17.3 GB of proof gone. Keep the artefact exactly when the top grade
    # was NOT reached; that is ~1 in 2,000 rows, so the cost is negligible and the category of
    # "permanently stuck at grade 2" disappears.
    if RETAIN_URI and row.get('rc') == 20 and not row.get('cake_verified') and PROOF:
        src = tr if (row.get('verified') and os.path.exists(tr)) else pr
        try:
            if os.path.exists(src) and shutil.which('gsutil'):
                dest = f"{RETAIN_URI.rstrip('/')}/{tag}/{os.path.basename(src)}"
                rr = subprocess.run(['gsutil', '-q', 'cp', src, dest], capture_output=True, text=True, timeout=1800)
                row['retained_proof'] = dest if rr.returncode == 0 else None
                row['retained_rc'] = rr.returncode
                row['retained_kind'] = 'trimmed' if src == tr else 'raw'
                row['retained_bytes'] = os.path.getsize(src)
                log(f"retained {row['retained_kind']} proof for {tag} ({row['retained_bytes']//10**6} MB) -> {dest} rc={rr.returncode}")
        except Exception as e:
            row['retained_proof'] = None; row['retained_error'] = str(e)[:200]
    for f_ in (p, pr, tr):
        try: os.remove(f_)
        except FileNotFoundError: pass
    row['checked_at_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
    with lock:
        with open(led, 'a') as f: f.write(json.dumps(row) + '\n')
        done[0] += 1; n = done[0]
    flag = '' if row['rc'] == 20 and (row['verified'] or row.get('cake_verified') or not PROOF) else ' <<< ' + ('CAPPED' if row['rc'] == 0 else 'SAT' if row['rc'] == 10 else f"rc {row['rc']} verified {row['verified']}")
    log(f"[{n}/{len(tasks)}] {tag} ({len(H)} e): {row['secs']}s" + (f" proof {round((row.get('proof_bytes') or 0)/1e6)}MB" if PROOF else '') + flag)
    if n % 50 == 0: log(f"STATUS {n}/{len(tasks)} done, {round((time.time() - t_start) / 60)} min elapsed, rate {round(n / max(1, (time.time() - t_start) / 3600))}/h")
with ThreadPoolExecutor(max_workers=a.workers) as ex: list(ex.map(one, tasks))
log(f"POOL DONE: {done[0]} cubes in {round((time.time() - t_start) / 60)} min")
