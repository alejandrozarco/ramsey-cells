#!/usr/bin/env python3
"""Refute ONE rooted census cube by a scripted incidence split, with a certificate for every child.

Why the parent's verdict follows: the children are the parent's exact clauses plus one unit per branch variable, and all
2^k sign patterns are present, so the disjunction of their unit sets is a tautology and UNSAT of every child gives UNSAT
of the parent. Coverage therefore needs no cover formula and no cover proof, unlike a march split.

Per child: CaDiCaL with binary LRAT -> lrat-trim + lrat-check -> cake_lpr (on the trimmed proof, or on the raw proof when
trimming fails, since cake reads binary LPR directly). A child that caps is retried once at --escalate conflicts. Proofs
are deleted as soon as they are checked; only hashes and sizes are kept.

The parent row is appended to the census ledger with rc 20 and the same (hist, root, comp, H) identity as an ordinary
cube, so the existing counters see it, PLUS a 'split' object carrying the branch variables, every child's sha256 and
verdict, and the coverage assertion. cake_verified is set only if EVERY child was cake-checked.

usage: split_certify.py --tag TAG --hidx I [--depth 6] [--mode column] [--limit 200000] [--escalate 3000000]
                        [--workers 2] [--tmp DIR] [--ledger-dir DIR]"""
import argparse, hashlib, itertools, json, os, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.abspath(os.path.join(HERE, '..', '..')))
from rooted_encode import rooted_formula, write, edge_index, cells_of
D = os.environ.get('CENSUS_DIR', os.path.join(HERE, '..', '..', 'runs', 'k28_rooted'))   # CENSUS_DIR: where H_*.txt and gen_*.json live (the boxes keep them elsewhere)
CAD = os.environ.get('CADICAL', 'cadical')
TRIM = os.environ.get('TRIM', 'lrat-trim')
CHECK = os.environ.get('CHECK', 'lrat-check')
CAKE = os.environ.get('CAKE', 'cake_lpr')
CAKE_MAX = float(os.environ.get('CAKE_MAX_GIB', '4')) * 2 ** 30
ap = argparse.ArgumentParser(); ap.add_argument('--tag', required=True); ap.add_argument('--hidx', type=int, required=True)
ap.add_argument('--depth', type=int, default=6); ap.add_argument('--mode', default='column')
ap.add_argument('--no-base-codegree', action='store_true',
                help='drop the codegree layer duplicated by add_counting, as the census lanes '
                     'already do. NOT a pure deletion: it also shifts every auxiliary by 57,519, '
                     'so the UNSAT implication holds via the substitution v -> v+57519, not by '
                     'clause removal alone (round 27 item 3). Recorded per '
                     'row so a mixed census stays auditable. DEFAULT OFF: the split lane has '
                     'always built the full formula, and flipping it silently would leave rows '
                     'from before and after indistinguishable.')
ap.add_argument('--limit', type=int, default=200000); ap.add_argument('--escalate', type=int, default=3000000)
ap.add_argument('--workers', type=int, default=2); ap.add_argument('--tmp', default='/private/tmp/split_certify')
ap.add_argument('--ledger-dir', default=D); ap.add_argument('--N', type=int, default=22)
ap.add_argument('--child-cache', default=None,
                help='directory holding per-parent child result caches. When set, a child whose '
                     'EXACT formula (cnf_sha256) was already refuted and certified is reused '
                     'instead of re-solved, so a preempted parent resumes instead of restarting '
                     'from zero. Opt-in: unset means behaviour identical to before this existed.')
ap.add_argument('--recurse', type=int, default=2, help='when a child still caps at --escalate, split IT on further variables, up to this many times')
ap.add_argument('--shortfall', action='store_true',
                help='add the Corollary 4.3 pair-shortfall clauses (PROVED; sound, strictly weaker \n                      than the corollary). Changes cnf_sha256, so cached children are NOT reused.')
ap.add_argument('--sub-depth', type=int, default=3, help='extra branch variables per recursion step')
a = ap.parse_args()
os.makedirs(a.tmp, exist_ok=True)
STAMP = 'rooted_encode.py@' + subprocess.run(['git', '-C', HERE, 'rev-parse', '--short', 'HEAD'], capture_output=True, text=True).stdout.strip()
# The commit stamp above is EMPTY on any host that is not a git checkout -- which is every cloud
# box, since they run from a tarball unpack. Split rows carried neither that nor the encoder
# source hashes, so unlike ordinary census rows they recorded no way to tell WHICH encoder built
# the CNF. That has to exist BEFORE a second encoding variant is introduced, or the census becomes
# a mixture nothing can separate afterwards.
ENCODER_SOURCES = {}
for _name in ('rooted_encode', 'typed_encode', 'lemma_encode', 'gen_ramsey'):
    try:
        _m = __import__(_name)
        _f = getattr(_m, '__file__', None)
        if _f:
            ENCODER_SOURCES[os.path.basename(_f)] = hashlib.sha256(open(_f, 'rb').read()).hexdigest()
    except Exception:
        pass

def sha_bytes(b): return hashlib.sha256(b).hexdigest()
def sha_file(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for c in iter(lambda: f.read(1 << 20), b''): h.update(c)
    return h.hexdigest()

g = json.load(open(f'{D}/gen_{a.tag}.json'))
lines = [l.split('#')[0].strip() for l in open(f'{D}/H_{a.tag}.txt')]; lines = [l for l in lines if l]
H = sorted(tuple(int(x) for x in e.split('-')) for e in lines[a.hidx].split(','))
DEG = tuple(g.get('degrees', (8, 9, 10))); degs = [d for d, c in zip(DEG, g['hist']) for _ in range(c)]
comp = {d: n for d, n in zip(DEG, g['composition']) if n}; root = g['root']
hist_s = ','.join(map(str, g['hist'])); comp_s = ','.join(map(str, g['composition']))
cls, nv, com, hedges, Dv = rooted_formula(a.N, ['K2x8', 'K2x5'], degs, root, comp, H=[tuple(e) for e in H],
                                          tight=True, budget=True, channel=True, wallpairs=True, auth=True,
                                          base_codegree=not a.no_base_codegree, shortfall=a.shortfall)
parent_txt = None
eidx = edge_index(a.N)
def blue(i, j): return eidx[(min(i, j), max(i, j))] * 2 + 2
_, ncells, wcells = cells_of(a.N, degs, root, comp)
S = list(range(2, root + 2)); W = [v for (lo, hi, d) in wcells for v in range(lo, hi + 1)]
hdeg = {u: sum(1 for (x, y) in H if u in (x, y)) for u in S}
if a.mode == 'column':
    u0 = min(S, key=lambda u: (hdeg[u], u)); picks = [(u0, w) for w in sorted(W, key=lambda w: (Dv[w - 1], w))[:a.depth]]
elif a.mode == 'row':
    w0 = min(W, key=lambda w: (Dv[w - 1], w)); picks = [(u, w0) for u in sorted(S, key=lambda u: (-hdeg[u], u))[:a.depth]]
else:
    import random; picks = random.Random(20260910).sample([(u, w) for u in S for w in W], a.depth)
bvars = [blue(u, w) for (u, w) in picks]; assert len(set(bvars)) == a.depth
# the reserve: further incidence edges, in the same order, for recursion on a child that will not close
Wrest = [w for w in sorted(W, key=lambda w: (Dv[w - 1], w))]
u0 = min(S, key=lambda u: (hdeg[u], u))
RESERVE = [blue(u, w) for w in Wrest for u in sorted(S, key=lambda u: (hdeg[u], u)) if blue(u, w) not in bvars]
pats = list(itertools.product((1, -1), repeat=a.depth)); assert len({p for p in pats}) == 2 ** a.depth == len(pats)
lock = threading.Lock(); t0 = time.time(); results = []
counter = [0]

def refute(lits, label, depth_left):
    """Refute the parent restricted by `lits`, recursing on further incidence edges if it will not close.
    Coverage composes: at every node all 2^k sign patterns over that node's new variables are present, so the
    disjunction of a node's children is a tautology relative to the node."""
    row = leaf(lits, label)
    if row.get('verdict') != 'CAPPED' or depth_left <= 0: return row
    used = {abs(l) for l in lits}
    nxt = [v for v in RESERVE if v not in used][:a.sub_depth]
    if not nxt: return row
    kids = []
    for signs in itertools.product((1, -1), repeat=len(nxt)):
        kids.append(refute(lits + [s * v for s, v in zip(signs, nxt)],
                           label + '.' + ''.join('1' if s > 0 else '0' for s in signs), depth_left - 1))
    sat = [k for k in kids if k.get('verdict') == 'SAT']
    ok = all(k.get('verdict') == 'UNSAT' for k in kids)
    verdict = 'SAT' if sat else ('UNSAT' if ok else 'CAPPED')       # SAT propagates; it is never folded into CAPPED
    with lock: print(f"  {label}: recursed on {nxt} -> {sum(1 for k in kids if k.get('verdict')=='UNSAT')}/{len(kids)} closed"
                     + ('  *** SAT BELOW ***' if sat else ''), flush=True)
    return dict(child=label, literals=lits, verdict=verdict, recursed=True, sub_vars=nxt,
                sat_model=(sat[0].get('sat_model') if sat else None),
                verified=ok and all(k.get('verified') for k in kids),
                cake_verified=ok and all(k.get('cake_verified') for k in kids),
                secs=round(sum(k.get('secs', 0) for k in kids), 1), children=kids)

# ---------------------------------------------------------------------------------------------
# CHILD CHECKPOINTING
#
# A preempted parent used to restart from zero: split_certify has no resume and start_all.sh opens
# with `rm -rf /opt/work/tmp/p*`. Measured 2026-09-15, tail parents run 11-17 h, so a preemption
# could discard most of a day of correct work, and any parent longer than the gap between
# preemptions could never finish at all.
#
# THE SAFETY ARGUMENT, which is the whole of it. A cached result is reused ONLY when
#   (a) the child's label matches, AND
#   (b) its cnf_sha256 matches the formula just written for this child, AND
#   (c) the cached verdict is UNSAT, AND
#   (d) the cached row carries verified or cake_verified.
# (b) is what makes this sound: cnf_sha256 is the hash of the exact CNF handed to the solver, the
# same hash the ledger records and scripts/referee/verify_row.py checks. If it matches, the cached
# refutation is a refutation OF THIS FORMULA, not of something merely similar. A CAPPED or SAT
# result is never reused -- capped means undecided, and a SAT must always be re-derived and shouted
# about rather than read from a file.
#
# The cache lives beside the persistent work directory, NOT under a.tmp, because tmp is deleted on
# every lane start. Entries are append-only; a corrupt or truncated line is skipped, never guessed.
def _cache_path():
    if not a.child_cache: return None
    os.makedirs(a.child_cache, exist_ok=True)
    return os.path.join(a.child_cache, f'{a.tag}_{a.hidx}.jsonl')


def _cache_load():
    """label -> row, for rows that are safe to reuse."""
    p_ = _cache_path()
    if not p_ or not os.path.exists(p_): return {}
    out = {}
    for line in open(p_):
        try: r = json.loads(line)
        except Exception: continue          # truncated by a mid-write preemption: skip, never guess
        if r.get('verdict') == 'UNSAT' and (r.get('verified') or r.get('cake_verified')) \
           and r.get('child') is not None and r.get('cnf_sha256'):
            out[r['child']] = r
    return out


def _cache_put(row):
    p_ = _cache_path()
    if not p_ or row.get('verdict') != 'UNSAT': return
    if not (row.get('verified') or row.get('cake_verified')): return
    try:
        with lock:
            with open(p_, 'a') as f:
                f.write(json.dumps(row) + '\n'); f.flush(); os.fsync(f.fileno())
    except Exception as exc:
        print(f'WARNING: could not checkpoint child {row.get("child")}: '
              f'{type(exc).__name__}: {exc}', flush=True)


CACHED = _cache_load()

# ---------------------------------------------------------------------------------------------
# CAPPED-NODE CACHE (2026-09-23)
#
# WHY. Only SOLVED children were cached. A retry at a deeper recursion (the row -> row2 ladder, or a
# manual --recurse +1) therefore re-ran every CAPPED node on the path to its unsolved leaves at the
# full budget before it could recurse -- on the same host and the same CNF, certain to cap again.
# Measured 2026-09-23 on 2_14_6_r8_c161#18: its row attempt recursed through 63 capped nodes, so
# row2 spent an estimated 15-20 hours re-proving caps before reaching six pieces that one more
# split level closed in minutes each (tail_experiments/split_bench.jsonl: 8/8 children, <= 1.7M).
#
# THE SAFETY ARGUMENT. A capped status is never a verdict: it only decides that a node is SPLIT,
# and the 2^k children of a split cover the node completely, so the node is refuted exactly when
# every child is. Skipping a solve that would have capped therefore changes nothing a certificate
# rests on. The worst a wrong entry can do is split a node that a solve would have closed -- more
# work, never a wrong answer. An entry is used only when
#   (a) its label matches, (b) its cnf_sha256 matches the CNF just written for this node,
#   (c) it recorded a genuine budget exhaustion -- cadical exit 0 (UNKNOWN) at the escalation
#       budget, never a kill, crash or error -- and (d) that budget is at least the current one.
# ---------------------------------------------------------------------------------------------
def _capcache_path():
    if not a.child_cache: return None
    os.makedirs(a.child_cache, exist_ok=True)
    return os.path.join(a.child_cache, f'{a.tag}_{a.hidx}.capped.jsonl')


def _capcache_load():
    p_ = _capcache_path(); out = {}
    if not p_ or not os.path.exists(p_): return out
    for l in open(p_):
        try: r = json.loads(l)
        except Exception: continue
        if r.get('child') is None or not r.get('cnf_sha256') or r.get('rc') != 0: continue
        out.setdefault(str(r['child']), []).append(r)
    return out


def _capcache_put(row):
    p_ = _capcache_path()
    if not p_ or row.get('rc') != 0 or row.get('limit') != a.escalate: return
    rec = dict(child=row['child'], cnf_sha256=row['cnf_sha256'], rc=0, escalate=a.escalate,
               limit=a.limit, host=os.uname().nodename, utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))
    try:
        with lock:
            with open(p_, 'a') as f:
                f.write(json.dumps(rec) + '\n'); f.flush(); os.fsync(f.fileno())
    except Exception as exc:
        print(f'WARNING: could not record capped node {row.get("child")}: {type(exc).__name__}: {exc}', flush=True)


CAPPED_KNOWN = _capcache_load()
if CAPPED_KNOWN:
    print(f'capped-node cache: {sum(len(v) for v in CAPPED_KNOWN.values())} known cap(s) available to skip', flush=True)
if CACHED:
    print(f'child cache: {len(CACHED)} certified child result(s) available for reuse', flush=True)


def leaf(lits, label):
    with lock: counter[0] += 1; i = counter[0]
    p = f'{a.tmp}/c{i}_{os.getpid()}.cnf'; pr = p + '.lrat'; tr = p + '.trim'
    write(p, cls + [[l] for l in lits], nv, com + [f'c split child of {a.tag} #{a.hidx}; units {lits}'])
    csha = sha_file(p)
    hit = CACHED.get(label)
    if hit is not None and hit.get('cnf_sha256') == csha:
        # Same label AND same formula hash: this exact CNF has already been refuted and certified.
        for f_ in (p, pr, tr):
            try: os.remove(f_)
            except FileNotFoundError: pass
        r2 = dict(hit); r2['restored_from_cache'] = True
        with lock: print(f'  {label}: UNSAT (restored from checkpoint)', flush=True)
        return r2
    for c_ in CAPPED_KNOWN.get(label, ()):
        if c_.get('cnf_sha256') == csha and int(c_.get('escalate') or 0) >= a.escalate:
            for f_ in (p, pr, tr):
                try: os.remove(f_)
                except FileNotFoundError: pass
            with lock: print(f'  {label}: CAPPED (restored from capped checkpoint, budget {c_.get("escalate")})', flush=True)
            return dict(child=label, literals=list(lits), cnf_sha256=csha, rc=0, limit=a.escalate,
                        secs=0.0, verdict='CAPPED', restored_capped=True)
    row = dict(child=label, literals=list(lits), cnf_sha256=csha)
    for lim in (a.limit, a.escalate):
        t1 = time.time()
        r = subprocess.run(['nice', '-n', '8', CAD, '-q', '-c', str(lim), '--lrat', '--binary=true', p, pr], capture_output=True, text=True)
        row.update(rc=r.returncode, secs=round(time.time() - t1, 1), limit=lim)
        if r.returncode == 20: break
        if r.returncode == 10:
            # A satisfying assignment here is a good colouring of K_22: the result that ENDS the census. Round 22 found
            # the old code dropping it (the recursion aggregated everything that was not all-UNSAT into CAPPED, and the
            # model was never saved). Keep it, write it out, and shout.
            row['verdict'] = 'SAT'
            mp = os.path.join(a.ledger_dir, f'SAT_{a.tag}_{a.hidx}_{label}_{int(time.time())}.txt')
            try:
                open(mp, 'w').write(f'c SAT child of {a.tag} #{a.hidx} label {label} units {lits}\n' + r.stdout)
                row['sat_model'] = mp
            except OSError as e: row['sat_model_error'] = str(e)
            with lock: print(f'*** SAT at {label}: model saved to {mp} ***', flush=True)
            return row
    if row['rc'] != 20:
        row['verdict'] = 'CAPPED'
        _capcache_put(row)
        for f_ in (p, pr, tr):
            try: os.remove(f_)
            except FileNotFoundError: pass
        return row
    row['proof_bytes'] = os.path.getsize(pr)
    tt = subprocess.run([TRIM, p, pr, tr, '--ascii'], capture_output=True)
    kk = subprocess.run([CHECK, p, tr], capture_output=True, text=True)
    row['trim_rc'] = tt.returncode; row['check_rc'] = kk.returncode
    row['verified'] = (tt.returncode == 20 and kk.returncode == 0)
    src = tr if row['verified'] else pr
    if os.path.exists(src) and os.path.getsize(src) <= CAKE_MAX:
        ck = subprocess.run([CAKE, p, src], capture_output=True, text=True)
        # a Boolean copied into JSON is an assertion about evidence; require the exit status too (round 22 A2)
        row['cake_rc'] = ck.returncode
        row['cake_verified'] = (ck.returncode == 0 and 's VERIFIED UNSAT' in ck.stdout)
        row['cake_input'] = 'trimmed' if row['verified'] else 'raw'
        row['cake_stdout_sha256'] = hashlib.sha256((ck.stdout or '').encode()).hexdigest()
        row['cake_tail'] = (ck.stdout.strip().splitlines() or [''])[-1][:120]
    else: row['cake_verified'] = False; row['cake_input'] = 'skipped_too_large'
    row['verdict'] = 'UNSAT'
    _cache_put(row)
    for f_ in (p, pr, tr):
        try: os.remove(f_)
        except FileNotFoundError: pass
    with lock: print(f"  {label}: {row['verdict']} {row['secs']}s proof {row['proof_bytes']//10**6}MB cake {row['cake_verified']}", flush=True)
    return row

jobs = [([s_ * v for s_, v in zip(signs, bvars)], ''.join('1' if s_ > 0 else '0' for s_ in signs)) for signs in pats]
with ThreadPoolExecutor(max_workers=a.workers) as ex:
    results = list(ex.map(lambda j: refute(j[0], j[1], a.recurse), jobs))
def walk(rows):
    for r in rows:
        yield r
        for c in (r.get('children') or []): yield from walk([c])
allrows = list(walk(results))
leaves = [r for r in allrows if not r.get('children')]
u = [r for r in results if r.get('verdict') == 'UNSAT']
s = [r for r in allrows if r.get('verdict') == 'SAT']          # anywhere in the tree, not just the top level
cap = [r for r in results if r.get('verdict') == 'CAPPED']
cake = [r for r in leaves if r.get('cake_verified')]
# round 22 A1: "discharged" must mean certified, not merely rc 20. Every LEAF needs an accepted certificate.
certified = all(r.get('cake_verified') or r.get('verified') for r in leaves if r.get('verdict') == 'UNSAT')
ok = (len(u) == len(pats) and not s and certified)
if s:
    print(f"*** SAT FOUND: {len(s)} satisfying child/children; models at "
          f"{[r.get('sat_model') for r in s if r.get('sat_model')]}. This is a colouring of K_22: STOP AND CHECK IT. ***")
    # DURABILITY. A SAT is the one outcome that would end this campaign the other way, and until
    # now it was a print statement. A parent containing a SAT child fails by construction (`ok`
    # requires `not s`), and the ledger row is written only `if ok` -- so a counterexample would
    # have been recorded in NO ledger anywhere, surviving only in a box's stdout log, which is not
    # synced to the repo and does not outlive the box. Write it immediately, to its own file,
    # before anything else can go wrong.
    try:
        with open(f'{a.ledger_dir}/SAT_FOUND.jsonl', 'a') as f:
            for r in s:
                f.write(json.dumps(dict(
                    tag=a.tag, hidx=a.hidx, hist=hist_s, root=root, comp=comp_s,
                    H=[list(e) for e in H], N=a.N, colors=['K2x8', 'K2x5'],
                    child=r.get('child'), literals=r.get('literals'),
                    cnf_sha256=r.get('cnf_sha256'), sat_model=r.get('sat_model'),
                    sat_model_error=r.get('sat_model_error'),
                    depth=a.depth, recurse=a.recurse, sub_depth=a.sub_depth,
                    encoder=STAMP, encoder_sources_sha256=ENCODER_SOURCES,
                    host=os.uname().nodename,
                    found_at_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))) + '\n')
            f.flush(); os.fsync(f.fileno())
        print(f'*** SAT recorded to {a.ledger_dir}/SAT_FOUND.jsonl ***')
    except Exception as exc:
        # Say so loudly; do NOT swallow. Losing this is the worst outcome available.
        print(f'*** CRITICAL: SAT FOUND BUT COULD NOT BE RECORDED: {type(exc).__name__}: {exc} ***')
split = dict(method='rooted_split incidence, recursive', mode=a.mode, depth=a.depth, recurse=a.recurse, sub_depth=a.sub_depth, branch_edges=[list(e) for e in picks],
             branch_vars=bvars, children=len(pats), unsat=len(u), sat=len(s), capped=len(cap), cake_children=len(cake),
             coverage='all 2^depth sign patterns present exactly once (asserted at generation)',
             leaves=len(leaves), leaves_certified=sum(1 for r in leaves if r.get('cake_verified') or r.get('verified')),
             limits=[a.limit, a.escalate], child_rows=results)
# Split rows carried no timestamp at all, while census rows carry started_at_utc/checked_at_utc.
# That is not cosmetic: throughput and ETA are computed by bucketing verified rows by time, so a
# fleet of five busy split boxes measured as "0 verified in the last 24h" -- a stalled fleet and a
# fully working one produce the identical reading (rule 3). Stamped here in the same field names
# the census lane uses, so one query covers both lanes. Rows written before 2026-09-14 have no
# stamp; treat their absence as "unknown", never as "old" or "idle".
_started_at = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime(t0))
row = dict(hist=hist_s, root=root, comp=comp_s, H=[list(e) for e in H], nedges=len(H),
           started_at_utc=_started_at,
           checked_at_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
           rc=20 if ok else 0, secs=round(time.time() - t0, 1), verified=ok and all(r.get('verified') for r in u),
           # Round 31: this compared cake-accepted LEAVES against the BASE pattern count. With
           # recursion there are more leaves than patterns -- a parent with one 8-child expansion has
           # 71 leaves, not 64 -- so 64 cake-accepted leaves out of 71 reported cake_verified TRUE
           # while seven leaves had NO cake acceptance (a false grade-3 claim), and all 71 accepted
           # reported FALSE. Quantify over every UNSAT leaf, as `certified` above and the recursive
           # node at line ~119 already do.
           cake_verified=ok and all(r.get('cake_verified') for r in leaves
                                    if r.get('verdict') == 'UNSAT'), verified_by='split', split=split,
           limit=0, host=os.uname().nodename, pool=False, encoder=STAMP,
           encoding={'budget': True, 'channel': True, 'wallpairs': True, 'auth': True,
                     'shortfall': a.shortfall,
                     'base_codegree': not a.no_base_codegree},
           encoder_sources_sha256=ENCODER_SOURCES,
           cnf_sha256=sha_bytes(('\n'.join(com) + f'\np cnf {nv} {len(cls)}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c in cls)).encode()))
if ok:
    with open(f'{a.ledger_dir}/ledger_{a.tag}.jsonl', 'a') as f: f.write(json.dumps(row) + '\n')
else:
    # A parent that fails is 62-of-64 or 63-of-64 solved: one or two children capped, after 11-17
    # HOURS of work. Until now none of that was recorded -- the row is written only `if ok`, so the
    # identity of the children that actually blocked it survived nowhere but a log line, and the
    # next attempt redoes all 64 from scratch to arrive at the same two. This records the stuck
    # LEAVES (post-recursion, so the genuinely unsolved nodes, not their closed ancestors) so they
    # can be attacked directly with a deeper split or a larger budget.
    #
    # Deliberately a SEPARATE file, never the ledger: a capped leaf is attempt state, not evidence,
    # and the ledger must hold only what was decided (rule 5). Nothing here is counted as progress.
    stuck = [r for r in leaves if r.get('verdict') == 'CAPPED']
    if stuck:
        try:
            with open(f'{a.ledger_dir}/capped_children.jsonl', 'a') as f:
                for r in stuck:
                    f.write(json.dumps(dict(
                        tag=a.tag, hidx=a.hidx, hist=hist_s, root=root, comp=comp_s,
                        H=[list(e) for e in H],
                        # The child row's own field names: `child` is the sign-pattern label,
                        # `literals` the restriction that defines it, `cnf_sha256` the exact
                        # formula. The sha is what makes this record actionable -- a later pass can
                        # rebuild that precise CNF and confirm it is attacking the same thing.
                        child=r.get('child'), literals=r.get('literals'),
                        cnf_sha256=r.get('cnf_sha256'), child_secs=r.get('secs'),
                        child_rc=r.get('rc'), child_limit=r.get('limit'),
                        parent_secs=round(time.time() - t0, 1),
                        parent_children=len(pats), parent_unsat=len(u), parent_capped=len(cap),
                        depth=a.depth, recurse=a.recurse, sub_depth=a.sub_depth,
                        limits=[a.limit, a.escalate],
                        host=os.uname().nodename,
                        recorded_at_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))) + '\n')
            print(f'recorded {len(stuck)} capped leaf/leaves to capped_children.jsonl')
        except Exception as exc:
            # Never let bookkeeping turn a failed parent into a crashed one.
            print(f'WARNING: could not record capped leaves: {type(exc).__name__}: {exc}')
print(json.dumps({k: row[k] for k in ('hist', 'root', 'comp', 'rc', 'secs', 'verified', 'cake_verified')} |
                 {k: split[k] for k in ('children', 'unsat', 'sat', 'capped', 'cake_children')}))
print('PARENT DISCHARGED' if ok else 'PARENT NOT DISCHARGED (no ledger row written)')
