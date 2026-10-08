#!/usr/bin/env python3
"""M5 step 3: bind every attached cube of the Lean table to its ledger hash.

1. rows_ser.txt (written by SerRows.lean from the Lean constant SB.Rooted.M5.rows) must equal, line for
   line, the serialisation of cube_table.jsonl in table order: the Lean data are the table.
2. The printer `m5-print` (lean-sb, compiled; LRATCatcher.Rooted.writeDimacs) takes the lines of
   rows_ser.txt as jobs, echoes Row.ser of the row it parsed (must equal the job text), and prints the
   cube's DIMACS file (direct) or every leaf file (split). Each file's sha256 must equal the recorded
   cnf_sha256 of the ledger row (direct) or of the leaf node (split). Files are hashed as they appear and
   deleted at once.
Rows whose (serialisation, expected hashes) were already verified in an earlier verify_*.jsonl are skipped,
so a merge of new M6 rows only prints the changed rows.
Output: verify_<stamp>.jsonl (one line per row), summary on stdout.
usage: m5_verify.py [--workers 3] [--tmp DIR] [--limit N] [--only-kind direct|split] [--sample N]"""
import argparse, collections, glob, hashlib, json, os, random, subprocess, sys, tempfile, threading, time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
LEANSB = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', 'lean', 'sbsound'))
EXE = os.path.join(LEANSB, '.lake', 'build', 'bin', 'm5-print')
OPTN = {'O1': '1', 'O2': '2', 'O3': '3'}


def ser(r):
    n8, n9, n10, v8, v9, v10 = r['key']
    H = ','.join(f'{a}-{b}' for a, b in r['H'])
    if r['kind'] == 'direct': v = 'D'
    elif r['kind'] == 'pending': v = 'P'
    else: v = f"S;{r['childof']};{r['fuel']};" + '/'.join(','.join(map(str, u)) for u, _ in r['leaves'])
    return f'{n8},{n9},{n10},{v8},{v9},{v10}|{H}|{OPTN[r["opt"]]}|{v}'


def expected(r):
    if r['kind'] == 'direct': return {'-': r['sha']}
    if r['kind'] == 'split': return {str(j): h for j, (_, h) in enumerate(r['leaves'])}
    return {}


def sha_file(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for c in iter(lambda: f.read(1 << 20), b''): h.update(c)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workers', type=int, default=3); ap.add_argument('--tmp', default=None)
    ap.add_argument('--limit', type=int, default=0); ap.add_argument('--only-kind', default=None)
    ap.add_argument('--sample', type=int, default=0); ap.add_argument('--seed', type=int, default=20261007)
    ap.add_argument('--ser', default=os.path.join(HERE, 'rows_ser.txt'))
    a = ap.parse_args()
    keys = json.load(open(os.path.join(HERE, 'cases.json')))
    tab = collections.defaultdict(list)
    for l in open(os.path.join(HERE, 'cube_table.jsonl')):
        r = json.loads(l); tab[r['tag']].append(r)
    table = [r for t in sorted(keys) for r in sorted(tab[t], key=lambda r: r['widx'])]
    lean = [l.rstrip('\n').split('\t', 1) for l in open(a.ser)]
    assert len(lean) == len(table), (len(lean), len(table))
    bad = [i for i, (r, (li, ls)) in enumerate(zip(table, lean)) if int(li) != i or ls != ser(r)]
    print(f'step 1: {len(table)} rows; Lean serialisation == table serialisation: {len(table) - len(bad)} / {len(table)}', flush=True)
    if bad:
        print('  first mismatches:', bad[:10]); sys.exit(1)
    done = {}
    for f in sorted(glob.glob(os.path.join(HERE, 'verify_*.jsonl'))):
        for l in open(f):
            v = json.loads(l)
            if v.get('verdict') == 'BOUND': done[v['ser_sha256']] = v
    todo = []
    for i, r in enumerate(table):
        if r['kind'] == 'pending': continue
        if a.only_kind and r['kind'] != a.only_kind: continue
        s = ser(r); k = hashlib.sha256((s + json.dumps(expected(r), sort_keys=True)).encode()).hexdigest()
        if k in done: continue
        todo.append((i, r, s, k))
    if a.sample:
        random.Random(a.seed).shuffle(todo); todo = sorted(todo[:a.sample], key=lambda x: x[0])
    if a.limit: todo = todo[:a.limit]
    nfiles = sum(len(expected(r)) for _, r, _, _ in todo)
    print(f'step 2: {len(todo)} rows to print ({nfiles} files); {len(done)} bound earlier', flush=True)
    tmp = a.tmp or tempfile.mkdtemp(prefix='m5v_')
    os.makedirs(tmp, exist_ok=True)
    stamp = time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())
    log = open(os.path.join(HERE, f'verify_{stamp}.jsonl'), 'w')
    lock = threading.Lock(); tally = collections.Counter(); t0 = time.time(); nf = [0]

    def batch(items):
        sub = tempfile.mkdtemp(dir=tmp)
        p = subprocess.Popen(['taskpolicy', '-b', 'nice', '-n', '19', EXE, sub, '-'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        p.stdin.write(''.join(f'{i}\t{s}\n' for i, _, s, _ in items)); p.stdin.close()
        got = collections.defaultdict(dict); sers = {}; errs = collections.defaultdict(list)
        for L in p.stdout:
            f = L.rstrip('\n').split('\t')
            if f[0] == 'SER': sers[int(f[1])] = f[2]
            elif f[0] == 'OK':
                h = sha_file(f[3]); os.unlink(f[3]); got[int(f[1])][f[2]] = h
                with lock: nf[0] += 1
            else: errs[f[1]].append(L.strip())
        p.wait()
        try: os.rmdir(sub)
        except OSError: pass
        out = []
        for i, r, s, k in items:
            exp = expected(r); g = got.get(i, {})
            miss = sorted(j for j in exp if g.get(j) != exp[j])
            ok = sers.get(i) == s and not miss and not errs.get(str(i)) and len(g) == len(exp)
            out.append(dict(i=i, tag=r['tag'], hidx=r['hidx'], widx=r['widx'], kind=r['kind'], opt=r['opt'],
                            src=r['src'], files=len(exp), matched=len(exp) - len(miss), ser_echo=sers.get(i) == s,
                            mismatched=miss[:20], errors=errs.get(str(i), [])[:3], ser_sha256=k,
                            verdict='BOUND' if ok else 'NOT_BOUND'))
        return out

    batches = []; cur = []; w = 0
    for it in todo:
        c = len(expected(it[1]))
        if cur and w + c > 40: batches.append(cur); cur = []; w = 0
        cur.append(it); w += c
    if cur: batches.append(cur)
    with ThreadPoolExecutor(a.workers) as ex:
        for res in ex.map(batch, batches):
            with lock:
                for v in res:
                    tally[v['verdict']] += 1; tally[f"{v['verdict']} {v['kind']}"] += 1
                    log.write(json.dumps(v) + '\n')
                    if v['verdict'] != 'BOUND': print('  !!', json.dumps(v)[:400], flush=True)
                log.flush()
                n = sum(v for k, v in tally.items() if ' ' not in k)
                if n % 200 < len(res) or n == len(todo):
                    print(f'  {n}/{len(todo)} rows, {nf[0]} files, {int(time.time() - t0)} s, {dict(tally)}', flush=True)
    print(f'done -> {log.name}: {dict(tally)}')
    sys.exit(0 if tally.get('NOT_BOUND', 0) == 0 else 1)


if __name__ == '__main__':
    main()
