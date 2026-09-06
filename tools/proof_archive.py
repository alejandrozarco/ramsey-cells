#!/usr/bin/env python3
"""proof_archive.py: re-solve every leaf of a certificate directory and KEEP its proof.
For each leaf (prefix ++ base body, exactly as tools/cert_pass.py builds it): solve with CaDiCaL
--lrat, trim with lrat-trim (rc 20 = checked UNSAT), check the trimmed proof with lrat-check
(rc 0) and with cake_lpr ('s VERIFIED UNSAT'), then xz-compress the trimmed LRAT into
<ARCHIVE>/leaf_<i>.lrat.xz and record {leaf, sha256 (leaf CNF), trim_sha256, xz_sha256, sizes,
verdicts} in <ARCHIVE>/manifest.jsonl. Resumable: leaves already in the manifest are skipped.
Env: CADICAL, LRAT_TRIM, LRAT_CHECK, CAKE_LPR (paths), WORKERS, WORKDIR (cert dir with
base_encoder.cnf + prefixes.tsv), ARCHIVE (output dir).
A third party checks an archived proof with:  xz -d leaf_i.lrat.xz; cake_lpr leaf_i.cnf leaf_i.lrat
where leaf_i.cnf is rebuilt from prefixes.tsv line i and base_encoder.cnf (see cert_pass.py)."""
import os, sys, json, hashlib, subprocess, time
from concurrent.futures import ThreadPoolExecutor
E = os.environ.get
CAD, TRIM, CHECK, CAKE = E('CADICAL','cadical'), E('LRAT_TRIM','lrat-trim'), E('LRAT_CHECK','lrat-check'), E('CAKE_LPR','cake_lpr')
W = int(E('WORKERS','2')); D = E('WORKDIR','.'); A = E('ARCHIVE', os.path.join(D, 'archive'))
os.makedirs(A, exist_ok=True)
body = open(f'{D}/base_encoder.cnf').read().split('\n',1)[1]
pref = [l.rstrip('\n').split('\t') for l in open(f'{D}/prefixes.tsv')]
man = f'{A}/manifest.jsonl'; done = set()
if os.path.exists(man):
    for l in open(man):
        if l.strip(): done.add(str(json.loads(l)['leaf']))
out = open(man, 'a')
def sha(p):
    h = hashlib.sha256()
    with open(p,'rb') as f:
        for b in iter(lambda: f.read(1<<20), b''): h.update(b)
    return h.hexdigest()
def one(item):
    i, p = item
    if i in done: return None
    text = p.replace('|','\n') + body; s = hashlib.sha256(text.encode()).hexdigest()
    cnf, lrat, trim = f'{D}/arch_{i}.cnf', f'{D}/arch_{i}.lrat', f'{D}/arch_{i}.trim.lrat'
    open(cnf,'w').write(text); t0 = time.time()
    r = subprocess.run([CAD,'-q','--lrat','--binary=false',cnf,lrat], capture_output=True, text=True)
    res = 'UNSAT' if r.returncode == 20 else ('SAT' if r.returncode == 10 else f'rc{r.returncode}')
    row = {'leaf': i, 'sha256': s, 'result': res, 'solve_secs': round(time.time()-t0,1), 'raw_bytes': os.path.getsize(lrat) if os.path.exists(lrat) else 0}
    if res == 'UNSAT':
        t = subprocess.run([TRIM, cnf, lrat, trim, '--ascii'], capture_output=True, text=True)
        row['trim_rc'] = t.returncode
        if t.returncode == 20 and os.path.exists(trim):
            c = subprocess.run([CHECK, cnf, trim], capture_output=True, text=True); row['lrat_check_rc'] = c.returncode
            k = subprocess.run([CAKE, cnf, trim], capture_output=True, text=True); row['cake'] = 'VERIFIED' if 's VERIFIED UNSAT' in k.stdout else 'FAIL'
            row['trim_bytes'] = os.path.getsize(trim); row['trim_sha256'] = sha(trim)
            xz = f'{A}/leaf_{i}.lrat.xz'; tmp = xz + '.tmp'   # written under a temp name so a concurrent
            subprocess.run(['xz','-T2','-4','-f','-c',trim], stdout=open(tmp,'wb'), check=True)  # sync loop moving *.xz away
            row['xz_bytes'] = os.path.getsize(tmp); row['xz_sha256'] = sha(tmp)                    # cannot race the hashing
            os.replace(tmp, xz)
    for f in (cnf, lrat, trim):
        if os.path.exists(f): os.remove(f)
    out.write(json.dumps(row)+'\n'); out.flush(); return row
with ThreadPoolExecutor(W) as ex:
    n = 0
    for r in ex.map(one, pref):
        if r: n += 1
rows = [json.loads(l) for l in open(man) if l.strip()]
ok = sum(1 for r in rows if r.get('result')=='UNSAT' and r.get('trim_rc')==20 and r.get('lrat_check_rc')==0 and r.get('cake')=='VERIFIED')
print(f'SUMMARY archive: {len(rows)} leaves in manifest, {ok} fully checked (solve+trim+lrat-check+cake_lpr), {sum(r.get("xz_bytes",0) for r in rows)/1e9:.2f} GB of xz proofs')
print('=== ARCHIVE DONE ===')
