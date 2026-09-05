#!/usr/bin/env python3
"""Streaming discharge pass: for every leaf of a flat cover, reconstruct the Lean-printed DIMACS
(prefix ++ base body), solve with proof, check with cake_lpr, record {leaf, sha256, verdicts},
delete the files. Then the cover CNF. Runs anywhere with cadical + cake_lpr on PATH-like paths."""
import subprocess, hashlib, json, os, sys, time
from concurrent.futures import ThreadPoolExecutor
import threading
CHECK_SEM = threading.Semaphore(int(os.environ.get('CHECKERS','3')))   # cake_lpr on ~0.5 GB proofs needs GBs; 16 at once OOM-killed on 16 GB
CAKE_ENV = dict(os.environ, CML_HEAP_SIZE=os.environ.get('CML_HEAP_SIZE','4000'), CML_STACK_SIZE=os.environ.get('CML_STACK_SIZE','1000'))
CAD, CAKE = os.environ.get('CADICAL','cadical'), os.environ.get('CAKE_LPR','cake_lpr')
W = int(os.environ.get('WORKERS', os.cpu_count())); D = os.environ.get('WORKDIR','.')
body = open(f'{D}/base_encoder.cnf').read().split('\n',1)[1]
pref = [l.rstrip('\n').split('\t') for l in open(f'{D}/prefixes.tsv')]
led = open(f'{D}/cert_ledger.jsonl','a'); done = set()
if os.path.getsize(f'{D}/cert_ledger.jsonl'):
    for l in open(f'{D}/cert_ledger.jsonl'):
        try:
            r=json.loads(l)
            if str(r.get('cake','')).startswith('VERIFIED'): done.add(str(r['leaf']))   # FAIL rows are re-done
        except Exception: pass
def one(item):
    i, p = item
    if i in done: return None
    text = p.replace('|','\n') + body; sha = hashlib.sha256(text.encode()).hexdigest()
    cnf, lrat = f'{D}/leaf_{i}.cnf', f'{D}/leaf_{i}.lrat'; open(cnf,'w').write(text); t0=time.time()
    r = subprocess.run([CAD,'-q','--lrat','--binary=false',cnf,lrat],capture_output=True,text=True)
    res = 'UNSAT' if 's UNSATISFIABLE' in r.stdout else ('SAT' if 's SATISFIABLE' in r.stdout else f'ERR{r.returncode}')
    t1=time.time()
    with CHECK_SEM: c = subprocess.run([CAKE,cnf,lrat],capture_output=True,text=True,env=CAKE_ENV)
    cake = 'VERIFIED' if 's VERIFIED UNSAT' in c.stdout else f'FAIL:rc{c.returncode}:{(c.stdout+c.stderr).strip()[-60:]}'
    row = {'leaf':i,'sha256':sha,'result':res,'solve_secs':round(t1-t0,1),'cake':cake,'cake_secs':round(time.time()-t1,1),'lrat_bytes':os.path.getsize(lrat) if os.path.exists(lrat) else 0}
    for f in (cnf,lrat):
        if os.path.exists(f): os.remove(f)
    led.write(json.dumps(row)+'\n'); led.flush(); return row
with ThreadPoolExecutor(max_workers=W) as ex:
    rows=[r for r in ex.map(one, pref) if r]
from collections import Counter
print("SUMMARY leaves this run:", dict(Counter(r['result'] for r in rows)), "| cake_lpr:", dict(Counter(r['cake'].split(':')[0] for r in rows)), flush=True)
if 'cover' not in done:
    cnf=f'{D}/negcubes.cnf'; lrat=f'{D}/negcubes.lrat'; sha=hashlib.sha256(open(cnf,'rb').read()).hexdigest()
    r=subprocess.run([CAD,'-q','--lrat','--binary=false',cnf,lrat],capture_output=True,text=True); c=subprocess.run([CAKE,cnf,lrat],capture_output=True,text=True,env=CAKE_ENV)
    led.write(json.dumps({'leaf':'cover','sha256':sha,'result':'UNSAT' if 's UNSATISFIABLE' in r.stdout else r.stdout[:20],'cake':'VERIFIED' if 's VERIFIED UNSAT' in c.stdout else 'FAIL'})+'\n'); led.flush()
    print("SUMMARY cover:", 'VERIFIED' if 's VERIFIED UNSAT' in c.stdout else 'FAIL', flush=True)
print("=== CERT PASS DONE ===", flush=True)
