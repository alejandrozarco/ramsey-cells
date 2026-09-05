"""Audit the pinned deposit. Does not re-solve its large UNSAT searches."""
import collections, hashlib, importlib.util, json, pathlib, subprocess, sys
root = pathlib.Path(sys.argv[1]).resolve()
out = pathlib.Path(sys.argv[2]).resolve()
out.mkdir(parents=True, exist_ok=True)
def sha(data): return hashlib.sha256(data).hexdigest()
def cubes(path):
    result=[]
    for l in path.read_text().splitlines():
        if l.startswith('a '):
            q=list(map(int,l.split()[1:])); assert q[-1]==0 and 0 not in q[:-1]
            assert not (set(q[:-1]) & {-x for x in q[:-1]})
            result.append(q[:-1])
    return result
def dimacs(cs, nv=None):
    if nv is None: nv=max((abs(x) for c in cs for x in c), default=0)
    return f'p cnf {nv} {len(cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs)
encpath=root/'k34k33-n19/tools/gen_ramsey.py'
spec=importlib.util.spec_from_file_location('deposit_encoder',encpath)
enc=importlib.util.module_from_spec(spec);spec.loader.exec_module(enc)
summary={}
configs=[('k34k33-n19',19,['K3x4','K3x3'],'instance/k34k33_n19_d10.icnf','certificate/k34k33_cakelpr_encoder_ledger.jsonl'),('k35k24-n19',19,['K3x5','K2x4'],'certificate/k35k24_n19_flat.icnf','certificate/k35k24_cakelpr_encoder_ledger.jsonl'),('k35k25-n22',22,['K3x5','K2x5'],'tree/k35k25_n22_flat.icnf','certificate/cake_lpr_ledger_IN_PROGRESS.jsonl')]
for name,n,graphs,flat,ledger in configs:
    d=root/name; cs,nv,comments=enc.build(n,graphs,vertex_lex=True)
    body=''.join(' '.join(map(str,c))+' 0\n' for c in cs)
    (out/(name+'.cnf')).write_text(dimacs(cs,nv))
    shipped=list((d/'instance').glob('*.cnf')) if (d/'instance').exists() else []
    same={}
    for p in shipped:
        lines=p.read_text().splitlines(); actual=[list(map(int,l.split()[:-1])) for l in lines if l and l[0] not in 'cp']
        same[p.name]=actual==cs
    cc=cubes(d/flat)
    cover=dimacs([[-x for x in c] for c in cc])
    (out/(name+'-negcubes.cnf')).write_text(cover)
    rows=[json.loads(l) for l in (d/ledger).read_text().splitlines() if l.strip()]
    ids=[str(r['leaf']) for r in rows]
    expected={str(i) for i in range(len(cc))}|{'cover'}
    mismatches=[]
    for r in rows:
        if str(r['leaf'])=='cover': text=cover
        else:
            cube=cc[int(r['leaf'])]
            text=f'p cnf {nv} {len(cs)+len(cube)}\n'+''.join(f'{x} 0\n' for x in cube)+body
        if sha(text.encode())!=r['sha256']: mismatches.append(r['leaf'])
    first=f'p cnf {nv} {len(cs)+len(cc[0])}\n'+''.join(f'{x} 0\n' for x in cc[0])+body
    (out/(name+'-leaf0.cnf')).write_text(first)
    summary[name]={'variables':nv,'clauses':len(cs),'shipped_clause_body_matches':same,'cubes':len(cc),'ledger_rows':len(rows),'unique_leaf_ids':len(set(ids)),'missing_ids_count':len(expected-set(ids)),'extra_ids':sorted(set(ids)-expected),'duplicate_ids':len(ids)-len(set(ids)),'solver_verdicts':dict(collections.Counter(r['result'] for r in rows)),'checker_verdicts':dict(collections.Counter(r['cake'] for r in rows)),'cover_recorded':'cover' in ids,'hash_mismatches':mismatches[:20],'hash_mismatch_count':len(mismatches)}
    if name=='k35k25-n22':
        led={r['id']:r for r in map(json.loads,(d/'tree/ledger.jsonl').read_text().splitlines())}
        vset={r['id'] for r in map(json.loads,(d/'tree/verified_leaves.jsonl').read_text().splitlines()) if r.get('verified')}
        splits={p.name.split('_d')[0]:p for p in (d/'tree/splits').glob('*.icnf')}
        leaves=[];gaps=[];unverified=[];sat=[]
        def walk(cid,lits):
            r=led.get(cid,{})
            if r.get('result')=='UNSAT':
                leaves.append(lits)
                if not (r.get('verified') or cid in vset):unverified.append(cid)
            elif r.get('result')=='SAT':sat.append(cid)
            elif cid not in splits:gaps.append(cid)
            else:
                children=cubes(splits[cid])
                if not children:walk(cid+'.solo',lits)
                for j,c in enumerate(children):walk(cid+'.'+str(j),lits+c)
        for i,c in enumerate(cubes(d/'instance/k35k25_n22_d10.icnf')):walk(str(i),c)
        summary[name]['tree_audit']={'leaves':len(leaves),'gaps':gaps,'unverified':unverified,'sat':sat,'flat_matches_tree_exactly':leaves==cc}
print(json.dumps(summary,indent=2))
