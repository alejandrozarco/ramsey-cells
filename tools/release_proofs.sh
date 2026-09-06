#!/bin/bash
# Bundle an archived proof directory (from tools/proof_archive.py) into <=1.9 GB tar chunks with a
# manifest and the inputs needed to rebuild every leaf, and attach them to a GitHub release of this
# repository.  usage: release_proofs.sh <cell-tag> <archive-dir> <cert-dir with base_encoder.cnf + prefixes.tsv> <tag-name>
set -eu
CELL=$1; A=$2; CERT=$3; TAG=$4; REPO=alejandrozarco/ramsey-cells
W=$(mktemp -d); echo "work $W"
N=$(grep -c . "$A/manifest.jsonl"); echo "manifest rows $N"
python3 - "$A/manifest.jsonl" <<'PY'
import json,sys
rows=[json.loads(l) for l in open(sys.argv[1]) if l.strip()]
ok=[r for r in rows if r.get('result')=='UNSAT' and r.get('trim_rc')==20 and r.get('lrat_check_rc')==0 and r.get('cake')=='VERIFIED' and r.get('xz_bytes')]
print('fully checked leaves with archived proofs:', len(ok), 'of', len(rows))
assert len(ok)==len(rows), 'archive incomplete or a leaf failed'
PY
cp "$A/manifest.jsonl" "$CERT/base_encoder.cnf" "$CERT/prefixes.tsv" "$CERT/negcubes.cnf" "$W/" 2>/dev/null || true
xz -T4 -6 -k -f "$W/base_encoder.cnf" "$W/prefixes.tsv" "$W/negcubes.cnf" 2>/dev/null || true
# chunk the .xz proofs into tars of at most 1.9 GB (GitHub's per-asset limit is 2 GB)
cd "$A"; ls leaf_*.lrat.xz | sort -t_ -k2 -n > "$W/files.txt"
python3 - "$W/files.txt" "$A" "$W" <<'PY'
import os,sys,subprocess
files=[l.strip() for l in open(sys.argv[1])]; A=sys.argv[2]; W=sys.argv[3]
LIM=1_900_000_000; chunks=[]; cur=[]; size=0
for f in files:
    sz=os.path.getsize(os.path.join(A,f))
    if cur and size+sz>LIM: chunks.append(cur); cur=[]; size=0
    cur.append(f); size+=sz
if cur: chunks.append(cur)
for k,ch in enumerate(chunks):
    lst=os.path.join(W,f'chunk{k}.txt'); open(lst,'w').write('\n'.join(ch)+'\n')
    out=os.path.join(W,f'proofs_part{k:02d}.tar')
    subprocess.run(['tar','-cf',out,'-C',A,'-T',lst],check=True)
    print(f'chunk {k}: {len(ch)} files, {os.path.getsize(out)/1e9:.2f} GB')
open(os.path.join(W,'nchunks'),'w').write(str(len(chunks)))
PY
cd "$W"; sha256sum proofs_part*.tar manifest.jsonl *.xz > SHA256SUMS.txt; cat SHA256SUMS.txt
NOTES="Archived LRAT proofs for every leaf of the $CELL refutation (tools/proof_archive.py): each leaf re-solved with CaDiCaL --lrat, the proof trimmed with lrat-trim (rc 20), checked again with lrat-check (rc 0) and with cake_lpr (s VERIFIED UNSAT), then xz-compressed. manifest.jsonl records per leaf the sha256 of the leaf CNF, of the trimmed proof and of the .xz. Leaf i is prefixes.tsv line i (with | as newline) followed by base_encoder.cnf minus its header, exactly as tools/cert_pass.py builds it. Unconfirmed, not peer reviewed; the mathematical claim lives in the repository README of the cell, not here."
gh release create "$TAG" --repo $REPO --title "Leaf proofs: $CELL" --notes "$NOTES" proofs_part*.tar manifest.jsonl SHA256SUMS.txt $(ls *.xz 2>/dev/null) 2>&1 | tail -3
gh release view "$TAG" --repo $REPO --json assets --jq '.assets[] | "\(.name) \(.size)"'
echo "RELEASE DONE $TAG"
