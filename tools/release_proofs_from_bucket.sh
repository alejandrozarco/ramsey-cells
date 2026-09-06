#!/bin/bash
# Like release_proofs.sh, but the archived .xz proofs live in a GCS bucket prefix (too large for a laptop
# disk): pull them in <=1.9 GB batches, tar each batch, upload it as a release asset, delete it, repeat.
# usage: release_proofs_from_bucket.sh <cell-tag> <gs://bucket/prefix> <local manifest.jsonl> <cert-dir> <tag-name>
set -eu
CELL=$1; BKT=$2; MAN=$3; CERT=$4; TAG=$5; REPO=alejandrozarco/ramsey-cells
W=$(mktemp -d); echo "work $W"
python3 - "$MAN" <<'PY'
import json,sys
rows=[json.loads(l) for l in open(sys.argv[1]) if l.strip()]
ok=[r for r in rows if r.get('result')=='UNSAT' and r.get('trim_rc')==20 and r.get('lrat_check_rc')==0 and r.get('cake')=='VERIFIED' and r.get('xz_bytes')]
print('fully checked leaves with archived proofs:', len(ok), 'of', len(rows)); assert len(ok)==len(rows), 'archive incomplete or a leaf failed'
PY
cp "$MAN" "$W/manifest.jsonl"; cp "$CERT/base_encoder.cnf" "$CERT/prefixes.tsv" "$CERT/negcubes.cnf" "$W/" 2>/dev/null || true
xz -T4 -6 -k -f "$W/base_encoder.cnf" "$W/prefixes.tsv" "$W/negcubes.cnf" 2>/dev/null || true
gsutil ls -l "$BKT/leaf_*.lrat.xz" | awk '$3 ~ /leaf_/ {print $1, $3}' | sed 's#gs://.*/##' | sort -t_ -k2 -n > "$W/sizes.txt"
NF=$(wc -l < "$W/sizes.txt"); echo "bucket files: $NF"
python3 - "$W/sizes.txt" "$W" <<'PY'
import sys
lines=[l.split() for l in open(sys.argv[1])]; W=sys.argv[2]; LIM=1_900_000_000
chunks=[]; cur=[]; size=0
for sz,name in lines:
    sz=int(sz)
    if cur and size+sz>LIM: chunks.append(cur); cur=[]; size=0
    cur.append(name); size+=sz
if cur: chunks.append(cur)
for k,ch in enumerate(chunks): open(f'{W}/chunk{k:02d}.txt','w').write('\n'.join(ch)+'\n')
open(f'{W}/nchunks','w').write(str(len(chunks))); print('chunks', len(chunks))
PY
N=$(cat "$W/nchunks")
NOTES="Archived LRAT proofs for every leaf of the $CELL refutation (tools/proof_archive.py): each leaf re-solved with CaDiCaL --lrat, trimmed with lrat-trim (rc 20), checked again with lrat-check (rc 0) and cake_lpr (s VERIFIED UNSAT), xz-compressed. manifest.jsonl records per leaf the sha256 of the leaf CNF, of the trimmed proof and of the .xz. Leaf i is prefixes.tsv line i (| as newline) followed by base_encoder.cnf minus its header, as tools/cert_pass.py builds it. Parts are plain tars of leaf_<i>.lrat.xz files. Unconfirmed, not peer reviewed; the mathematical claim lives in the cell's README, not here."
gh release create "$TAG" --repo $REPO --title "Leaf proofs: $CELL" --notes "$NOTES" "$W/manifest.jsonl" $(ls "$W"/*.xz 2>/dev/null) 2>&1 | tail -1
: > "$W/SHA256SUMS.txt"; sha256sum "$W/manifest.jsonl" >> "$W/SHA256SUMS.txt"; for f in "$W"/*.xz; do sha256sum "$f" >> "$W/SHA256SUMS.txt"; done
for k in $(seq 0 $((N-1))); do
  kk=$(printf %02d $k); D="$W/batch$kk"; mkdir -p "$D"
  sed "s#^#$BKT/#" "$W/chunk$kk.txt" > "$W/urls$kk.txt"
  cat "$W/urls$kk.txt" | gsutil -q -m cp -I "$D/" 
  got=$(ls "$D" | wc -l | tr -d ' '); want=$(wc -l < "$W/chunk$kk.txt" | tr -d ' '); [ "$got" = "$want" ] || { echo "batch $kk: got $got of $want"; exit 1; }
  tar -cf "$W/proofs_part$kk.tar" -C "$D" $(cat "$W/chunk$kk.txt"); rm -rf "$D"
  sha256sum "$W/proofs_part$kk.tar" >> "$W/SHA256SUMS.txt"
  gh release upload "$TAG" --repo $REPO "$W/proofs_part$kk.tar" 2>&1 | tail -1; rm -f "$W/proofs_part$kk.tar"
  echo "part $kk uploaded ($got files)"
done
sed -i '' "s#$W/##" "$W/SHA256SUMS.txt" 2>/dev/null || sed -i "s#$W/##" "$W/SHA256SUMS.txt"
gh release upload "$TAG" --repo $REPO "$W/SHA256SUMS.txt" 2>&1 | tail -1
gh release view "$TAG" --repo $REPO --json assets --jq '.assets[] | "\(.name) \(.size)"'
echo "RELEASE DONE $TAG"
