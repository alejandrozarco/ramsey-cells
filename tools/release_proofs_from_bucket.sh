#!/bin/bash
# Bundle a bucket-staged proof archive (tools/proof_archive.py output) into <=1.9 GB release parts without
# holding it all on disk. The MANIFEST is authoritative: the parts contain exactly leaf_<id>.lrat.xz for its
# rows (sizes from its xz_bytes). Resumable: an existing release is reused, parts already attached are skipped.
# usage: release_proofs_from_bucket.sh <cell-tag> <gs://bucket/prefix> <manifest.jsonl> <cert-dir> <tag-name>
set -eu
CELL=$1; BKT=$2; MAN=$3; CERT=$4; TAG=$5; REPO=alejandrozarco/ramsey-cells
W=${WORKDIR:-$(mktemp -d)}; mkdir -p "$W"; echo "work $W"
python3 - "$MAN" "$W" "$BKT" <<'PY'
import json,sys,subprocess,os
man,W,BKT=sys.argv[1:4]
rows=[json.loads(l) for l in open(man) if l.strip()]
ok=[r for r in rows if r.get('result')=='UNSAT' and r.get('trim_rc')==20 and r.get('lrat_check_rc')==0 and r.get('cake')=='VERIFIED' and r.get('xz_bytes')]
print('fully checked leaves with archived proofs:', len(ok), 'of', len(rows)); assert len(ok)==len(rows), 'archive incomplete or a leaf failed'
names=[f"leaf_{r['leaf']}.lrat.xz" for r in rows]; assert len(set(names))==len(names), 'duplicate leaf ids'
have=set(l.strip().rsplit('/',1)[-1] for l in subprocess.run(['gsutil','ls',BKT+'/'],capture_output=True,text=True).stdout.splitlines() if l.strip())
missing=[n for n in names if n not in have]; assert not missing, f'missing in bucket: {missing[:5]}'
LIM=1_900_000_000; chunks=[]; cur=[]; size=0
for r,n in zip(rows,names):
    sz=int(r['xz_bytes'])
    if cur and size+sz>LIM: chunks.append(cur); cur=[]; size=0
    cur.append(n); size+=sz
if cur: chunks.append(cur)
for k,ch in enumerate(chunks): open(f'{W}/chunk{k:02d}.txt','w').write('\n'.join(ch)+'\n')
open(f'{W}/nchunks','w').write(str(len(chunks))); print('chunks', len(chunks), 'files', len(names))
PY
N=$(cat "$W/nchunks")
cp "$MAN" "$W/manifest.jsonl"; cp "$CERT/base_encoder.cnf" "$CERT/prefixes.tsv" "$CERT/negcubes.cnf" "$W/" 2>/dev/null || true
for f in base_encoder.cnf prefixes.tsv negcubes.cnf; do [ -f "$W/$f" ] && [ ! -f "$W/$f.xz" ] && xz -T4 -6 -k -f "$W/$f"; done
NOTES="Archived LRAT proofs for every leaf of the $CELL refutation (tools/proof_archive.py): each leaf re-solved with CaDiCaL --lrat, trimmed with lrat-trim (rc 20), checked again with lrat-check (rc 0) and cake_lpr (s VERIFIED UNSAT), xz-compressed. manifest.jsonl records per leaf the sha256 of the leaf CNF, of the trimmed proof and of the .xz. Leaf i is prefixes.tsv line i (| as newline) followed by base_encoder.cnf minus its header, as tools/cert_pass.py builds it. Parts are plain tars of leaf_<i>.lrat.xz files. Unconfirmed, not peer reviewed; the mathematical claim lives in the cell's README, not here."
if gh release view "$TAG" --repo $REPO >/dev/null 2>&1; then echo "release $TAG exists; resuming"; else gh release create "$TAG" --repo $REPO --title "Leaf proofs: $CELL" --notes "$NOTES" "$W/manifest.jsonl" $(ls "$W"/*.xz 2>/dev/null) 2>&1 | tail -1; fi
HAVE=$(gh release view "$TAG" --repo $REPO --json assets --jq '.assets[].name')
: > "$W/SHA256SUMS.txt"; (cd "$W" && sha256sum manifest.jsonl *.xz >> SHA256SUMS.txt)
for k in $(seq 0 $((N-1))); do
  kk=$(printf %02d $k); PART="proofs_part$kk.tar"
  if echo "$HAVE" | grep -qx "$PART"; then echo "part $kk already attached; skipping"; continue; fi
  D="$W/batch$kk"; rm -rf "$D"; mkdir -p "$D"
  # -o GSUtil:parallel_process_count=1 : gsutil's multiprocessing hangs on macOS
  # (bugs.python.org/issue33725); a 1,630-file batch stalled at 400 for an hour without it.
  # Threads still give parallelism. Batches of 100 keep the argv short and let a stall be seen.
  sed "s#^#$BKT/#" "$W/chunk$kk.txt" | xargs -n 100 sh -c 'gsutil -q -o "GSUtil:parallel_process_count=1" -m cp "$@" "'"$D"'/"' _
  got=$(ls "$D" | wc -l | tr -d ' '); want=$(wc -l < "$W/chunk$kk.txt" | tr -d ' '); [ "$got" = "$want" ] || { echo "batch $kk: got $got of $want"; exit 1; }
  tar -cf "$W/$PART" -C "$D" $(cat "$W/chunk$kk.txt"); rm -rf "$D"
  (cd "$W" && sha256sum "$PART" >> SHA256SUMS.txt)
  gh release upload "$TAG" --repo $REPO "$W/$PART" --clobber 2>&1 | tail -1; rm -f "$W/$PART"
  echo "part $kk uploaded ($got files)"
done
gh release upload "$TAG" --repo $REPO "$W/SHA256SUMS.txt" --clobber 2>&1 | tail -1
gh release view "$TAG" --repo $REPO --json assets --jq '.assets[] | "\(.name) \(.size)"'
echo "RELEASE DONE $TAG"
