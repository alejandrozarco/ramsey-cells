# Verifying the two lead results — the bare minimum

Unconfirmed, not peer reviewed. Nothing here is a claim; these are the artifacts and the commands
that let a third party re-derive each statement. Python 3, a C compiler (for CaDiCaL / lrat-trim /
lrat-check) and, for the last step only, Lean 4 (`elan`) are the prerequisites. Times are for one core.

## 1. R(K_{2,11}, K_{2,4}) = 26 — both bounds ours

**Lower bound, R ≥ 26** (seconds). A 2-colouring of K_25 with no K_{2,11} in colour 1 and no
K_{2,4} in colour 2: `k2x11-k2x4-lb26/witness/witness_k2x11k2x4_n25.txt` (lines `i j colour`).
```
python3 tools/check_any.py k2x11-k2x4-lb26/witness/witness_k2x11k2x4_n25.txt K2x11,K2x4
```
Any checker of subgraph containment will do; nothing else is assumed.

**Upper bound, R ≤ 26** (the formula for n = 26 is unsatisfiable).
1. The formula: `k211k24-n26/instance/k211k24_n26.cnf` (codegree counters + vertex-lex breaking).
   Regenerate and compare (minutes): `python3 tools/gen_ramsey.py 26 K2x11,K2x4 --vertex-lex`.
2. Tree and cover (minutes): every leaf verdict is in `k211k24-n26/tree/ledger.jsonl`; this re-proves
   and checks that the leaves cover every assignment and reports the tree structure:
```
cd k211k24-n26 && python3 ../tools/verify_close.py instance/k211k24_n26.cnf instance/k211k24_n26_d10.icnf tree --check-all
```
3. Every leaf, re-solved (about 20 CPU-hours): rebuild each of the 10,017 leaves from the Lean-printed
   base and prefixes, solve, check with cake_lpr — `tools/cert_pass.py` (usage in its header); the
   ledger we obtained is `k211k24-n26/certificate/k211k24_cakelpr_encoder_ledger.jsonl`, the hashes
   recomputed on a second machine `k211k24_encoder_leaf_sha256.txt`. A release with every trimmed
   proof kept (`tools/proof_archive.py`) is the release `proofs-k211k24-n26-2026-09-07` (five tar parts,
   9.07 GB), so a leaf can be replayed instead of re-solved.
4. The composed statement, replayed by the Lean kernel and by nanoda (minutes after the Lean build):
```
cd lean/lrat-catcher && lake build LRATCatcher.ComparatorUnsatK211K24 LRATCatcher.ComparatorChallengeK211K24
```
   then the Comparator (pins and PATH in `lean/lrat-catcher/README_RAMSEY_CELLS.md`); our transcript is
   `k211k24-n26/certificate/PASS_lrat-catcher-k211k24_2026-09-06.log`. The two external axioms are the
   cake_lpr verdicts of step 3.

What is NOT machine-checked publicly: that the encoder is faithful to "2-colouring of K_26 avoiding
both graphs" and that vertex-lex symmetry breaking loses no colouring. Both are argued in
`REVIEWER.md` section 5 and proved in a private Lean development; the public chain ends at
"this CNF is unsatisfiable".

## 2. R(K_{3,5}, K_{2,5}) = 22

**Lower bound, R ≥ 22** (seconds): `k35k25-lb22/witness/witness_k35k25_n21.txt`, checked by
`python3 tools/check_any.py k35k25-lb22/witness/witness_k35k25_n21.txt K3x5,K2x5`
(the directory also carries its own `verify.sh` and checksums). The survey printed 21–23.

**Upper bound, R ≤ 22.** Same layout under `k35k25-n22/`: instance (`gen_ramsey.py 22 K3x5,K2x5
--vertex-lex`), tree with 137,350 leaves (`tree/ledger.jsonl`, `tree/verified_leaves.jsonl`),
`tree/cover_audit_2026-09-05.txt`, and
```
cd k35k25-n22 && python3 ../tools/verify_close.py instance/k35k25_n22.cnf instance/k35k25_n22_d10.icnf tree --check-all
```
The Comparator statement passed (`certificate/PASS_lrat-catcher-k35k25_2026-09-05.log`); the cake_lpr
pass over all 137,350 Lean-printed leaves is running (`certificate/cake_lpr_ledger_IN_PROGRESS.jsonl`
is a snapshot) and its complete ledger replaces that file when it ends. Re-solving every leaf yourself
is about 40 CPU-hours with `tools/cert_pass.py`; proofs for this cell are not archived (about 3 TB raw).

## What independent review has already done
Two external audits (`review/2026-09-05/`, and the update review answered in `REVIEWER.md` section 7)
regenerated the formulas, traversed the trees, re-proved both covers, matched all certificate hashes
and re-checked every deposited witness with a checker written from the definition.

## 3. R(K_{3,5}, K_{3,3}) = 21 — refutation ours, lower bound Van Overberghe's (added 2026-09-08)

Different trust base from sections 1 and 2; see `k35k33-n21/certificate/CERTIFICATE_k35k33.md`.
The formula is the lex-free base in one-variable-per-edge layout plus 39,369 smsg symmetry clauses.

**Formula** (seconds): rebuild the base and Sigma and compare clause bodies with the deposit.
```
python3 tools/gen_ramsey.py 21 K3x5,K3x3 -o base.cnf
python3 tools/sms/tosms.py base.cnf base_sms.cnf 210
gunzip -k k35k33-n21/instance/sb21_nolex_salvaged.json.gz
python3 tools/sms/sigma2dimacs.py k35k33-n21/instance/sb21_nolex_salvaged.json 21 sigma.cnf
```
**Symmetry clauses** (~20 min, one core; cadical + lrat-trim + cake_lpr): every certificate individually.
```
CADICAL=... LRAT_TRIM=... CAKE_LPR=... python3 tools/sms/nc_cake_check.py k35k33-n21/instance/sb21_nolex_salvaged.json 21 nc.jsonl
```
Expect `NC-CAKE SUMMARY clauses=39369 UNSAT=39369 cake_VERIFIED=39369 bad=0`. What this does NOT
check: that appending all of Sigma preserves satisfiability (argued in `tools/sms/README.md`).

**Tree and cover** (minutes): every leaf of the cube tree on disk has a verified UNSAT row, and the
negated leaves are jointly unsatisfiable with a checked LRAT proof.
```
CADICAL=... LRAT_TRIM=... LRAT_CHECK=... python3 tools/verify_close.py k35k33-n21/instance/k35k33_n21_sms.cnf k35k33-n21/instance/k35k33_n21_sms_d10.icnf k35k33-n21/tree --check-sample 0
```
**Leaves** (~110 CPU-h): re-solve every leaf and check with cake_lpr, as in section 1.
```
python3 tools/export_prefixes.py k35k33-n21/instance/k35k33_n21_sms.cnf k35k33-n21/instance/k35k33_n21_sms_d10.icnf k35k33-n21/tree prefixes.tsv negcubes.cnf
cp k35k33-n21/instance/k35k33_n21_sms.cnf base_encoder.cnf
CADICAL=... CAKE_LPR=... WORKERS=16 CHECKERS=3 python3 tools/cert_pass.py
```
