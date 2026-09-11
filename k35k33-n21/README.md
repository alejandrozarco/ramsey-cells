# R(K_{3,5}, K_{3,3}) — refutation at n = 21

This directory records a search that found no 2-colouring of K_21 with no K_{3,5} in colour 1 and
no K_{3,3} in colour 2. Together with a colouring of K_20 for this cell, that would give
R(K_{3,5}, K_{3,3}) = 21.

**The K_20 in `witness/` is not a new object.** It was found here by a Cayley search on Z_20
(connection set 2,3,4,5,7,10,13,15,16,17,18) and is **isomorphic, after relabelling, to Steven Van
Overberghe's archived `K(3,5)K(3,3)n20.g6`** in github.com/Steven-VO/circulant-Ramsey. The lower
bound R >= 21 is his and is cited [VO] in DS1; an external review pointed the coincidence out on
2026-09-11 and it is confirmed here by an explicit isomorphism. It is kept in this directory only so
the lower bound can be checked beside the refutation, which is the part done here. See `../NOTICE.md`. The survey window (DS1 rev. #18, table IVb) is 21–24, with no published
value. Unconfirmed, not peer reviewed. Nothing here is a claim.

**This refutation is one grade below the other deposited refutations, and differently shaped.**
Read "What is machine-checked" and "What is argued" before citing anything.

## How the formula differs from the other cells

The other refutations use `tools/gen_ramsey.py --vertex-lex` (static lex-leader symmetry breaking).
Under that encoding this cell did not close: a 100-cube sample of its top-level split capped 23 of
100 at 200,000 conflicts and the tree grew without bound. The formula deposited here instead is

    tosms( gen_ramsey.py 21 K3x5,K3x3 )  ++  Sigma

where the base is generated WITHOUT vertex-lex (so its solution set is closed under vertex
relabelling), `tools/sms/tosms.py` rewrites it to one variable per edge (colour 2 = edge present),
and Sigma is a set of 39,369 symmetry-breaking clauses extracted once by `smsg` (SAT Modulo
Symmetries, Kirchweger and Szeider, `--sym-break-clauses`) from a run bounded at 30 minutes and then
killed; `tools/sms/salvage_sigma.py` recovered the complete entries from the truncated dump. Every
clause of Sigma comes with the permutation smsg used as its non-canonicity witness
(`instance/sb21_nolex_salvaged.json.gz`). Sigma is used only as a set of clauses: no propagator runs
at proof time, and the solver, proof format and checkers are the ordinary ones.

## What is here

| path | contents |
|---|---|
| `instance/k35k33_n21_sms.cnf` | the formula (183,750 vars, 390,489 clauses): 351,120 base clauses followed by the 39,369 clauses of Sigma, in that order |
| `instance/sigma21_nolex.cnf` | Sigma alone, as printed by `tools/sms/sigma2dimacs.py` from the salvaged dump |
| `instance/sb21_nolex_salvaged.json.gz` | the 39,369 (clause, permutation) certificates, salvaged from smsg's dump |
| `instance/k35k33_n21_sms_d10.icnf` | the 403 top-level cubes (march_cu, depth 10) |
| `tree/splits/` | the depth-8 sub-cube file of every cube that hit the 120 s cap, seven levels of resplits (437 files) |
| `tree/ledger.jsonl` | one row per cube solved: id, result, seconds, `verified` (74,740 rows: 74,303 UNSAT, 437 CAP, 0 SAT) |
| `tree/k35k33_n21_sms_flat.icnf` | the 74,303 leaves of the tree as one flat cube list |
| `tree/close_k35k33_n21_sms.log` | the closer's log, ending in `level 7: 271 UNSAT(verified), 0 capped` |
| `tree/cover_audit_2026-09-08.txt` | `tools/verify_close.py` on the complete leaf set: TREE CLOSED, COVER VERIFIED |
| `certificate/cake_nc21nolex_ledger.jsonl` | cake_lpr verdict on each of the 39,369 non-canonicity certificates: all VERIFIED |
| `certificate/CERTIFICATE_k35k33.md` | the trust base, and the second-machine leaf pass (see below) |

## What is machine-checked

1. **Every leaf.** CaDiCaL 3.0.1 produced an LRAT proof for each of the 74,303 leaves, checked at
   solve time by `lrat-trim` (exit 20) then `lrat-check` (exit 0): `tree/ledger.jsonl`, field
   `verified`, true on every UNSAT row. Proofs were not retained. 0 SAT.
2. **Tree and cover.** `tools/verify_close.py` walks the cube tree on disk (top cubes + `splits/`),
   never the ledger, finds every leaf verified, then refutes the conjunction of the negated leaves
   with a checked LRAT proof: `tree/cover_audit_2026-09-08.txt` (run on a different machine from
   the solve). An audit of the ledger against the split files found, at every level, exactly as
   many children per capped cube as its split file has cubes, and no cap at the last level.
3. **Every certificate in Sigma, individually.** For each (clause, permutation) pair,
   `tools/sms/nc_sat_reduction.py` builds a propositional formula that is unsatisfiable exactly when
   the permutation witnesses non-canonicity of the assignment the clause forbids, over all
   completions; `tools/sms/nc_cake_check.py` refutes it with CaDiCaL, trims, and hands it to
   cake_lpr. 39,369 of 39,369 VERIFIED (`certificate/cake_nc21nolex_ledger.jsonl`).
4. **The formula itself**, clause by clause: the first 351,120 clauses equal
   `tosms(gen_ramsey.py 21 K3x5,K3x3)` and the rest equal `sigma2dimacs` of the salvaged dump,
   as sequences.

## What is argued, not machine-checked

- **Composition.** Item 3 shows each clause of Sigma is individually a sound symmetry-breaking
  clause. The step from "each clause is individually sound" to "appending all of Sigma to the base
  preserves satisfiability" is the standard lex-leader argument (the lexicographically minimal
  adjacency matrix in the isomorphism class of any solution satisfies every clause of Sigma at
  once, because each certificate excludes only assignments that are not lex-minimal). It is stated
  in `../tools/sms/README.md` and has not been formalised. Do not describe this deposit as
  "cake_lpr-verified symmetry breaking".
- **Base soundness.** The base encoding's faithfulness (codegree counters for K_{s,t}-freeness)
  is the same as for the other bipartite cells; the Lean development for it (`sbsound`) does not
  cover the one-variable-per-edge layout, so no Comparator-grade certificate exists for this cell.

## Second-machine leaf pass

The other refutations carry a `cert_*` ledger in which every leaf was re-solved and checked by
cake_lpr on a machine other than the solve box, with a sha256 of every leaf formula. The same pass
for this cell (`tools/export_prefixes.py` then `tools/cert_pass.py` on `instance/` + `tree/`) was
started on 2026-09-08 20:41 UTC; its ledger is added to `certificate/` when it lands, and
`CERTIFICATE_k35k33.md` states the result.

## Re-deriving it

```
# formula: base (no lex), SMS layout, then Sigma
python3 ../tools/gen_ramsey.py 21 K3x5,K3x3 -o base.cnf
python3 ../tools/sms/tosms.py base.cnf base_sms.cnf 210
gunzip -k instance/sb21_nolex_salvaged.json.gz
python3 ../tools/sms/sigma2dimacs.py instance/sb21_nolex_salvaged.json 21 sigma.cnf
# base_sms.cnf ++ sigma.cnf  ==  instance/k35k33_n21_sms.cnf  (clause bodies, in order)

# the certificates (needs cadical, lrat-trim, cake_lpr; ~20 min on one core)
CADICAL=... LRAT_TRIM=... CAKE_LPR=... python3 ../tools/sms/nc_cake_check.py instance/sb21_nolex_salvaged.json 21 nc_ledger.jsonl

# tree and cover
CADICAL=... LRAT_TRIM=... LRAT_CHECK=... python3 ../tools/verify_close.py instance/k35k33_n21_sms.cnf instance/k35k33_n21_sms_d10.icnf tree --check-sample 0

# the leaves themselves (re-solve + cake_lpr on every leaf; ~110 CPU-h)
python3 ../tools/export_prefixes.py instance/k35k33_n21_sms.cnf instance/k35k33_n21_sms_d10.icnf tree prefixes.tsv negcubes.cnf
cp instance/k35k33_n21_sms.cnf base_encoder.cnf
CADICAL=... CAKE_LPR=... WORKERS=16 CHECKERS=3 python3 ../tools/cert_pass.py
```
