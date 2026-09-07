# R(K_{3,5}, K_{2,5}) — refutation at n = 22

Together with the K_21 coloring in `../k35k25-lb22/`, this directory records a search that found no
2-coloring of K_22 with no K_{3,5} in color 1 and no K_{2,5} in color 2, over the symmetry-broken
encoding. Unconfirmed, not peer reviewed. Nothing here is a claim.

## What is here

| path | contents |
|---|---|
| `instance/k35k25_n22.cnf` | the CNF from `../tools/gen_ramsey.py 22 K3x5,K2x5 --vertex-lex` (164,416 vars, 317,478 clauses) |
| `instance/k35k25_n22_d10.icnf` | the 484 top-level cubes (march_cu, depth 10) |
| `tree/splits/` | the sub-cube files for every cube that hit the 900 s cap (depth 8 each), nine levels |
| `tree/ledger.jsonl` | one row per cube solved: id, result, seconds, `verified` |
| `tree/verified_leaves.jsonl` | leaves whose proofs were checked in a separate pass |
| `tree/k35k25_n22_flat.icnf` | the 137,350 leaves of the tree as one flat cube list |
| `tree/cover_audit_2026-09-05.txt` | output of `tools/verify_close.py`: every leaf of the cube tree on disk has a checked UNSAT verdict; no gaps; no SAT |
| `certificate/` | the Lean statement and Comparator transcript (see below) |

## What is machine-checked

1. Every leaf: CaDiCaL 3.0.1 produced an LRAT proof, checked at solve time by `lrat-trim` then
   `lrat-check` (`tree/ledger.jsonl`, field `verified`), or in the pre-verification pass
   (`tree/verified_leaves.jsonl`). 137,350 leaves; 0 SAT.
2. Tree and cover: `tools/verify_close.py` walks the cube tree on disk (top cubes + `splits/`),
   not the ledger, finds every leaf verified (TREE CLOSED), and then refutes the conjunction of
   the negated leaves with a checked LRAT proof (COVER VERIFIED) — `tree/cover_audit_2026-09-05.txt`.
   An earlier version of the tool reported only the first property; an external review showed
   it accepted an incomplete cube list. The reviewer independently proof-checked this cover.
3. Statement, by Comparator (`certificate/PASS_lrat-catcher-k35k25_2026-09-05.log`): the theorem
   `LRATCatcher.Comparator.K35K25.encoded_unsat : LRATCatcher.Encoder.k35k25_n22.Unsat`
   is accepted by the Lean kernel and by nanoda, with axioms exactly `propext`, `Quot.sound`,
   `Classical.choice` and the two named external verdicts in `certificate/ComparatorAxiomsK35K25.lean`.
4. The two external verdicts were re-derived by cake_lpr (a CakeML-verified LRAT checker) on leaf
   files printed from the Lean encoder term. **Complete as of 2026-09-07**:
   `certificate/k35k25_cakelpr_encoder_ledger.jsonl` has 137,350 leaf rows plus the cover row, all
   `VERIFIED`, no failures (per-file sha256, solver verdict, checker verdict, proof size). The pass
   took 489 CPU-h of solving and 261 CPU-h of checking over 3.1 TB of LRAT proofs, largest single
   proof 1.85 GB. `certificate/k35k25_encoder_leaf_sha256.txt` lists the same leaf hashes recomputed
   independently on a second machine; they match the ledger 137,350/137,350.
   Twenty-six leaves initially reported `FAIL` with empty checker output: those were cake_lpr
   processes killed by the kernel's OOM handler when too many ran concurrently on a 16 GB machine
   over GB-sized proofs. Those rows were removed and the leaves re-checked with fewer concurrent
   checkers; none failed on the re-check. See `certificate/CERTIFICATE_k35k25.md`.
   The proofs themselves are not archived (3.1 TB); a third party re-solves each leaf with
   `../tools/cert_pass.py`, or `../tools/proof_archive.py` to keep the proofs.

## What is not in this repository

The theorem that the encoder's unsatisfiability implies that no coloring exists — the encoding's
faithfulness and the soundness of the lex-leader symmetry breaking — is a separate Lean
development (`sbsound`, private at the time of writing). `certificate/Encoder.lean` is the Lean
transcription of `gen_ramsey.py`; `diff` of its printed output against `instance/k35k25_n22.cnf`
shows identical clause bodies (see `../REVIEWER.md`).
