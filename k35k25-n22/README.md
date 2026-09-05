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
2. Cover: `tools/verify_close.py` walks the cube tree on disk (top cubes + `splits/`), not the
   ledger, and finds every leaf verified (`tree/cover_audit_2026-09-05.txt`).
3. Statement, by Comparator (`certificate/PASS_lrat-catcher-k35k25_2026-09-05.log`): the theorem
   `LRATCatcher.Comparator.K35K25.encoded_unsat : LRATCatcher.Encoder.k35k25_n22.Unsat`
   is accepted by the Lean kernel and by nanoda, with axioms exactly `propext`, `Quot.sound`,
   `Classical.choice` and the two named external verdicts in `certificate/ComparatorAxiomsK35K25.lean`.
4. The two external verdicts are being re-derived by cake_lpr (a CakeML-verified LRAT checker)
   on leaf files printed from the Lean encoder term: `certificate/cake_lpr_ledger_IN_PROGRESS.jsonl`
   (per-file sha256, solver verdict, checker verdict). This pass was still running when this
   directory was committed; the file is replaced when it completes.

## What is not in this repository

The theorem that the encoder's unsatisfiability implies that no coloring exists — the encoding's
faithfulness and the soundness of the lex-leader symmetry breaking — is a separate Lean
development (`sbsound`, private at the time of writing). `certificate/Encoder.lean` is the Lean
transcription of `gen_ramsey.py`; `diff` of its printed output against `instance/k35k25_n22.cnf`
shows identical clause bodies (see `../REVIEWER.md`).
