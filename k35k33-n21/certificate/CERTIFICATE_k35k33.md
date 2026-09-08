# Trust base of the R(K_{3,5}, K_{3,3}) refutation at n = 21

Unconfirmed, not peer reviewed. Nothing here is a claim. This file says exactly what was checked
by what, so that the statement is cited at its real grade and no higher.

## Statement

No 2-colouring of the edges of K_21 has colour 1 free of K_{3,5} and colour 2 free of K_{3,3}.

## Chain, from the formula to the statement

| step | what it establishes | checked by | where |
|---|---|---|---|
| A | the deposited formula is `tosms(gen_ramsey 21 K3x5,K3x3)` followed by `sigma2dimacs(sb21_nolex_salvaged.json)`, clause for clause | byte comparison, 2026-09-08 | `../README.md`, "Re-deriving it" |
| B | each of the 39,369 clauses of Sigma is individually a sound symmetry-breaking clause: its permutation witnesses non-canonicity over all completions | reduction to propositional UNSAT (`tools/sms/nc_sat_reduction.py`), CaDiCaL LRAT proof, `lrat-trim`, **cake_lpr** (CakeML-verified) | `cake_nc21nolex_ledger.jsonl`, 39,369/39,369 VERIFIED, `cake_nc21nolex.log` |
| C | appending all of Sigma to the isomorphism-closed base preserves satisfiability | **argued** (lex-leader composition, `tools/sms/README.md`); not machine-checked | — |
| D | every one of the 74,303 leaves of the cube tree is unsatisfiable | CaDiCaL 3.0.1 LRAT proof, `lrat-trim` exit 20, `lrat-check` exit 0, at solve time on the solve box | `../tree/ledger.jsonl`, field `verified` |
| E | the 74,303 leaves cover the whole space (their negations are jointly unsatisfiable) | CaDiCaL LRAT proof, `lrat-trim`, `lrat-check`, on a second machine | `../tree/cover_audit_2026-09-08.txt` |
| F | the cube tree on disk is complete: every capped cube has a split file whose cube count equals its number of children; the last level has no cap | `tools/verify_close.py` walk plus an independent ledger-vs-splits audit | `../tree/cover_audit_2026-09-08.txt`, campaign journal 2026-09-08 |
| G | second-machine re-solve and cake_lpr check of every leaf, with sha256 of each leaf formula | `tools/cert_pass.py` on a separate box | **in progress**, started 2026-09-08 20:41 UTC; ledger to be added here as `cert_ledger.jsonl` |
| H | the base encoding is faithful to K_{s,t}-freeness | the codegree encoding is the one used for every other bipartite cell here; its Lean development (`sbsound`) does not cover the one-variable-per-edge layout | — |

## Grade, compared with the other refutations in this repository

The other refutations have steps D, E and G at cake_lpr grade and, on top of that, a Comparator
transcript: the statement `encoded_unsat` accepted by the Lean kernel and by nanoda, with the leaf
verdicts as named external axioms re-derived by cake_lpr on Lean-printed leaves. This cell has no
Comparator transcript, because no Lean encoder exists for its formula layout, and it carries step C
as a written argument rather than a machine check. When step G lands, the leaves reach the same
checker grade as the other cells; steps C and H remain argued.

## Wording

Permitted: "every leaf and the cover are LRAT-checked; every non-canonicity obligation of the
symmetry clauses is cake_lpr-checked; the composition of those obligations is argued."
Not permitted: "cake_lpr-verified symmetry breaking", "formally verified", "certified" without the
qualification above.
