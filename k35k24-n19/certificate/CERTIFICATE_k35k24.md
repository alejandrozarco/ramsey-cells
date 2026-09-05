# Certificate: R(K_{3,5}, K_{2,4}) — no valid 2-colouring of K_19 — Comparator-grade

**Statement certified** (`LRATCatcher.ComparatorChallengeK35K24`):
`LRATCatcher.Comparator.K35K24.encoded_unsat : LRATCatcher.Encoder.k35k24_n19.Unsat`
— the CNF the Lean encoder builds for n = 19, K_{3,5} in colour 0, K_{2,4} in colour 1, is
unsatisfiable. With `SB.Portfolio.sound_K3x5_K2x4` and `no_colouring_of_no_leader` (lean-sb,
three standard axioms, Comparator-checked): no 2-colouring of K_19 avoids both patterns, so
R(K_{3,5},K_{2,4}) ≤ 19; with the 18-vertex witness `witness_k35k24_n18.txt`, = 19.

**History.** Claimed "=19 (UNSAT-based)" on 2026-08-20 from ledgers whose cube files were later
lost; re-closed 2026-09-04 with `cnc_close2` (every leaf verified at solve time): 408 top cubes,
406 UNSAT, 2 capped and split into 367 children, all UNSAT — 773 verified leaves, 0 SAT.
The flattened cover (`k35k24_n19_flat.icnf`, 773 cubes) is the cube list literal
`ComparatorCubesK35K24.lean`.

**Comparator verdict** (`PASS_lrat-catcher-k35k24_2026-09-05.log`): statement matches the
Challenge; replayed and accepted by the Lean kernel AND nanoda; axioms exactly
`[propext, Classical.choice, Quot.sound, K35K24.cover_cakelpr, K35K24.leaves_cakelpr]`.

**External verdicts** (`ComparatorAxiomsK35K24.lean`), discharged by cake_lpr on DIMACS printed
from the Lean terms by `lratcatch-export-encoder k35k24_n19` (773 leaves + `negcubes.cnf`),
reconstructed on the checking host and sha256-matched 773/773
(`k35k24_encoder_leaf_sha256.txt`): ledger `k35k24_cakelpr_encoder_ledger.jsonl`
— see the discharge line below.

**Trust base:** as for K_{3,4},K_{3,3} (CERTIFICATE.md): Lean 4.30.0 kernel, nanoda, the three
standard axioms, cake_lpr, `Std.Sat.CNF.dimacs`, and the cube list literal.

**Discharge (2026-09-05):** cake_lpr `s VERIFIED UNSAT` on **774/774** files (773 leaves + `negcubes.cnf`), 0 failures; leaf sha256 matched the Lean-printed files 773/773; cover verdict VERIFIED; largest proof 666 MB; total solve 2.16 CPU-h.
