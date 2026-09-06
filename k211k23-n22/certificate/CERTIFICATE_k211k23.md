# Certificate: R(K_{2,11}, K_{2,3}) — no valid 2-colouring of K_22 — Comparator-grade

**Statement certified** (`LRATCatcher.ComparatorChallengeK211K23`):
`LRATCatcher.Comparator.K211K23.encoded_unsat : LRATCatcher.Encoder.k211k23_n22.Unsat`
— the CNF the Lean encoder builds for n = 22, K_{2,11} in colour 0, K_{2,3} in colour 1
(`encodeBip 22 2 11 2 3`, codegree counters plus vertex-lex symmetry breaking), is unsatisfiable.
With the encoder soundness and the vertex-lex argument of the private Lean development
(`../../REVIEWER.md` section 5): no 2-colouring of K_22 avoids both patterns, so
R(K_{2,11},K_{2,3}) ≤ 22; with the 21-vertex lower bound already in the literature
(Radziszowski's survey, section 3.3.2), = 22.

**History.** Closed 2026-09-06 with `cnc_close2` (every leaf verified at solve time): 374 top cubes
(march_cu, depth 10), 4 capped and resplit at depth 8, 1,313 verified UNSAT leaves, 0 SAT, 5,628
core-seconds. The flattened cover (`../tree/k211k23_n22_flat.icnf`, 1,313 cubes) is embedded
verbatim as the string literal in `K211K23FlatIcnf0.lean` and parsed by `ComparatorCubesK211K23.lean`.

**Comparator verdict** (`PASS_lrat-catcher-k211k23_2026-09-06.log`): statement matches the
Challenge; replayed and accepted by the Lean kernel AND nanoda; axioms exactly
`[propext, Classical.choice, Quot.sound, K211K23.cover_cakelpr, K211K23.leaves_cakelpr]`.

**External verdicts** (`ComparatorAxiomsK211K23.lean`), discharged by cake_lpr on DIMACS printed
from the Lean terms (`lratcatch-export-encoder k211k23_n22`: the base CNF, sha256 `57518b8c...`,
and the 1,313 cube prefixes) — every leaf is that prefix followed by the base body, solved with
CaDiCaL `--lrat` and checked with cake_lpr; the cover is the negation of the 1,313 cubes
(`p cnf 63944 1313`, sha256 `178f8555...`), refuted and checked the same way.
Ledger: `k211k23_cakelpr_encoder_ledger.jsonl` (1,313 leaf rows + 1 cover row).
`k211k23_encoder_leaf_sha256.txt` lists the leaf hashes recomputed on a second machine from the
same printed base and prefixes; they match the ledger 1,313/1,313.

**Relation to the deposited instance.** `../instance/k211k23_n22.cnf` (sha256 `799c7b96...`) is
the file the tree was built on; it equals the Lean-printed base clause for clause and in order,
differing only by six leading comment lines.

**Trust base:** as for K_{3,4},K_{3,3} (`../../k34k33-n19/certificate/CERTIFICATE.md`): Lean 4.30.0
kernel, nanoda, the three standard axioms, cake_lpr, `Std.Sat.CNF.dimacs`, and the embedded cube text.

**Discharge (2026-09-06):** cake_lpr `s VERIFIED UNSAT` on **1,314/1,314** files (1,313 leaves +
the negated cover), 0 failures; largest proof 419 MB, 15.5 GB of proofs in total, 1.92 CPU-h solving and
0.98 CPU-h checking (6-core host); summary in `cert_pass_summary.txt`.
