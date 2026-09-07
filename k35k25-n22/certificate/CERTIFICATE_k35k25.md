# Certificate: R(K_{3,5}, K_{2,5}) — no valid 2-colouring of K_22 — Comparator-grade

**Statement certified** (`LRATCatcher.ComparatorChallengeK35K25`):
`LRATCatcher.Comparator.K35K25.encoded_unsat : LRATCatcher.Encoder.k35k25_n22.Unsat`
— the CNF the Lean encoder builds for n = 22, K_{3,5} in colour 0, K_{2,5} in colour 1
(codegree counters plus vertex-lex symmetry breaking), is unsatisfiable. With the encoder
soundness and the vertex-lex argument of the private Lean development (`../../REVIEWER.md`
section 5): no 2-colouring of K_22 avoids both patterns, so R(K_{3,5},K_{2,5}) ≤ 22; with the
K_21 colouring in `../../k35k25-lb22/`, = 22. The survey window was 21–23.

**History.** Closed 2026-09-05 with `cnc_close2` (every leaf verified at solve time): 484 top
cubes, nine levels of depth-8 resplits, 137,350 verified UNSAT leaves, 0 SAT. The flattened cover
(`../tree/k35k25_n22_flat.icnf`) is embedded verbatim as the string literals in
`K35K25FlatIcnf0..7.lean` and parsed by `ComparatorCubesK35K25.lean`.

**Comparator verdict** (`PASS_lrat-catcher-k35k25_2026-09-05.log`): statement matches the
Challenge; replayed and accepted by the Lean kernel AND nanoda; axioms exactly
`[propext, Classical.choice, Quot.sound, K35K25.cover_cakelpr, K35K25.leaves_cakelpr]`.

**External verdicts** (`ComparatorAxiomsK35K25.lean`), discharged by cake_lpr on DIMACS printed
from the Lean terms (`lratcatch-export-encoder k35k25_n22`: the base CNF, sha256 `2b81217d...`,
and the 137,350 cube prefixes) — every leaf is its prefix followed by the base body, solved with
CaDiCaL `--lrat` and checked with cake_lpr; the cover is the negation of the 137,350 cubes
(sha256 `b55c4786...`), refuted and checked the same way.
Ledger: `k35k25_cakelpr_encoder_ledger.jsonl` (137,350 leaf rows + 1 cover row, **all VERIFIED,
0 failures**). `k35k25_encoder_leaf_sha256.txt` lists the leaf hashes recomputed on a second
machine from the same printed base and prefixes; they match the ledger 137,350/137,350.

**Relation to the deposited instance.** `../instance/k35k25_n22.cnf` (sha256 `98a80fb4...`) is the
file the tree was built on; it equals the Lean-printed base clause for clause and in order,
differing only by its leading comment lines.

**Trust base:** as for K_{3,4},K_{3,3} (`../../k34k33-n19/certificate/CERTIFICATE.md`): Lean 4.30.0
kernel, nanoda, the three standard axioms, cake_lpr, `Std.Sat.CNF.dimacs`, and the embedded cube text.

**Discharge (2026-09-05 to 2026-09-07):** cake_lpr `s VERIFIED UNSAT` on **137,351/137,351** files
(137,350 leaves + the negated cover), 0 failures; 489 CPU-h solving and 261 CPU-h checking on a
16-vCPU machine, largest single proof 1.85 GB, **3.1 TB of LRAT proofs in total** — which is why
the proofs of this cell are not archived: a third party re-solves each leaf (`tools/cert_pass.py`).
Two operational notes, both visible in the ledger's history: the pass was disk-throughput-bound
until its boot disk was resized, and 26 leaves initially reported `FAIL` because concurrent cake_lpr
processes on GB-sized proofs were killed by the kernel's OOM handler; those rows were removed and
the leaves re-checked with fewer concurrent checkers (backups of the pre-repair ledgers are kept in
the project bucket). No leaf failed on a re-check.
