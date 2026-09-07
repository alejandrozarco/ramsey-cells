# Certificate: R(K_{2,11}, K_{2,4}) — no valid 2-colouring of K_26 — Comparator-grade

**Statement certified** (`LRATCatcher.ComparatorChallengeK211K24`):
`LRATCatcher.Comparator.K211K24.encoded_unsat : LRATCatcher.Encoder.k211k24_n26.Unsat`
— the CNF the Lean encoder builds for n = 26, K_{2,11} in colour 0, K_{2,4} in colour 1
(`encodeBip 26 2 11 2 4`, codegree counters plus vertex-lex symmetry breaking), is unsatisfiable.
With the encoder soundness and the vertex-lex argument of the private Lean development
(`../../REVIEWER.md` section 5): no 2-colouring of K_26 avoids both patterns, so
R(K_{2,11},K_{2,4}) ≤ 26; with our K_25 colouring (`../../k2x11-k2x4-lb26/`), = 26.

**History.** Closed 2026-09-06 with `cnc_close2` (every leaf verified at solve time): 402 top cubes
(march_cu, depth 10), 49 capped cubes resplit at depth 8 over three levels, 10,017 verified UNSAT
leaves, 0 SAT, 48,416 core-seconds. The flattened cover (`../tree/k211k24_n26_flat.icnf`, 10,017 cubes)
is embedded verbatim as the string literal in `K211K24FlatIcnf0.lean` and parsed by
`ComparatorCubesK211K24.lean`.

**Comparator verdict** (`PASS_lrat-catcher-k211k24_2026-09-06.log`): statement matches the
Challenge; replayed and accepted by the Lean kernel AND nanoda; axioms exactly
`[propext, Classical.choice, Quot.sound, K211K24.cover_cakelpr, K211K24.leaves_cakelpr]`.

**External verdicts** (`ComparatorAxiomsK211K24.lean`), discharged by cake_lpr on DIMACS printed
from the Lean terms (`lratcatch-export-encoder k211k24_n26`: the base CNF, sha256 `72b4e9cc...`,
and the 10,017 cube prefixes) — every leaf is its prefix followed by the base body, solved with
CaDiCaL `--lrat` and checked with cake_lpr; the cover is the negation of the 10,017 cubes
(`p cnf 115703 10017`, sha256 `ed93aefc...`), refuted and checked the same way.
Ledger: `k211k24_cakelpr_encoder_ledger.jsonl` (10,017 leaf rows + 1 cover row).
`k211k24_encoder_leaf_sha256.txt` lists the leaf hashes recomputed on a second machine from the
same printed base and prefixes; they match the ledger 10,017/10,017.

**Relation to the deposited instance.** `../instance/k211k24_n26.cnf` (sha256 `f9bceef8...`) is
the file the tree was built on; it equals the Lean-printed base clause for clause and in order,
differing only by six leading comment lines.

**Trust base:** as for K_{3,4},K_{3,3} (`../../k34k33-n19/certificate/CERTIFICATE.md`): Lean 4.30.0
kernel, nanoda, the three standard axioms, cake_lpr, `Std.Sat.CNF.dimacs`, and the embedded cube text.

**Discharge (2026-09-06):** cake_lpr `s VERIFIED UNSAT` on **10,018/10,018** files (10,017 leaves +
the negated cover), 0 failures; largest proof 419 MB, 144 GB of proofs in total, 18.6 CPU-h solving
and 11.7 CPU-h checking on a 6-core host shared with other work; summary in `cert_pass_summary.txt`.

**Archived proofs (2026-09-07):** every leaf re-solved a second time, trimmed, re-checked with
lrat-check and cake_lpr (10,017/10,017) and kept: release `proofs-k211k24-n26-2026-09-07`,
`proofs_part00.tar` .. `proofs_part04.tar` (9.07 GB of xz proofs), with `manifest.jsonl`, the printed
inputs and `SHA256SUMS.txt`. The cover proof is re-derived by `verify_close.py --check-all` in minutes.
