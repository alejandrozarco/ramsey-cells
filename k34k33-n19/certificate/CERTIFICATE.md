# Certificate: R(K_{3,4}, K_{3,3}) — no valid 2-colouring of K_19 — Comparator-grade

**Statement certified** (`LRATCatcher.ComparatorChallenge`):
`LRATCatcher.Comparator.encoded_unsat : LRATCatcher.Encoder.k34k33_n19.Unsat`
— the CNF the Lean encoder builds for n = 19, K_{3,4} in colour 0, K_{3,3} in colour 1
(codegree Sinz counters + vertex-lex symmetry breaking) is unsatisfiable. With
`SB.Portfolio.sound_K3x4_K3x3` and `no_colouring_of_no_leader` (lean-sb, certified under the
three standard axioms alone) this is: no 2-colouring of K_19 avoids both patterns, i.e.
R(K_{3,4},K_{3,3}) ≤ 19; with the verified 18-vertex witness, = 19.

**Comparator verdict** (`PASS_lrat-catcher_2026-09-03.log`): statement matches the Challenge;
replayed and accepted by the Lean kernel AND nanoda; axioms used exactly
`[propext, Classical.choice, Quot.sound, cover_cakelpr, leaves_cakelpr]`. No `native_decide`.

**The two named external verdicts** (`LRATCatcher/ComparatorAxioms.lean`), discharged by
cake_lpr — the CakeML-verified LRAT checker, built from its shipped assembly on x86-64 Linux:
- `leaves_cakelpr` — 571 leaf files, each `cube ++ Encoder.k34k33_n19` printed from the Lean
  term by `lratcatch-export-encoder` (`Std.Sat.CNF.dimacs`), reconstructed on the checking
  host and sha256-matched 571/571 to the Lean-printed originals
  (`k34k33_encoder_leaf_sha256.txt`): **572/572 `s VERIFIED UNSAT`** (571 leaves + cover),
  ledger `k34k33_cakelpr_encoder_ledger.jsonl` (per-file sha256, proof bytes, timings).
- `cover_cakelpr` — `negcubes.cnf` printed from the cube literal: `s VERIFIED UNSAT`.

**Trust base, in full:** Lean 4.30.0 kernel; nanoda (independent Rust kernel); the three
standard axioms; cake_lpr's verified checker; the ~20-line DIMACS printer `Std.Sat.CNF.dimacs`
(the only unverified link between the Lean terms and the files cake_lpr read); and the cube
list literal `ComparatorCubes.lean` (any error there can only make the cover check fail).

**Not in the trust base any more:** the compiled Lean evaluator (`Lean.ofReduceBool`, 573 uses
before), the DIMACS parser and the file-vs-encoder bridge O7 (kept only as a cross-check:
`diff` shows the printed base is byte-identical in clause body to `gen_ramsey.py`'s file).

**Reproduce:** `scripts/certify/comparator_setup.sh` (toolchain, pinned), then
`lake env comparator Comparator/lrat-catcher-fallback.json`; the cake_lpr pass is
`scripts/certify/cakelpr_encoder_pass.py` over `lratcatch-export-encoder` output.
