# Lean package behind the `certificate/` directories

This is a buildable snapshot of the Lean 4 project used to produce every Comparator certificate in
this repository (snapshot of 2026-09-06). It is a fork of **lrat-catcher** by Stefan Szeider
(github.com/leansolving/lrat-catcher, MIT license, upstream commit 4ec2168), which imports SAT
certificates into Lean 4 by reflection. Our additions, all under the same license:

* `LRATCatcher/Encoder.lean` — a Lean port of `tools/gen_ramsey.py` (`encodeBip`: codegree counters
  plus vertex-lex symmetry breaking) and of the degree-ordering variants of `benchmarks/.../gen_variant.py`
  (`encodeBipDO`, `encodeBipDOL`), with one named cell per certified formula
  (`k34k33_n19`, `k35k24_n19`, `k35k25_n22`, `k211k23_n22`, `k211k24_n26`, `k28k25_n22_DO/DOL`, ...).
  `lake exe lratcatch-export-encoder <cell> cubes.icnf outDir --prefixes` prints the base CNF and one
  prefix line per cube; every certificate's `base_encoder.cnf` hash quoted in a README is the hash of
  that printed file.
* `LRATCatcher/Cover.lean`, `MixedCover.lean`, `EncodedUnsat.lean` — cube covers as data
  (`parseICnf`), `cover_unsat` (leaves unsat + negated cubes unsat ⇒ formula unsat) and its mixed
  variant for trees whose leaves were solved under two formulas implied by one target.
* `LRATCatcher/Comparator*.lean`, `Comparator/*.json` — per-cell Challenge (statement with `sorry`),
  Axioms (the two external cake_lpr verdicts), Cubes/FlatIcnf (the flat cover embedded verbatim as a
  string) and Unsat (the solution) modules, with the Comparator configuration listing the permitted
  axioms. These are the same files as in each cell's `certificate/` directory.

Not included: the `Generated/` directory of earlier per-chunk reflection modules (16 GB, superseded
by the Comparator route), upstream tests and showcases, and the private `sbsound` development that
proves the encoders faithful and the symmetry breaking sound (see `../../REVIEWER.md` section 5).

Note on K_{3,4}/K_{3,3}: its certified solution module is `ComparatorUnsatFallback.lean` with the
configuration `Comparator/lrat-catcher-fallback.json` (two external verdict axioms, like every later
cell; PASS transcript in `../../k34k33-n19/certificate/`). `ComparatorUnsat.lean` is an experimental
variant that checks the cover certificate inside the Lean kernel (`lrat_reflect_cnf +kernel`,
reading `../runs/k34k33_export/cover.lrat`); it takes well over an hour of kernel reduction and is
not part of any deposited certificate. Build named targets rather than the whole library.

## Build and replay a certificate

Toolchain: Lean `v4.30.0` (pinned in `lean-toolchain`; `elan` fetches it), no Mathlib.

```
cd lean/lrat-catcher
lake build LRATCatcher.ComparatorUnsatK211K23 LRATCatcher.ComparatorChallengeK211K23
```
`#print axioms` in the Unsat module lists exactly `propext, Classical.choice, Quot.sound` and the two
cell axioms `leaves_cakelpr`, `cover_cakelpr`.

The Comparator protocol (statement matches the challenge; solution replayed by the Lean kernel and by
nanoda; axioms restricted to the configured list) was run with these pins:
leanprover/comparator @ 71b52ec29e06d4b7d882726553b1ceb99a2499e0, leanprover/lean4export @ v4.30.0,
robsimmons/nanoda_lib @ 68d5ca9db226849b41a6fff59d796ff19d0a8840, zouuup/landrun @ 5ed4a3db3a4ad930d577215c6b9abaa19df7f99f
(landrun and lean4export must be on PATH):
```
lake env <comparator>/.lake/build/bin/comparator Comparator/lrat-catcher-k211k23.json
```
The transcript of each run is the `PASS_*.log` in the cell's `certificate/` directory. The two
external axioms are discharged outside Lean by `cake_lpr` on the printed leaves and negated cover
(`tools/cert_pass.py`; the ledger in `certificate/`), or replayed with kept proofs by
`tools/proof_archive.py`.
