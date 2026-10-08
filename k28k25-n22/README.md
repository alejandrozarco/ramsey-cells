# R(K_{2,8}, K_{2,5}) at n = 22 (status 2026-10-08)

Status: **computation record with a Comparator-checked Lean theorem, not peer reviewed.** Unconfirmed;
nothing here is a claim. **Produced by AI models** under the direction of the repository owner; see
[`../AI_DISCLOSURE.md`](../AI_DISCLOSURE.md).

DS1 rev #18 lists $`R(K_{2,8}, K_{2,5})`$ as 22–23. A good coloring of $`K_{21}`$ (color 1 with no
$`K_{2,8}`$, color 2 with no $`K_{2,5}`$) is in `witness/`; the lower bound 22 is already published
(Van Overberghe), and this coloring was found here independently (`witness/`, header line).

This directory records a search for a good coloring of $`K_{22}`$ that found none, and a Lean theorem
about colorings built on it. `lean/FaithfulK28K25Comparator.lean` proves

```
theorem k28k25_eq_22 :
    (¬ ∃ a : EColouring 22 2, NoKst a 0 2 8 ∧ NoKst a 1 2 5) ∧
    (∃ a : EColouring 21 2, NoKst a 0 2 8 ∧ NoKst a 1 2 5)
```

against the statement `statement/ChallengeK22.lean`, fixed on 2026-09-27 before the census closed
(sha256 `ba92cca2…cf35029`, unchanged). Lean's colors 0 and 1 are colors 1 and 2 on this page.
`#print axioms`: `propext`, `Classical.choice`, `Quot.sound` and three named axioms that stand for
cake_lpr verdicts, `SB.Rooted.M4.CoverData.cover_cakelpr`, `SB.Rooted.M5.direct_cakelpr`,
`SB.Rooted.M5.leaves_cakelpr`. Comparator accepted the theorem with exactly these permitted axioms, in the
Lean kernel and in nanoda, on 2026-10-08 (`certificate/faithful/`).

Unlike the other cells with a Lean value theorem, the search here is not over one formula with a cube
tree. It is a census: the colorings are split by degree histogram and by the neighbourhood of a root
vertex into 23,886 cubes, each encoded and refuted separately. The Lean proof therefore has three parts
that the other cells do not need: the census lemmas, the coverage of the census, and the soundness of
the rooted encoder for every clause family. The sources are in `../lean/sbsound/` (directories
`RootedLemmas/`, `RootedBridge/`, `RootedM4/`, `RootedM5/`, and `Lemma12.lean`) and
`../lean/lrat-catcher/LRATCatcher/RootedEncoder.lean`.

## The census

A good coloring of $`K_{22}`$ would have every color-2 degree in $`\{8, 9, 10\}`$, at most 7 vertices of
color-2 degree 8 and at most 10 of degree 10. That leaves 44 degree histograms. Each histogram is split
by the neighbourhood of a chosen root vertex into rooted lists: 781 lists holding 23,886 cubes in
total (`runs/k28_rooted/H_<hist>_r<root>_c<comp>.txt`, one cube per line; the case parameters of each
list are in `gen_<tag>.json`).

Each cube was encoded by `scripts/lemma/rooted_encode.py` and refuted by CaDiCaL with an LRAT proof.
Cubes that did not finish within a cap were split recursively (`scripts/lemma/split_certify.py`); the
row of such a cube records its children and their verdicts in the field `split`. Every cube now has a
proof accepted by cake_lpr, the CakeML-verified LRAT checker: 22,457 directly and 1,429 through a
split into 126,351 leaves. Two cubes (`5_10_7_r8_c242`, lines 49 and 70) had direct proofs too large for
cake_lpr (11.3 and 16.1 GB after trimming) and were re-solved by splitting; the last large direct proofs
were checked with a larger memory budget.

## The Lean theorem

`no_good_colouring_K22` is composed in `../lean/sbsound/RootedM5/Close.lean` and
`../lean/sbsound/RootedM5/Attached.lean` from the following pieces. Everything except the three named
axioms is checked by the Lean kernel, with axioms `propext`, `Classical.choice`, `Quot.sound` at most.

* **Census lemmas** (`Lemma12.lean`, `RootedLemmas/`): every color-2 degree is 8, 9 or 10, and the 44
  histograms (`degree_in_eight_nine_ten`, `histogram_in_admissible`, `admissibleHistograms_card`); the
  complement identity, the deficit sum, the interval and budget bounds, the threshold sum and the filters
  (i)–(iii) of the list generator, each in the exact form the encoder and the generator compute.
* **Coverage** (`RootedM4/`): every good coloring of $`K_{22}`$ has a relabelling that is in canonical form
  for one cube of the table (`exists_canon`, `no_good_K22_of_cubes`). The steps: the semantics of the
  encoder's cell layout `cellsOf` for all 781 cases, evaluated by `decide +kernel` (`caseB_all`,
  `census_cells`); the relabelling by degree and root (`exists_relabel`); a two-stage lex leader
  (`stage1`, `exists_leader_orbit`); and the H-cover: for each of the 53 (root degree, composition)
  families, a cover CNF built from a certificate says that every neighbourhood graph meeting filters (i)
  and (ii) is lex-leader for the recorded permutations only if it is a blocked word (`cover_sound`). The
  certificate checks (filter-(iii) witnesses for 59,625 words, listed words, permutations) are
  kernel-checked (`RootedM4/CoverChecks/`); the 53 cover CNFs are the axiom `cover_cakelpr`.
* **Encoder soundness** (`RootedBridge/`): for every clause family that `rootedFormula` emits (edge
  layer, base codegree counters, row 1, H units, degree counters, codegree gates and counters, tight
  intervals, channel, budget, lex comparisons, wall pairs, automorphism comparisons) the truthful
  assignment of a good coloring in canonical form satisfies it, so an unsatisfiable formula excludes the
  cube (`no_canon_of_unsat`); for a split cube, unsatisfiable leaves that form a complete case split
  (`coversB`) do the same (`no_canon_of_children_unsat`). The theorems are about
  `LRATCatcher.Rooted.rootedFormula`, the Lean encoder, which prints CNFs byte-identical to
  `rooted_encode.py`.
* **Cube table** (`RootedM5/`): the 23,886 rows as Lean data (case, H, option set, verdict shape, split
  leaves), with kernel checks that the table covers every census case (`keys_all`), that each case's
  rows are exactly the listed words of its family certificate (`famH_spec`, `table_ok`), that every
  split is complete (`coversB`), and that no row is pending (`no_pending`). The cube verdicts are the
  axioms `direct_cakelpr` and `leaves_cakelpr`.
* **Witness** (`RootedM5/Witness21.lean`): the coloring in `witness/` (sha256 `49984dbd…`), checked by
  `decide +kernel`.

Only the direction the upper bound needs is proved: a good coloring would satisfy some cube's formula.
Kernel evaluation of `rootedFormula` itself is not used (it does not reduce in the kernel); the cube
axioms are therefore stated about the Lean terms `Row.clauses r` / `Row.leafClauses r t u`, and bound to
the cake_lpr verdicts by printing those terms (next section), as the other cells do for their leaf
files.

## Binding of the verdicts to the Lean terms

`runs/k28_rooted/m5_final/` holds the evidence:

* `cube_table.jsonl.gz`: one row per cube: list, line, H, option set, verdict (`direct` with the CNF
  sha256, or `split` with every leaf's literals and CNF sha256), and the ledger row it comes from
  (`src`, file:line of the ledgers in `runs/k28_rooted/`).
* `rows_ser.txt.gz`: the serialisation of every row of the Lean constant `SB.Rooted.M5.rows`, written by
  `SerRows.lean`; it equals the serialisation of `cube_table.jsonl` line for line.
* `binding_verify.jsonl.gz`: the output of `m5_verify.py`. The compiled printer `m5-print`
  (`../lean/sbsound/RootedM5Print.lean`) parses each serialised row, echoes the serialisation of the
  parsed row (equal to its input for all 23,886), and prints the DIMACS file of `Row.clauses r` (direct)
  or of every leaf with `LRATCatcher.Rooted.writeDimacs`. 23,886 / 23,886 rows BOUND: each of the 148,808
  printed files (22,457 cube files, 126,351 leaf files) has the sha256 recorded in a cake_lpr-verified
  ledger row or split leaf. Summary: `binding_summary.json`.
* `print_axioms_FaithfulK28K25Comparator.txt`: `#print axioms` of the two theorems.
* `m5_table.py` (builds the table from the ledgers and the family certificates), `m5_gen_lean.py`,
  `m5_gen_fam.py` (write the Lean data and check modules), `cases.json`, `opt_resolve.json` (option set of
  12 split rows without an `encoding` field, resolved by printing their first leaf),
  `table_summary.json`.

`runs/k28_rooted/m4_canon/` and `runs/k28_rooted/m0_hcover/` hold the H-cover: `cakelpr_cover.jsonl`
(the 53 cover CNFs printed from the Lean terms `famCNF fc` by `PrintCover.lean`, their sha256, and
cake_lpr `s VERIFIED UNSAT`, 53 / 53), `cover_print_compare.jsonl` (the Lean-printed files equal the
generator's files minus their comment lines, 53 / 53), `gen_cover_data.py` (writes
`RootedM4/CoverData/` from the certificates), and the generator: `enum_classes.py`, `hcover.py`,
`cnfgen.py`, `validate.py` (an independent rebuild of every cover CNF from its certificate),
`certs.jsonl.gz` (the 53 family certificates, one JSON per line; `validate.py` reads them as
`data/<tag>/cert_<tag>.json`) and `results.jsonl` (per family: classes, rounds, CNF size, CaDiCaL,
lrat-check and cake_lpr verdicts). The cover proofs (178 MB) and the cube proofs are not archived; a
third party re-solves them.

## Checks

| check (run from this directory) | result |
|---|---|
| `python3 scripts/lemma/census_grades.py` | 23,886 / 23,886 cubes decided against the 781 list files; certificate grades: cake_lpr 23,886, lrat-check 0, solver only 0 (2026-10-08) |
| `python3 scripts/referee/check_no_sat.py` | no SAT in 39,057 ledger rows across 667 files; no SAT record, no model file (2026-10-08) |
| `python3 scripts/lemma/check_histogram_set.py` | the 44 histograms and 781 list names match, name for name (names only) |
| `python3 scripts/referee/check_cube_table.py` | every list line has one row of the cube table; its ledger row is cake_lpr-verified with the recorded hash (direct) or leaf hashes (split, complete case split); 23,886 / 23,886 rows BOUND, 148,808 printed files |
| `python3.12 scripts/lemma/indep_check.py` | a second, independent enumeration of the lists: 53 / 53 families, 0 mismatches |
| `python3 scripts/referee/verify_row.py --sample 200` | 200 sampled rows: the CNF rebuilt from the encoder hashes to the recorded `cnf_sha256` |
| `python3 scripts/referee/encoder_equiv_test.py` | encoder soundness and orbit completeness, exhaustive at small n; two deliberately wrong encoders must fail, and do |

The output of these checks except `check_cube_table.py`, on the working copy of 2026-10-05 (before the cake_lpr
re-check of the remaining cubes, so with the counts of that day), is in `checks/closure_checks_20261005.log`.

The census grades count, per cube, the best ledger row of that cube's own list. 5,396 cubes were first
solved before cake_lpr was added to the pipeline; they were re-solved and checked by cake_lpr on
2026-10-05/06 (rows marked `synced_from: arm-vm`). The 21 rows of the large-proof pass and the split
re-solve of 2026-10-07/08 (19 direct, 2 split) were appended to their ledgers on 2026-10-08 (host
`arm-vm`).

To replay the binding: build `m5-print` in `../lean/sbsound/` (`lake build m5-print`), `gunzip -k` the
table and `rows_ser.txt.gz` in `runs/k28_rooted/m5_final/`, and run `python3 m5_verify.py` there; it prints
every file and compares hashes (it uses macOS `taskpolicy`; remove it on Linux). To replay a verdict,
solve the printed file with CaDiCaL (`--lrat`) and check the proof with cake_lpr. The Comparator replay
is described in `certificate/faithful/README.md`.

## Files

| path | contents |
|---|---|
| `statement/ChallengeK22.lean` | the statement, fixed on 2026-09-27 before the census closed (sha256 `ba92cca2…cf35029`) |
| `lean/FaithfulK28K25Comparator.lean` | the solution: `no_good_colouring_K22`, `k28k25_eq_22` |
| `certificate/faithful/` | Comparator configurations, the axiom wrapper `ChallengeK22Ax.lean`, workspace `lakefile.toml`, driver `run_cmp28.sh`, PASS transcript |
| `CERTIFICATION_2026-09-27.md` | the verification plan written on the day the statement was fixed. Unchanged; its `[CLOSURE: …]` fields are not filled in. It foresaw two named verdict axioms and `Std.Sat.CNF.dimacs` as printer; the solution has three (the H-cover is a separate axiom) and prints with `writeDimacs` / `dimacsBody` from the Lean encoder |
| `runs/k28_rooted/H_*.txt`, `gen_*.json` | the 781 lists and their case parameters |
| `runs/k28_rooted/ledger_<tag>.jsonl` | one row per attempt: cube, result, seconds, proof checks, tools and their sha256 |
| `runs/k28_rooted/monster_lists.json` | the 80 lists handled by the split lane |
| `runs/k28_rooted/m5_final/`, `m4_canon/`, `m0_hcover/` | cube table, hash binding, H-cover evidence and scripts (above) |
| `scripts/lemma/`, `scripts/referee/`, `gen_ramsey.py` | encoder, census pool, splitter, and the checks above |
| `lean/Lemma12.lean` | the degree lemma (a copy of `../lean/sbsound/Lemma12.lean`); from `../lean/sbsound`: `lake env lean ../../k28k25-n22/lean/Lemma12.lean` |
| `scripts/astra/census_gen.py` | the list generator that `indep_check.py` compares against |
| `witness/witness_k2x8k2x5_n21.txt` | a good coloring of $`K_{21}`$ (`../tools/check_any.py witness/witness_k2x8k2x5_n21.txt K2x8,K2x5`) |
| `checks/` | the check transcript of 2026-10-05 |

In the ledgers, the `host` field and machine paths were replaced for publication by labels (`laptop`,
`workstation`, `arm-vm`, `cloud-<name>`, `~/`, `<bucket>/`). Nothing else was changed. In the scripts of
`runs/k28_rooted/` the paths to the Lean project were set to `../lean/sbsound` and `../lean/lrat-catcher`,
and in `m5_table.py` the name of the mirrored host was replaced by `mirror` / `arm-vm`. Tool paths in the
scripts default to `cadical`, `lrat-trim`, `lrat-check` and `cake_lpr` on `PATH`, or to the environment
variables `CADICAL`, `TRIM`, `CHECK`, `CAKE`; the M0 scripts name `~/claude_projects/sat/…` as in the ledgers.

## What is trusted

* the Lean kernel (v4.30.0) and nanoda, which both replayed the solution;
* cake_lpr, on the 53 cover files and the 148,808 cube and leaf files;
* that each ledger's `cnf_sha256` is the hash of the file cake_lpr read, and sha256;
* the Lean compiler agreeing with the kernel on `rootedFormula`, `writeDimacs`, `famCNF` and `dimacsBody`
  (the printers that wrote the files; the same kind of trust as the other cells, whose axioms are also
  about printed Lean terms);
* Comparator's tooling (comparator, lean4export, landrun);
* a reading of `NoKst` against the definition of $`R(K_{2,8}, K_{2,5})`$.

The hand proof of the census (degree lemma, filters, Theorem 3.1 on the canonical form) is now replaced by
the Lean proofs above; no gap was found in it. No one outside has checked the argument or the
formalisation. Until someone does, this is a search record with a machine-checked certificate, not a
settled value.
