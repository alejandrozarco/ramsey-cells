# R(K_{2,8}, K_{2,5}): rooted census at n = 22 (status 2026-10-06)

Status: **computation record, not peer reviewed.** Unconfirmed; nothing here is a claim. **Produced by AI
models** under the direction of the repository owner; see [`../AI_DISCLOSURE.md`](../AI_DISCLOSURE.md).

DS1 rev #18 lists $`R(K_{2,8}, K_{2,5})`$ as 22–23. A good coloring of $`K_{21}`$ (color 1 with no
$`K_{2,8}`$, color 2 with no $`K_{2,5}`$) is in `witness/`; the lower bound 22 is already published
(Van Overberghe), and this coloring was found here independently (`witness/`, header line).

This directory records a search for a good coloring of $`K_{22}`$. If every step below is correct, there
is none, and the value would be 22. The work is complete as a computation; the formal verification
listed under *Not yet done* is not.

## The census

A good coloring of $`K_{22}`$ would have every color-2 degree in $`\{8, 9, 10\}`$, at most 7 vertices of
color-2 degree 8 and at most 10 of degree 10. That leaves 44 degree histograms. Each histogram is split
by the neighbourhood of a chosen root vertex into rooted lists: 781 lists holding 23,886 cubes in
total (`runs/k28_rooted/H_<hist>_r<root>_c<comp>.txt`, one cube per line; the case parameters of each
list are in `gen_<tag>.json`). The argument for the census is that every good coloring with a given
histogram has a representative in one listed cube; see *Not yet done*.

The degree step is a Lean theorem, `lean/Lemma12.lean` (`degree_in_eight_nine_ten`, `n8_le_seven`,
`n10_le_ten`, `histogram_in_admissible`, `admissibleHistograms_card`); every `#print axioms` in the file
reports `propext`, `Classical.choice` and `Quot.sound` at most. It imports two modules of `../lean/sbsound`;
from that directory, after `lake build`: `lake env lean ../../k28k25-n22/lean/Lemma12.lean`.

Each cube was encoded by `scripts/lemma/rooted_encode.py` and refuted by CaDiCaL with an LRAT proof.
Cubes that did not finish within a cap were split recursively (`scripts/lemma/split_certify.py`); the
row of such a cube records its children and their verdicts in the field `split`.

| check (run from this directory) | result |
|---|---|
| `python3 scripts/lemma/census_grades.py` | 23,886 / 23,886 cubes decided against the 781 list files; certificate grades: cake_lpr 23,865, lrat-check 21, solver only 0 (2026-10-06) |
| `python3 scripts/referee/check_no_sat.py` | no SAT in 39,036 ledger rows across 667 files; no SAT record, no model file (2026-10-06) |
| `python3 scripts/lemma/check_histogram_set.py` | the 44 histograms and 781 list names match, name for name (names only) |
| `python3.12 scripts/lemma/indep_check.py` | a second, independent enumeration of the lists: 53 / 53 families, 0 mismatches |
| `python3 scripts/referee/verify_row.py --sample 200` | 200 sampled rows: the CNF rebuilt from the encoder hashes to the recorded `cnf_sha256` |
| `python3 scripts/referee/encoder_equiv_test.py` | encoder soundness and orbit completeness, exhaustive at small n; two deliberately wrong encoders must fail, and do |

The complete output of these checks on the working copy is in `checks/closure_checks_20261005.log`.

Certificate grades, per cube, as `census_grades.py` counts them:

* **cake_lpr (23,865 cubes)**: the proof was accepted by cake_lpr, the CakeML-verified LRAT checker;
* **lrat-check (21 cubes)**: accepted by `lrat-trim` and `lrat-check` at solve time. 5,396 cubes were
  solved before cake_lpr was added to the pipeline; they were re-solved and checked by cake_lpr on
  2026-10-05/06 (rows marked `synced_from: arm-vm`). The remaining 21 have proofs larger than 4 GiB and are
  being re-checked with a larger memory budget.

`verify_row.py` skips rows written before the fields it needs (`cnf_sha256`, encoder stamps) existed.

## Files

| path | contents |
|---|---|
| `statement/ChallengeK22.lean` | the statement, fixed on 2026-09-27 before the census closed (sha256 `ba92cca2…cf35029`) |
| `CERTIFICATION_2026-09-27.md` | the verification plan written on the same day: what must be trusted, how to check, what is missing. Unchanged since; its `[CLOSURE: …]` fields are not filled in yet |
| `runs/k28_rooted/H_*.txt`, `gen_*.json` | the 781 lists and their case parameters |
| `runs/k28_rooted/ledger_<tag>.jsonl` | one row per attempt: cube, result, seconds, proof checks, tools and their sha256 |
| `runs/k28_rooted/monster_lists.json` | the 80 lists handled by the split lane |
| `scripts/lemma/`, `scripts/referee/`, `gen_ramsey.py` | encoder, census pool, splitter, and the checks above |
| `lean/Lemma12.lean` | the degree lemma: every color-2 degree is 8, 9 or 10, and the 44 histograms |
| `scripts/astra/census_gen.py` | the list generator that `indep_check.py` compares against |
| `witness/witness_k2x8k2x5_n21.txt` | a good coloring of $`K_{21}`$ (`../tools/check_any.py witness/witness_k2x8k2x5_n21.txt K2x8,K2x5`) |
| `checks/` | the check transcript of 2026-10-05 |

In the ledgers, the `host` field and machine paths were replaced for publication by labels (`laptop`,
`workstation`, `arm-vm`, `cloud-<name>`, `~/`, `<bucket>/`). Nothing else was changed. Tool paths in the
scripts default to `cadical`, `lrat-trim`, `lrat-check` and `cake_lpr` on `PATH`, or to the environment
variables `CADICAL`, `TRIM`, `CHECK`, `CAKE`.

## Not yet done

* **cake_lpr for the last 21 cubes** (large proofs; in progress).
* **The argument that the 781 lists cover every good coloring.** The degree step is the Lean theorem
  above. The rest is a hand proof, checked by two independent enumerations (`check_histogram_set.py`,
  `indep_check.py`) but not formalised and not yet deposited.
* **A Lean link from the rooted encoder to colorings.** `../lean/sbsound` covers the bipartite encoder
  `encodeBip` used in `../k34k33-n19/` and `../k35k25-n22/`, not `rooted_encode.py`. For this cell the
  encoder is tested (`encoder_equiv_test.py`) and reviewed, not proved.
* **A Comparator check of `statement/ChallengeK22.lean`.**
* **The split cube trees** (`.icnf` files of the split lane) are not in this directory.

Until these are done, and until someone outside has checked the argument, this is a search record.
