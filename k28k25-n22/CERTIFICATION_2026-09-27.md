# Verification: R(K_{2,8}, K_{2,5}) at N = 22

Unconfirmed, not peer reviewed. Nothing here is a claim.

This file says what a reader must trust to accept the result, and how to check the rest. It was
written on 2026-09-27, before the census closed, so that on closure day it is a copy, not a
composition. Every bracketed `[CLOSURE: …]` is a number or a fact to be filled in from the
artefacts on that day, never from memory. Until they are filled in, the result is not established
and this file says so.

## 1. The statement, pinned in advance

`ChallengeK22.lean` (this directory; the compiled original is
`lean-sb/StageD/comparator/ChallengeK22.lean`), sha256

    ba92cca24659ec5e2d1525cca8f02b3dc027f2019953ae02f9a5dfebbcf35029

fixed on 2026-09-27 with the census at 23,861 of 23,886 cubes decided and zero satisfiable. It
states, in the same vocabulary as the deposited K_19 challenge (`EColouring n 2`,
`SB.NoKst a c s t`):

```lean
theorem LRATCatcher.FaithfulC.no_good_colouring_K22 :
    ¬ ∃ a : EColouring 22 2, SB.NoKst a 0 2 8 ∧ SB.NoKst a 1 2 5

theorem LRATCatcher.FaithfulC.k28k25_eq_22 :
    (¬ ∃ a : EColouring 22 2, SB.NoKst a 0 2 8 ∧ SB.NoKst a 1 2 5) ∧
    (∃ a : EColouring 21 2, SB.NoKst a 0 2 8 ∧ SB.NoKst a 1 2 5)
```

Colour 0 avoids K_{2,8}, colour 1 avoids K_{2,5}. The file compiles under Lean 4.30.0 with
exactly two `declaration uses 'sorry'` warnings and no other output; a solution proves these
statements as written. If any census cube is satisfiable, the first statement is false, the deposit
is a K_22 colouring checked by the kernel, and this file records the target that failed.

## 2. What must be trusted when the chain is complete

The target standard is the one the K_19 cell reached (`ramsey-cells/k34k33-n19/certificate/`):

1. **Lean's kernel** (4.30.0) and nanoda, on a build the reader makes from source.
2. **The statement**, section 1.
3. **The axioms**: `propext`, `Classical.choice`, `Quot.sound`, and two named external verdicts
   declared on the challenge side, `[CLOSURE: exact names]`, each meaning "cake_lpr, the
   CakeML-verified LRAT checker, printed `s VERIFIED UNSAT` on the files printed from these Lean
   terms": one for the leaves, one for the cover.
4. **cake_lpr** itself, built from its shipped assembly (`TOOLCHAIN.json` pins the commit and
   binary sha256).
5. **The ~20-line DIMACS printer** `Std.Sat.CNF.dimacs`, the only unverified link between the
   Lean terms and the files cake_lpr read.
6. **The cube list literal**, whose only possible failure makes the cover check fail.

Nothing else would need to be read. In particular the encoder, the census scripts, the solvers,
the trimmer, `lrat-check`, every ledger and every hand proof would be outside the trust base.

## 3. What must be trusted today (2026-09-27)

The chain does not yet reach the statement of section 1 in Lean. As the repository stands, the
result "no good colouring of K_22" rests on the following, in decreasing order of assurance.
Section 5 lists what closes each gap.

| # | Step | Form | Evidence | Trust base |
|---|---|---|---|---|
| a | Blue degrees lie in {8,9,10}; at most 7 vertices of degree 8, at most 10 of degree 10; hence one of 44 histograms | **Lean theorem** | `degree_exclusion/lean/Lemma12.lean`: `degree_in_eight_nine_ten`, `n8_le_seven`, `n10_le_ten`, `histogram_in_admissible`, `admissibleHistograms_card` | kernel, 3 axioms, no `sorry` (check `#print axioms`) |
| b | The 44 histograms expand into exactly 781 rooted lists holding 23,886 cubes, and every good colouring with a given histogram has a representative in one listed cube | **hand proof + two independent programs** (obligation G, Theorem 7.1 of `LEMMAS_draft.md`) | `scripts/lemma/check_histogram_set.py` (names, from Lean bounds); `scripts/lemma/indep_check.py` (53/53 families, 0 mismatches, input digest `7212f56e…2951`); the generator's `F == orbit` assertions | the two enumerations and the canonical-form argument as refereed in Astra rounds 3–4, 11–12b, 15, 32; **not formalised** |
| c | Each cube's CNF says "a good colouring in this cube exists" and nothing stronger | **Python encoder**, tested and audited | `scripts/referee/encoder_equiv_test.py` (exhaustive at N ≤ 7, soundness + orbit completeness, two negative controls); Astra round 27 encoder audit; `verify_row.py` rebuilds any row's CNF byte-for-byte | `rooted_encode.py` as reviewed; **no Lean bridge** (obligation E). `Sbsound.Portfolio.sound_K2x8_K2x5` covers the base bipartite encoding, not the rooted cube encoder |
| d | Each of the 23,886 cubes is unsatisfiable | **machine-checked per cube** | ledgers `ledger_<tag>.jsonl`: `[CLOSURE: n]` cake_lpr-verified, `[CLOSURE: n]` lrat-trim + lrat-check only, `[CLOSURE: n]` rc 20 only (today: 18,465 / 5,396 / 0) | cake_lpr for grade 3–4 rows; `lrat-check` (unverified C) for grade-2 rows; the solver alone for grade-1 rows. Derivations are not retained |
| e | For a cube solved by splitting, the children cover the cube | per-parent record | `split_certify.py`: `[CLOSURE: cite the cover check it performs and the ledger field that records it]` | as recorded; `[CLOSURE: verify against the code, not this table]` |
| f | The lower bound: a good colouring of K_21 | witness file | `runs/reference_graphs/witness_k2x8k2x5_n21_circulant21.txt`, `check_any.py`; published bound (Van Overberghe; DS1 rev 18: 22–23) | any subgraph-containment checker |

Two things this table does not say and must not be read as saying:

* "Zero SAT" is a statement about the cubes attempted. While any remain, it says nothing about
  them, and the remainder is the hard tail.
* Rows b and c are the places an error would leave every certificate in row d valid and worthless.
  They are where a reader's time should go first.

## 4. How to check

From `ramsey/`, in this order; the first is decisive if it fails.

```
python3 scripts/referee/check_no_sat.py          # reads ledgers, SAT_FOUND.jsonl, SAT_*.txt; exits 2 if it read nothing
python3 scripts/lemma/census_grades.py           # decided / total against the LIST files, and the grade breakdown
python3 scripts/fleet/coverage_audit.py --census-lists ''   # must print ORPHANED 0
python3 scripts/lemma/check_histogram_set.py     # 44 histograms, 781 lists, names generated not parsed
python3.12 scripts/lemma/indep_check.py          # second enumeration, 53/53 families, minutes
python3 scripts/referee/verify_row.py --sample 200   # each sampled row's CNF rebuilt and hash-matched
python3 scripts/referee/encoder_equiv_test.py    # soundness + orbit completeness at small N; two controls must FAIL
```

Lean, from `lean-sb/`:

```
lake build Lemma12 && grep -n "print axioms" Lemma12.lean    # then read the output: no sorryAx anywhere
lake env lean StageD/comparator/ChallengeK22.lean            # exactly two 'declaration uses sorry' warnings
```

At closure, additionally:

```
[CLOSURE: the Comparator command and config, as StageD/comparator/run_cmp2.sh does for K_19]
```

## 5. Distance from section 3 to section 2

Known items, none new, in decreasing order of size:

1. **The Lean bridge for the rooted encoder** (obligation E): a syntactic identity between what
   `rooted_encode.py` emits and a Lean-defined formula, plus soundness of that formula for
   `SB.NoKst`. `lrat-catcher` has this for `gen_ramsey.py` at other cells (O7); not for the
   rooted census.
2. **The canonical-form and coverage theorem** (row b, Theorem 7.1): hand proof, refereed, not
   formalised.
3. **Lean-printed leaves.** The K_19 certificate printed every leaf from the Lean term and
   sha256-matched the files cake_lpr read. The census leaves are Python-printed.
4. **The K_21 witness in the kernel** (`Witness21Kernel`, as `Witness18Kernel` for K_19): needed
   for `k28k25_eq_22`, not for `no_good_colouring_K22`.
5. **Grade-2 rows**: `[CLOSURE: n]` rows have `lrat-check` but no cake_lpr verdict; the cake
   regeneration pass is owed (`JOURNAL.md`, cake_regen).

Without items 1–3 the deposit is "census + hand proofs + per-cube certificates", the grade the
K3x5,K3x3 note is filed at, and this file must say so in its first line.

## 6. Scope

Lean establishes row a. Programs establish rows b–d to the extent section 3 states. The hand
proofs (`LEMMAS_draft.md`, Propositions 4.2, 5.1, 5.3–5.6, 5.8, 6.1, 6.5, Lemmas 6.2–6.4,
Theorem 7.1) are the argument that rows a–d together imply the statement of section 1.

The theorem and the proof as written are separate claims. A defect in rows b or c would be a
defect in the proof; whether the theorem survives it would then depend on what the defect is.
The soundness canary that a reader will ask for first, that the same pipeline returns SAT on a
size where a good colouring is known, is `[CLOSURE: cite the run and its ledger row]`.

## 7. Results

`[CLOSURE: date, host, Lean version, build time, census_grades output verbatim, check_no_sat
output verbatim, Comparator transcript path and its last three lines]`
