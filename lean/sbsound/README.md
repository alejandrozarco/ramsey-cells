# sbsound: soundness of the bipartite encoding, in Lean 4

A Lean 4 development (Mathlib, `leanprover/lean4:v4.30.0`) proving that if the CNF produced by the
encoder `encodeBip` is unsatisfiable, then no 2-colouring of $`K_n`$ avoids $`K_{s_0,t_0}`$ in colour 0
and $`K_{s_1,t_1}`$ in colour 1. This step connects the refutations in `k34k33-n19/` and
`k35k25-n22/` to statements about colourings. It covers both parts of the encoding:

* the codegree constraints (Sinz sequential counters over every $`s`$-set), and
* the vertex-lex symmetry-breaking clauses: every good colouring has a relabelling that satisfies
  them.

Only the direction an upper bound needs is proved: a good colouring yields a satisfying assignment.
The converse is not proved.

## Main statements

| theorem | file | what |
|---|---|---|
| `SB.BipBridge.no_colouring_of_toCNFV_unsat` | `Sbsound/BipBridge.lean` | for $`s_0+2 \le n`$, $`s_1+2 \le n`$, $`t_0, t_1 \ge 2`$: `CNF.Unsat (toCNFV (encodeBip n s₀ t₀ s₁ t₁))` implies `¬ ∃ a : EColouring n 2, NoKst a 0 s₀ t₀ ∧ NoKst a 1 s₁ t₁` |
| `SB.Witness18.witness18_kernel` | `Sbsound/Witness18Kernel.lean` | the $`K_{18}`$ colouring of `k34k33-n19/witness/` has no $`K_{3,4}`$ in colour 0 and no $`K_{3,3}`$ in colour 1 (`decide +kernel`) |
| `SB.Witness21.witness21_kernel` | `Sbsound/Witness21Kernel.lean` | the $`K_{21}`$ colouring of `k35k25-lb22/witness/` has no $`K_{3,5}`$ in colour 0 and no $`K_{2,5}`$ in colour 1 (`decide +kernel`) |

`NoKst a c s t` (`Sbsound/Codegree.lean`) says that colour `c` contains no $`K_{s,t}`$: there are no
disjoint vertex sets $`S`$, $`T`$ with $`\lvert S\rvert = s`$, $`\lvert T\rvert = t`$ and every edge between them coloured `c`.
`EColouring n 2` (`Sbsound/SBGraph.lean`) maps the edges $`\{i,j\}`$, $`i \lt j`$, of $`K_n`$ to two colours.

`#print axioms` for each of the three theorems: `[propext, Classical.choice, Quot.sound]`. The library
contains no `sorry`. Its one use of `native_decide` is the earlier proof `witness18` in
`Sbsound/Witness18.lean`, which the three theorems above and the composing files do not use.

## Where it is used

* `k34k33-n19/lean/FaithfulK34K33Comparator.lean`: $`R(K_{3,4}, K_{3,3}) = 19`$.
* `k35k25-n22/lean/FaithfulK35K25Comparator.lean`: $`R(K_{3,5}, K_{2,5}) = 22`$.

Each composes `no_colouring_of_toCNFV_unsat` with the cell's `encoded_unsat` (from `lean/lrat-catcher`,
resting on two named cake_lpr verdict axioms) and the cell's kernel-checked witness. The Comparator
checks are in the cells' `certificate/faithful/` directories.

`Sbsound/EncoderVendored.lean` is a copy of the encoder definitions up to `encodeBip`
(`k34k33-n19/lean/Encoder.lean`, sha256 `f633f9b8…`), with the namespace changed. The composing files
prove the copy equal to `LRATCatcher.Encoder.encodeBip` (`encodeBip_eq`).

## Build

```
lake exe cache get     # Mathlib oleans
lake build
```

On a 16 GB machine the build completes; the largest module, `Sbsound/BipBridge.lean`, is the slowest.

## Files

| file | content |
|---|---|
| `SBGraph.lean` | edges, colourings, vertex and colour actions |
| `Codegree.lean` | `NoKst` and its codegree form (`codegree_iff`) for any colouring |
| `Sinz.lean`, `BiCounter.lean`, `CodegreeEncode.lean` | the sequential counters and their soundness |
| `SBEncode.lean`, `EncodeSound.lean` | the base encoding and its soundness |
| `SBCore.lean`, `SBChain.lean`, `SBKeystone.lean`, `SBClauses.lean` | lex-leader symmetry breaking: a good colouring has a relabelling satisfying the emitted clauses |
| `SBDegree.lean`, `SBDegreeVars.lean`, `SBDegreeClauses.lean` | the degree-ordered variant (used by `Portfolio.lean`, not by the two cells above) |
| `Portfolio.lean` | the encode step instantiated for the bipartite cells of this repository |
| `EncoderVendored.lean` | the copied encoder definitions |
| `BipBridge.lean` | the bridge from the encoder's clause list to colourings |
| `Witness18.lean`, `Witness18Kernel.lean`, `Witness21Kernel.lean` | the two witnesses |

## Related work

* M. Kirchweger, P. Manrique, S. Szeider, *Formally Verified Graph Generation with SAT Modulo Symmetries
  and Lean*, IJCAR 2026, LNCS, pp. 117–135. An end-to-end verified pipeline (encoding, dynamic symmetry
  breaking, solver proof) for graph generation.
* M. Anders et al., *Faster Certified Symmetry Breaking Using Orders With Auxiliary Variables*,
  AAAI 2026 (arXiv:2511.16637). Certified symmetry breaking (satsuma, VeriPB).
* S. Szeider, *Streaming LRAT Certificates into Lean Theorems* (arXiv:2607.00815), describing
  lrat-catcher; `lean/lrat-catcher` is a fork of its code.

Licence: MIT (`LICENSE`).
