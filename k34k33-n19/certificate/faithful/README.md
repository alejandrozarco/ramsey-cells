# Comparator check of the value, stated about colorings (2026-09-17)

Cell: R(K_{3,4}, K_{3,3}), n = 19. Not a claim, unconfirmed, not peer reviewed.

[Comparator](https://github.com/leanprover/comparator) builds a trusted challenge file and a
solution in a sandbox, exports both, checks that the solution proves the challenge's statements
using only the permitted axioms, and replays the solution in the Lean kernel and, here, also in
nanoda, an independent kernel.

## What was checked

| config | challenge | theorem | permitted axioms | result |
|---|---|---|---|---|
| `faithful-value-kernel.json` | `ChallengeValueK.lean` | `LRATCatcher.FaithfulC.k34k33_eq_19` | `propext`, `Quot.sound`, `Classical.choice`, `LRATCatcher.Comparator.leaves_cakelpr`, `LRATCatcher.Comparator.cover_cakelpr` | nanoda and Lean kernel accept (`PASS_faithful-value-kernel_2026-09-17.log`) |
| `faithful-k19.json` | `Challenge.lean` | `LRATCatcher.FaithfulC.no_good_colouring_K19` | the same five | nanoda and Lean kernel accept (`PASS_faithful-k19_2026-09-17.log`) |

The statement of `k34k33_eq_19`, from `ChallengeValueK.lean`:

```
(¬ ∃ a : EColouring 19 2, SB.NoKst a 0 3 4 ∧ SB.NoKst a 1 3 3) ∧
(∃ a : EColouring 18 2, SB.NoKst a 0 3 4 ∧ SB.NoKst a 1 3 3)
```

`EColouring n 2` maps the edges of K_n (pairs i < j) to two colors. `SB.NoKst a c s t` says
color `c` contains no K_{s,t}: no disjoint vertex sets S, T with |S| = s, |T| = t and every
edge between them colored `c`. No `native_decide` is permitted, so none is used.

The two named axioms are the ones `../CERTIFICATE.md` describes: cake_lpr, the CakeML-verified
LRAT checker, accepted the 571 leaf files and the cover file printed from the Lean terms.

## The solution

`../../lean/FaithfulK34K33Comparator.lean`, unchanged. It combines three pieces:
* `LRATCatcher.Comparator.encoded_unsat`, the encoder's formula refuted through the two cake_lpr
  axioms;
* a bridge theorem: if the encoder's formula is unsatisfiable, no coloring avoids the two
  patterns (encoding faithfulness and vertex-lex symmetry breaking; three standard axioms);
* `SB.Witness18.witness18_kernel`: the K_18 coloring of `../../witness/`, checked by
  `decide +kernel`. The table is read from one natural number with `Nat.testBit`, proved equal to
  the table on all 324 vertex pairs, and the codegree condition is counted over ordered triples.

The bridge and the kernel witness are in the separate Lean development `sbsound`, which is not in
this repository (`../../../REVIEWER.md`, section 5). These files show exactly what was checked, but
the run cannot yet be repeated from this repository alone.

## How it was run

On one Linux machine (x86_64): Lean v4.30.0, comparator 71b52ec, nanoda_lib 68d5ca9,
lean4export v4.30.0, landrun. The workspace was sbsound with the eight lrat-catcher modules
behind `encoded_unsat` (`Basic`, `Kernel`, `Reflect`, `Cover`, `Encoder`, `ComparatorCubes`,
`ComparatorAxioms`, `ComparatorUnsatFallback`, byte-identical to `../../../lean/lrat-catcher/`)
copied in as a second library, so that Comparator's sandboxed build writes only inside the
project (`lakefile.toml` here). Dependencies were built first; the challenge and solution
modules were built by Comparator. Driver: `run_cmp2.sh`.

Two kinds of warnings in the transcripts carry no meaning for the result:
* `repository ... has local changes` for Mathlib and its dependencies: the Mathlib build tree
  was copied onto an exFAT disk, which does not keep file modes or symlinks. Lake reported
  Mathlib up to date and rebuilt none of it.
* style lints such as line length.
