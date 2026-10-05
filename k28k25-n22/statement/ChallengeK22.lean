/-
# Comparator CHALLENGE: R(K_{2,8}, K_{2,5}) at N = 22, stated about colourings

THE TRUSTED FILE FOR THE 2003 CELL. Written 2026-09-27, while the rooted census stood at 23,861 of
23,886 cubes decided and zero satisfiable, so that the statement to be certified is fixed before the
result exists and cannot be fitted to it afterwards. Its sha256 is recorded in ramsey/JOURNAL.md
under that date. It is to be kept byte-identical; a solution must prove these statements as written.

`EColouring 22 2` is a map from the edges of K_22 (pairs i < j) to two colours. `SB.NoKst a c s t`
says colour c contains no K_{s,t}: no disjoint vertex sets S, T with |S| = s, |T| = t and every S-T
edge coloured c. Both are defined in this development (`Sbsound/SBGraph.lean`,
`Sbsound/Codegree.lean`) and are the same definitions the deposited K_19 challenge uses
(`Challenge.lean`, `ChallengeValueK.lean` beside this file). Colour 0 is the colour that must avoid
K_{2,8} (the census's "red", codegree at most 7); colour 1 must avoid K_{2,5} ("blue", codegree at
most 4). This matches `SB.Portfolio.sound_K2x8_K2x5 : EncodeSoundFor n 2 8 2 5`.

Two statements, so that the refutation can be certified on its own:

* `no_good_colouring_K22` -- no 2-colouring of K_22 avoids both patterns, i.e. R(K_{2,8},K_{2,5}) <= 22.
  This is what the census decides. If any cube is satisfiable this statement is FALSE and the
  deposit is a K_22 colouring instead; this file then records the target that failed.
* `k28k25_eq_22` -- the same, together with a good colouring of K_21, i.e. R(K_{2,8},K_{2,5}) = 22.
  The lower bound is published (Van Overberghe; DS1 rev 18 prints 22-23); a K_21 colouring is held
  at `ramsey/runs/reference_graphs/witness_k2x8k2x5_n21_circulant21.txt` and would be checked by the
  kernel as `Sbsound.Witness18Kernel` checks the K_18 colouring for the K_19 cell.

Permitted axioms for a solution: `propext`, `Quot.sound`, `Classical.choice`, plus named external
verdicts of cake_lpr declared on the challenge side, as for the K_19 cell. Nothing else.
-/
import Sbsound.Codegree

theorem LRATCatcher.FaithfulC.no_good_colouring_K22 :
    ¬ ∃ a : EColouring 22 2, SB.NoKst a 0 2 8 ∧ SB.NoKst a 1 2 5 := sorry

theorem LRATCatcher.FaithfulC.k28k25_eq_22 :
    (¬ ∃ a : EColouring 22 2, SB.NoKst a 0 2 8 ∧ SB.NoKst a 1 2 5) ∧
    (∃ a : EColouring 21 2, SB.NoKst a 0 2 8 ∧ SB.NoKst a 1 2 5) := sorry
