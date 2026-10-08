/-
# `R(K_{2,8}, K_{2,5}) = 22`, Comparator-grade route: no `native_decide`

The solution for the fixed challenge `ramsey-cells/k28k25-n22/statement/ChallengeK22.lean` (sha256
`ba92cca2…cf35029`, 2026-09-27). Composition:
* `SB.Rooted.M5.no_good_K22_of_pending'` (`RootedM5/Close.lean`): no good colouring of `K_22`, assuming the
  refutation of the table rows still `pending`. It rests on M1-M4 (census lemmas, encoder soundness
  bridge, rooted canonical form, H-cover; standard axioms + `cover_cakelpr`), the kernel checks of the
  cube table (`RootedM5/Checks`, `RootedM5/Keys`) and the cube verdicts `direct_cakelpr`, `leaves_cakelpr`;
* `SB.Rooted.M5.no_pending` (`RootedM5/Attached.lean`): no row is `pending` (`decide +kernel`; builds
  only once every cube has an attached verdict);
* `SB.Witness21K28.witness_kernel` (`RootedM5/Witness21.lean`): the deposited good colouring of `K_21`,
  checked by `decide +kernel`.

`#print axioms` at the foot should list propext, Classical.choice, Quot.sound and the three named
cake_lpr axioms `SB.Rooted.M4.CoverData.cover_cakelpr`, `SB.Rooted.M5.direct_cakelpr`,
`SB.Rooted.M5.leaves_cakelpr`.

Build (lean-sb, one module per call): RootedM5.Close, RootedM5.Attached, RootedM5.Witness21, then
  lake env lean FaithfulK28K25Comparator.lean
-/
import RootedM5.Close
import RootedM5.Attached
import RootedM5.Witness21

namespace LRATCatcher.FaithfulC

/-- **No 2-colouring of `K_22` avoids `K_{2,8}` in colour 0 and `K_{2,5}` in colour 1.** -/
theorem no_good_colouring_K22 :
    ¬ ∃ a : EColouring 22 2, SB.NoKst a 0 2 8 ∧ SB.NoKst a 1 2 5 :=
  SB.Rooted.M5.no_good_K22_of_pending' (fun r hr hp => absurd hp (SB.Rooted.M5.no_pending r hr))

/-- **`R(K_{2,8}, K_{2,5}) = 22`**: no good colouring of `K_22`, and an explicit good colouring of
`K_21`. -/
theorem k28k25_eq_22 :
    (¬ ∃ a : EColouring 22 2, SB.NoKst a 0 2 8 ∧ SB.NoKst a 1 2 5) ∧
    (∃ a : EColouring 21 2, SB.NoKst a 0 2 8 ∧ SB.NoKst a 1 2 5) :=
  ⟨no_good_colouring_K22,
   ⟨SB.Witness21K28.w, SB.Witness21K28.witness_kernel.1, SB.Witness21K28.witness_kernel.2⟩⟩

end LRATCatcher.FaithfulC

#print axioms LRATCatcher.FaithfulC.no_good_colouring_K22
#print axioms LRATCatcher.FaithfulC.k28k25_eq_22
