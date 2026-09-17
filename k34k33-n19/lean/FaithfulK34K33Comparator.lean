/-
# `R(K_{3,4}, K_{3,3}) = 19`, Comparator-grade route: no `native_decide` in the refutation

Same composition as `FaithfulK34K33.lean`, with one piece swapped. The refutation of the encoder's
CNF is `LRATCatcher.Comparator.encoded_unsat` (module `LRATCatcher.ComparatorUnsatFallback`), the
statement Comparator certified on 2026-09-03 (`Comparator/CERTIFICATE.md`): it composes two named
axioms, `leaves_cakelpr` (571 leaf files) and `cover_cakelpr` (the cube cover), each discharged
outside Lean by cake_lpr, the CakeML-verified LRAT checker, on DIMACS printed from the Lean terms.
It replaces `LRATCatcher.Generated.k34k33_n19_unsat.encoded_unsat`, which needed 573
`native_decide` uses and 16 GB of chunk modules.

The K_18 colouring is `SB.Witness18.witness18_kernel` (lean-sb `Sbsound/Witness18Kernel.lean`), the same
statement as `witness18` proved by `decide +kernel` instead of `native_decide`. So both theorems below
should rest on propext, Classical.choice, Quot.sound and the two cake_lpr axioms only: no
`native_decide` anywhere. (Until 2026-09-17 this file used `witness18`, adding its two `native_decide`
axioms to `k34k33_eq_19`.) Nothing here imports a generated chunk.

Build (both projects on leanprover/lean4:v4.30.0):
  cd lean-sb && lake build Sbsound.BipBridge Sbsound.Witness18Kernel
  cd <lrat-catcher> && lake build LRATCatcher.ComparatorUnsatFallback
  LEAN_PATH="$(cd lean-sb && lake env printenv LEAN_PATH):<lrat-catcher>/.lake/build/lib/lean" \
    lean LRATCatcher/FaithfulK34K33Comparator.lean
-/
import LRATCatcher.ComparatorUnsatFallback
import Sbsound.BipBridge
import Sbsound.Witness18Kernel

namespace LRATCatcher.FaithfulC

open SB

/-! The vendored copy of the encoder is the original. Every definition except `combos`
is identified by `rfl`; `combos` is structurally recursive and the elaborator's smart
unfolding does not compare two separately compiled copies, so it is identified by
recursion on its own equations, and the two definitions built on it follow by rewriting. -/

theorem combos_eq : ∀ (k : ℕ) (l : List ℕ),
    SB.Encoder.combos k l = LRATCatcher.Encoder.combos k l
  | 0, [] => rfl
  | 0, _ :: _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => by
    simp only [SB.Encoder.combos, LRATCatcher.Encoder.combos]
    rw [combos_eq k xs, combos_eq (k + 1) xs]

theorem combos_eq' : SB.Encoder.combos = LRATCatcher.Encoder.combos := by
  funext k l; exact combos_eq k l

theorem codegreeColour_eq :
    SB.Encoder.codegreeColour = LRATCatcher.Encoder.codegreeColour := by
  funext n r c s t nv0
  unfold SB.Encoder.codegreeColour LRATCatcher.Encoder.codegreeColour
  rw [combos_eq']
  rfl

theorem encodeBip_eq (n s₀ t₀ s₁ t₁ : ℕ) :
    SB.Encoder.encodeBip n s₀ t₀ s₁ t₁ = LRATCatcher.Encoder.encodeBip n s₀ t₀ s₁ t₁ := by
  unfold SB.Encoder.encodeBip LRATCatcher.Encoder.encodeBip
  rw [codegreeColour_eq]
  rfl

/-- The vendored DIMACS conversion is `LRATCatcher.Encoder.toCNF`, definitionally
(both convert a literal by `l ↦ (|l| - 1, decide (0 < l))`). -/
theorem toCNF_eq (cs : List (List Int)) :
    SB.BipBridge.toCNFV cs = LRATCatcher.Encoder.toCNF cs := rfl

/-- The cake_lpr-certified `encoded_unsat`, restated on the vendored definitions. -/
theorem vendored_unsat : (SB.BipBridge.toCNFV (SB.Encoder.encodeBip 19 3 4 3 3)).Unsat := by
  rw [toCNF_eq, encodeBip_eq]
  exact LRATCatcher.Comparator.encoded_unsat

/-- **No 2-colouring of `K_19` avoids `K_{3,4}` in colour 0 and `K_{3,3}` in colour 1.** -/
theorem no_good_colouring_K19 :
    ¬ ∃ a : EColouring 19 2, NoKst a 0 3 4 ∧ NoKst a 1 3 3 :=
  SB.BipBridge.no_colouring_of_toCNFV_unsat (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) vendored_unsat

/-- **`R(K_{3,4}, K_{3,3}) = 19`**: no good colouring of `K_19`, and an explicit good
colouring of `K_18`. -/
theorem k34k33_eq_19 :
    (¬ ∃ a : EColouring 19 2, NoKst a 0 3 4 ∧ NoKst a 1 3 3) ∧
    (∃ a : EColouring 18 2, NoKst a 0 3 4 ∧ NoKst a 1 3 3) :=
  ⟨no_good_colouring_K19,
   ⟨SB.Witness18.w18, SB.Witness18.witness18_kernel.1, SB.Witness18.witness18_kernel.2⟩⟩

end LRATCatcher.FaithfulC

#print axioms LRATCatcher.FaithfulC.no_good_colouring_K19
#print axioms LRATCatcher.FaithfulC.k34k33_eq_19
