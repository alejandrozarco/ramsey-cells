/-
# `R(K_{3,4}, K_{3,3}) = 19` with no informal step between the encoder and the refutation

Composes three machine-checked pieces:
* `LRATCatcher.Generated.k34k33_n19_unsat.encoded_unsat` (module `LRATCatcher.EncodedUnsat`):
  the Lean encoder's own output `toCNF (encodeBip 19 3 4 3 3)` is unsatisfiable
  (571 `native_decide` chunk theorems + the cover theorem);
* `SB.BipBridge.no_colouring_of_toCNFV_unsat` (lean-sb, `Sbsound/BipBridge.lean`):
  `CNF.Unsat (toCNFV (encodeBip n s₀ t₀ s₁ t₁))` refutes every 2-colouring of `K_n` with no
  `K_{s₀,t₀}` in colour 0 and no `K_{s₁,t₁}` in colour 1, for `s + 2 ≤ n` and `2 ≤ t`
  (standard axioms only);
* `SB.Witness18.witness18` (lean-sb): the explicit good colouring of `K_18`.

`SB.Encoder` is a verbatim vendored copy of `LRATCatcher.Encoder` (up to `encodeBip`) and
`SB.BipBridge.toCNFV`/`dimacsLitV` are verbatim copies of `LRATCatcher.Encoder.toCNF` /
`LRATCatcher.dimacsLit`; the two `rfl` lemmas below are the identification.

Build recipe (this file cannot be built on a 16 GB laptop; see lean-sb/BRIDGE_PROGRESS.md, Stage D):
importing `LRATCatcher.EncodedUnsat` loads all 571 chunk oleans (~16 GB); it succeeded on a
64 GB machine for `EncodedUnsat` itself. Both projects use leanprover/lean4:v4.30.0, so the
oleans can be combined on one `LEAN_PATH`:
  LP="$(cd lean-sb && lake env printenv LEAN_PATH)"      # Mathlib + Sbsound oleans
  LP="$LP:<lrat-catcher>/.lake/build/lib/lean"          # LRATCatcher oleans incl. Generated/…
  LEAN_PATH="$LP" lean FaithfulK34K33.lean
after `lake build Sbsound.BipBridge Sbsound.Witness18` in lean-sb and with
`LRATCatcher/Generated/k34k33_n19_unsat/*.olean` (571 chunks + Base/Cover/Main) and
`LRATCatcher/{Basic,Encoder,EncoderBridge,EncodedUnsat}.olean` present in lrat-catcher's build tree.
-/
import LRATCatcher.EncodedUnsat
import Sbsound.BipBridge
import Sbsound.Witness18

namespace LRATCatcher.Faithful

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

/-- `encoded_unsat`, restated on the vendored definitions. -/
theorem vendored_unsat : (SB.BipBridge.toCNFV (SB.Encoder.encodeBip 19 3 4 3 3)).Unsat := by
  rw [toCNF_eq, encodeBip_eq]
  exact LRATCatcher.Generated.k34k33_n19_unsat.encoded_unsat

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
   ⟨SB.Witness18.w18, SB.Witness18.witness18.1, SB.Witness18.witness18.2⟩⟩

end LRATCatcher.Faithful

#print axioms LRATCatcher.Faithful.no_good_colouring_K19
#print axioms LRATCatcher.Faithful.k34k33_eq_19
