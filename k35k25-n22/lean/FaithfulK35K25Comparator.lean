/-
# `R(K_{3,5}, K_{2,5}) = 22`, Comparator-grade route: no `native_decide`

The same composition as `FaithfulK34K33Comparator.lean`, for the cell `k35k25_n22`:
* `LRATCatcher.Comparator.K35K25.encoded_unsat` (module `LRATCatcher.ComparatorUnsatK35K25`): the Lean
  encoder's own output `toCNF (encodeBip 22 3 5 2 5)` is unsatisfiable. It composes two named axioms,
  `leaves_cakelpr` (137,350 leaf files) and `cover_cakelpr` (the cube cover), each discharged outside
  Lean by cake_lpr, the CakeML-verified LRAT checker, on DIMACS printed from the Lean terms
  (Comparator PASS 2026-09-05; cake_lpr ledger complete 2026-09-07);
* `SB.BipBridge.no_colouring_of_toCNFV_unsat` (lean-sb, `Sbsound/BipBridge.lean`): `CNF.Unsat` of the
  encoding refutes every 2-colouring of `K_n` with no `K_{s₀,t₀}` in colour 0 and no `K_{s₁,t₁}` in
  colour 1 (encoding soundness and soundness of the vertex-lex symmetry breaking; standard axioms only);
* `SB.Witness21.witness21_kernel` (lean-sb, `Sbsound/Witness21Kernel.lean`): an explicit good colouring
  of `K_21`, checked by `decide +kernel`.

So `no_good_colouring_K22` and `k35k25_eq_22` should rest on propext, Classical.choice, Quot.sound and
the two cake_lpr axioms only (`#print axioms` at the foot).

Build (both projects on leanprover/lean4:v4.30.0):
  cd lean-sb && lake build Sbsound.BipBridge Sbsound.Witness21Kernel
  cd <lrat-catcher> && lake build LRATCatcher.ComparatorUnsatK35K25
  LEAN_PATH="$(cd lean-sb && lake env printenv LEAN_PATH):<lrat-catcher>/.lake/build/lib/lean" \
    lean LRATCatcher/FaithfulK35K25Comparator.lean
-/
import LRATCatcher.ComparatorUnsatK35K25
import Sbsound.BipBridge
import Sbsound.Witness21Kernel

namespace LRATCatcher.FaithfulK35K25

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
theorem vendored_unsat : (SB.BipBridge.toCNFV (SB.Encoder.encodeBip 22 3 5 2 5)).Unsat := by
  rw [toCNF_eq, encodeBip_eq]
  exact LRATCatcher.Comparator.K35K25.encoded_unsat

/-- **No 2-colouring of `K_22` avoids `K_{3,5}` in colour 0 and `K_{2,5}` in colour 1.** -/
theorem no_good_colouring_K22 :
    ¬ ∃ a : EColouring 22 2, NoKst a 0 3 5 ∧ NoKst a 1 2 5 :=
  SB.BipBridge.no_colouring_of_toCNFV_unsat (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) vendored_unsat

/-- **`R(K_{3,5}, K_{2,5}) = 22`**: no good colouring of `K_22`, and an explicit good colouring of
`K_21`. -/
theorem k35k25_eq_22 :
    (¬ ∃ a : EColouring 22 2, NoKst a 0 3 5 ∧ NoKst a 1 2 5) ∧
    (∃ a : EColouring 21 2, NoKst a 0 3 5 ∧ NoKst a 1 2 5) :=
  ⟨no_good_colouring_K22,
   ⟨SB.Witness21.w21, SB.Witness21.witness21_kernel.1, SB.Witness21.witness21_kernel.2⟩⟩

end LRATCatcher.FaithfulK35K25

#print axioms LRATCatcher.FaithfulK35K25.no_good_colouring_K22
#print axioms LRATCatcher.FaithfulK35K25.k35k25_eq_22
