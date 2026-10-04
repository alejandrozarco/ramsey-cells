/-
DOL clause layer, part 1: variables and inputs.

* `DAux`: the new auxiliary variables of gen_variant.py — degree registers `dreg v i j`
  (0-based `i, j`, meaning "at least j+1 colour-c edges among v's first i+1 other vertices"),
  the gate `eqv v`, and the witnesses `diff v k` (k 1-based).
* `DVar n r = SVar n r ⊕ DAux`; the deposited clause families lift by `liftD`.
* `degInputs a c v`: the colour-`c` input vector of `v` in label order of the other endpoint,
  through `Fin.succAbove v` (the order embedding that skips `v`); its true-count is `deg a c v`.
-/
import Mathlib
import Sbsound.SBClauses
import Sbsound.SBDegree
import Sbsound.BiCounter

namespace SB

variable {n r : ℕ}

/-- New auxiliary variables of the DOL families. -/
inductive DAux : Type
  | dreg (v i j : ℕ)
  | eqv (v : ℕ)
  | diff (v k : ℕ)
  deriving DecidableEq

abbrev DVar (n r : ℕ) := SVar n r ⊕ DAux
abbrev DAssign (n r : ℕ) := DVar n r → Bool
abbrev DLit (n r : ℕ) := DVar n r × Bool
abbrev DClause (n r : ℕ) := List (DLit n r)

def evalDLit (β : DAssign n r) : DLit n r → Bool
  | (x, true) => β x
  | (x, false) => !β x

def satDClause (β : DAssign n r) (C : DClause n r) : Bool := C.any (evalDLit β)

def satDCNF (β : DAssign n r) (F : List (DClause n r)) : Prop :=
  ∀ C ∈ F, satDClause β C = true

lemma satDCNF_append {β : DAssign n r} {F₁ F₂ : List (DClause n r)} :
    satDCNF β (F₁ ++ F₂) ↔ satDCNF β F₁ ∧ satDCNF β F₂ := by
  simp [satDCNF, or_imp, forall_and]

lemma satDClause_of_mem {β : DAssign n r} {C : DClause n r} {l : DLit n r}
    (hl : l ∈ C) (hv : evalDLit β l = true) : satDClause β C = true :=
  List.any_eq_true.mpr ⟨l, hl, hv⟩

/-- Lift a clause over the deposited variables. -/
def liftD (C : SClause n r) : DClause n r := C.map fun l => (Sum.inl l.1, l.2)

lemma evalDLit_lift (β : DAssign n r) (l : SLit n r) :
    evalDLit β (Sum.inl l.1, l.2) = evalSLit (β ∘ Sum.inl) l := by
  rcases l with ⟨x, b⟩; cases b <;> rfl

lemma satDClause_liftD (β : DAssign n r) (C : SClause n r) :
    satDClause β (liftD C) = satSClause (β ∘ Sum.inl) C := by
  unfold satDClause satSClause liftD
  rw [List.any_map]
  congr 1
  funext l
  exact evalDLit_lift β l

lemma satDCNF_liftD (β : DAssign n r) (F : List (SClause n r)) :
    satDCNF β (F.map liftD) ↔ satSCNF (β ∘ Sum.inl) F := by
  simp only [satDCNF, satSCNF, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, satDClause_liftD]

/-- Variable shorthands. -/
abbrev dregvar (v i j : ℕ) : DVar n r := Sum.inr (DAux.dreg v i j)
abbrev eqvvar (v : ℕ) : DVar n r := Sum.inr (DAux.eqv v)
abbrev diffvar (v k : ℕ) : DVar n r := Sum.inr (DAux.diff v k)
abbrev dpos (x : DVar n r) : DLit n r := (x, true)
abbrev dneg (x : DVar n r) : DLit n r := (x, false)

/-! ### Neighbour inputs -/

open Classical in
/-- Colour-`c` input vector of vertex `v`: entry `i` is the colour test of the edge from `v`
to the `i`-th other vertex in label order (`Fin.succAbove v` skips `v`). -/
noncomputable def degInputs (a : EColouring (n + 1) r) (c : Fin r) (v : Fin (n + 1)) :
    Fin n → Bool :=
  fun i => decide ((colourGraph a c).Adj v (v.succAbove i))

/-- The number of true inputs is the colour-`c` degree. -/
theorem card_degInputs (a : EColouring (n + 1) r) (c : Fin r) (v : Fin (n + 1)) :
    ((Finset.univ : Finset (Fin n)).filter fun i => degInputs a c v i = true).card = deg a c v := by
  classical
  unfold deg degInputs
  refine Finset.card_bij (fun i _ => v.succAbove i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hi ⊢
    exact hi
  · intro i _ j _ h
    exact Fin.succAbove_right_injective h
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    have hne : w ≠ v := fun h => by subst h; exact (colourGraph a c).irrefl hw
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hne
    refine ⟨i, ?_, hi⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    rw [hi]; exact hw

/-- Degree output as a Boolean: `k ≤ deg a c v` (k 1-based). -/
noncomputable def dout (a : EColouring (n + 1) r) (c : Fin r) (v : Fin (n + 1)) (k : ℕ) : Bool :=
  decide (k ≤ deg a c v)

/-- The truthful last register row of the degree counter is the degree output. -/
theorem truthful_last_eq_dout (a : EColouring (n + 1) r) (c : Fin r) (v : Fin (n + 1))
    (h0 : 0 < n) (k : Fin n) :
    BiCounter.truthful (degInputs a c v) ⟨n - 1, by omega⟩ k = dout a c v (k.val + 1) := by
  rw [BiCounter.truthful_last _ h0 k, card_degInputs]; rfl

end SB

#print axioms SB.card_degInputs
#print axioms SB.truthful_last_eq_dout
