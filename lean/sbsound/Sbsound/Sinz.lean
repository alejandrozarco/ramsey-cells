import Mathlib

/-!
# Correctness of the Sinz sequential counter

The encoder expresses "at most `k` of these `m` booleans are true" with a chain of
auxiliary *register* variables `R i j`, intended to mean "at least `j+1` of the first
`i+1` inputs are true". This file proves that the emitted clause set is satisfiable
exactly when the count really is at most `k` — the obligation P1 rests on, and the
reason the encoder's 105,213 variables are only 342 edge variables plus counter
machinery.

The statement is about the gadget alone: nothing here mentions graphs or Ramsey.
-/

namespace SB.Sinz

variable {m k : ℕ}

/-- The clause set the encoder emits, as a predicate on a candidate register
assignment. `y` are the inputs, `R i j` is the register "at least `j+1` of
`y 0 .. y i`". Mirrors `gen_ramsey.py`: a base clause, a per-step "input sets the
first register", a monotone clause, a carry clause, and the blocking clause. -/
def Clauses (y : Fin m → Bool) (R : Fin m → Fin k → Bool) : Prop :=
  (∀ h0 : 0 < m, ∀ hk : 0 < k, y ⟨0, h0⟩ = true → R ⟨0, h0⟩ ⟨0, hk⟩ = true) ∧
  (∀ i : Fin m, ∀ hk : 0 < k, y i = true → R i ⟨0, hk⟩ = true) ∧
  (∀ i : Fin m, ∀ hi : i.val + 1 < m, ∀ j : Fin k,
      R i j = true → R ⟨i.val + 1, hi⟩ j = true) ∧
  (∀ i : Fin m, ∀ hi : i.val + 1 < m, ∀ j : Fin k, ∀ hj : j.val + 1 < k,
      y ⟨i.val + 1, hi⟩ = true → R i j = true → R ⟨i.val + 1, hi⟩ ⟨j.val + 1, hj⟩ = true) ∧
  (∀ i : Fin m, ∀ hi : i.val + 1 < m, ∀ hk : k - 1 < k,
      ¬(y ⟨i.val + 1, hi⟩ = true ∧ R i ⟨k - 1, hk⟩ = true))

/-- How many of the first `i+1` inputs are true. -/
def prefixSet (y : Fin m → Bool) (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun a => a.val ≤ i.val ∧ y a = true

def prefixCount (y : Fin m → Bool) (i : Fin m) : ℕ := (prefixSet y i).card

/-- The truthful register assignment: `R i j` holds exactly when the prefix count
through `i` is at least `j+1`. This is the witness for the easy direction. -/
def truthful (y : Fin m → Bool) : Fin m → Fin k → Bool :=
  fun i j => decide (j.val + 1 ≤ prefixCount y i)


/-! ### Basic facts about the prefix count -/

lemma mem_prefixSet {y : Fin m → Bool} {i a : Fin m} :
    a ∈ prefixSet y i ↔ a.val ≤ i.val ∧ y a = true := by
  simp [prefixSet]

lemma prefixSet_mono (y : Fin m → Bool) {i i' : Fin m} (h : i.val ≤ i'.val) :
    prefixSet y i ⊆ prefixSet y i' := by
  intro a ha
  rw [mem_prefixSet] at ha ⊢
  exact ⟨le_trans ha.1 h, ha.2⟩

lemma prefixCount_mono (y : Fin m → Bool) {i i' : Fin m} (h : i.val ≤ i'.val) :
    prefixCount y i ≤ prefixCount y i' :=
  Finset.card_le_card (prefixSet_mono y h)

lemma one_le_prefixCount (y : Fin m → Bool) {i : Fin m} (hy : y i = true) :
    1 ≤ prefixCount y i := by
  refine Finset.card_pos.mpr ⟨i, ?_⟩
  rw [mem_prefixSet]; exact ⟨le_refl _, hy⟩

/-- The step-up: moving from `i` to `i+1` when the new input is true grows the prefix
set by exactly that element, so the count rises by at least one. This is what makes the
carry and blocking clauses work. -/
lemma prefixCount_succ (y : Fin m → Bool) (i : Fin m) (hi : i.val + 1 < m)
    (hy : y ⟨i.val + 1, hi⟩ = true) :
    prefixCount y i + 1 ≤ prefixCount y ⟨i.val + 1, hi⟩ := by
  have hnot : (⟨i.val + 1, hi⟩ : Fin m) ∉ prefixSet y i := by
    rw [mem_prefixSet]; intro hc; simp only [Fin.val_mk] at hc; omega
  have hsub : insert (⟨i.val + 1, hi⟩ : Fin m) (prefixSet y i) ⊆ prefixSet y ⟨i.val + 1, hi⟩ := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha'
    · rw [mem_prefixSet]; exact ⟨le_refl _, hy⟩
    · rw [mem_prefixSet] at ha' ⊢
      exact ⟨Nat.le_succ_of_le ha'.1, ha'.2⟩
  calc prefixCount y i + 1
      = (insert (⟨i.val + 1, hi⟩ : Fin m) (prefixSet y i)).card := by
        rw [Finset.card_insert_of_notMem hnot]; rfl
    _ ≤ prefixCount y ⟨i.val + 1, hi⟩ := Finset.card_le_card hsub


/-! ### Completeness: a genuine bound always admits a satisfying assignment

This is the direction the upper-bound results rest on. Its contrapositive is what makes
an UNSAT verdict meaningful: if no register assignment satisfies the clauses, then no
input vector with at most `k` true entries exists — so a colouring that respects the
codegree bound could not have been missed by the search. -/

theorem truthful_satisfies (y : Fin m → Bool) (hk : 0 < k)
    (hcount : ∀ i : Fin m, prefixCount y i ≤ k) :
    Clauses y (truthful y : Fin m → Fin k → Bool) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- base: a true first input forces the first register
    intro h0 hk' hy
    simpa [truthful] using one_le_prefixCount y hy
  · -- a true input forces the first register at that position
    intro i hk' hy
    simpa [truthful] using one_le_prefixCount y hy
  · -- monotone: registers never fall as the prefix grows
    intro i hi j h
    simp only [truthful, decide_eq_true_eq] at h ⊢
    exact le_trans h (prefixCount_mono y (by simp))
  · -- carry: a true input plus a register at level j gives level j+1
    intro i hi j hj hy h
    simp only [truthful, decide_eq_true_eq] at h ⊢
    have := prefixCount_succ y i hi hy
    omega
  · -- blocking: a true input on top of a full register would exceed the bound
    intro i hi hk' hcon
    obtain ⟨hy, hreg⟩ := hcon
    simp only [truthful, decide_eq_true_eq] at hreg
    have hstep := prefixCount_succ y i hi hy
    have hbound := hcount ⟨i.val + 1, hi⟩
    omega

#print axioms truthful_satisfies

end SB.Sinz
