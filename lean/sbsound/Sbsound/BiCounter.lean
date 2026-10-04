/-
Bidirectional sequential counter (the degree counters of gen_variant.py, "D").

Registers `R i j` (0-based) mean "at least `j+1` of the inputs `y 0 .. y i` are true".
gen_variant.py emits, for 1-based `i` in `1..m` and `j` in `1..i` (here `i, j` 0-based
with `j ≤ i`):
  (a) s_ij → s_{i-1,j} ∨ x_i            (for j = i the register s_{i-1,i} does not exist: s_ii → x_i)
  (b) s_ij → s_{i-1,j} ∨ s_{i-1,j-1}    (j ≥ 1; for j = i: s_ii → s_{i-1,i-1})
  (c) s_{i-1,j} → s_ij                  (j ≤ i-1)
  (d) x_i ∧ s_{i-1,j-1} → s_ij          (j ≥ 1), and x_i → s_i0
Boundary i = 0: s_00 → x_0 and x_0 → s_00.
The truthful registers satisfy all of them, and the last register row reads off the count.
-/
import Mathlib
import Sbsound.Sinz

namespace SB.BiCounter

open SB.Sinz

variable {m : ℕ}

/-- The clause set as a predicate on a register assignment (0-based indices, `j ≤ i`). -/
def Clauses (y : Fin m → Bool) (R : Fin m → Fin m → Bool) : Prop :=
  -- (a) for i ≥ 1: s_ij → s_{i-1,j} ∨ x_i (j ≤ i-1), s_ii → x_i; boundary s_00 → x_0
  (∀ (i : Fin m) (hi : i.val + 1 < m) (j : Fin m), j.val ≤ i.val →
      R ⟨i.val + 1, hi⟩ j = true → R i j = true ∨ y ⟨i.val + 1, hi⟩ = true) ∧
  (∀ (i : Fin m), R i i = true → y i = true) ∧
  -- (b) s_ij → s_{i-1,j} ∨ s_{i-1,j-1} for 1 ≤ j ≤ i-1; s_ii → s_{i-1,i-1}
  (∀ (i : Fin m) (hi : i.val + 1 < m) (j : Fin m) (hj : 0 < j.val), j.val ≤ i.val →
      R ⟨i.val + 1, hi⟩ j = true → R i j = true ∨ R i ⟨j.val - 1, by omega⟩ = true) ∧
  (∀ (i : Fin m) (hi : i.val + 1 < m),
      R ⟨i.val + 1, hi⟩ ⟨i.val + 1, hi⟩ = true → R i i = true) ∧
  -- (c) monotone in i
  (∀ (i : Fin m) (hi : i.val + 1 < m) (j : Fin m), j.val ≤ i.val →
      R i j = true → R ⟨i.val + 1, hi⟩ j = true) ∧
  -- (d) carry: x_i ∧ s_{i-1,j-1} → s_ij ; x_i → s_i0
  (∀ (i : Fin m) (hi : i.val + 1 < m) (j : Fin m) (hj : 0 < j.val), j.val ≤ i.val + 1 →
      y ⟨i.val + 1, hi⟩ = true → R i ⟨j.val - 1, by omega⟩ = true → R ⟨i.val + 1, hi⟩ j = true) ∧
  (∀ (i : Fin m) (h0 : 0 < m), y i = true → R i ⟨0, h0⟩ = true)

/-- Truthful registers: `R i j` iff at least `j+1` of the first `i+1` inputs are true. -/
def truthful (y : Fin m → Bool) : Fin m → Fin m → Bool :=
  fun i j => decide (j.val + 1 ≤ prefixCount y i)

lemma prefixCount_succ_le (y : Fin m → Bool) (i : Fin m) (hi : i.val + 1 < m) :
    prefixCount y ⟨i.val + 1, hi⟩ ≤ prefixCount y i + 1 := by
  have hsub : prefixSet y ⟨i.val + 1, hi⟩ ⊆ insert (⟨i.val + 1, hi⟩ : Fin m) (prefixSet y i) := by
    intro a ha
    rw [mem_prefixSet] at ha
    rcases Nat.lt_or_ge a.val (i.val + 1) with h | h
    · exact Finset.mem_insert_of_mem (by rw [mem_prefixSet]; exact ⟨Nat.lt_succ_iff.mp h, ha.2⟩)
    · have : a = ⟨i.val + 1, hi⟩ := Fin.ext (by simp only [Fin.val_mk] at ha ⊢; omega)
      exact this ▸ Finset.mem_insert_self _ _
  calc prefixCount y ⟨i.val + 1, hi⟩ ≤ (insert (⟨i.val + 1, hi⟩ : Fin m) (prefixSet y i)).card :=
        Finset.card_le_card hsub
    _ ≤ prefixCount y i + 1 := Finset.card_insert_le _ _

lemma prefixCount_succ_of_false (y : Fin m → Bool) (i : Fin m) (hi : i.val + 1 < m)
    (hy : y ⟨i.val + 1, hi⟩ = false) :
    prefixCount y ⟨i.val + 1, hi⟩ = prefixCount y i := by
  unfold prefixCount
  congr 1
  ext a
  rw [mem_prefixSet, mem_prefixSet]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rcases Nat.lt_or_ge a.val (i.val + 1) with h | h
    · exact Nat.lt_succ_iff.mp h
    · have : a = ⟨i.val + 1, hi⟩ := Fin.ext (by simp only [Fin.val_mk] at h1 ⊢; omega)
      subst this; simp [hy] at h2
  · rintro ⟨h1, h2⟩; exact ⟨Nat.le_succ_of_le h1, h2⟩

lemma prefixCount_zero (y : Fin m → Bool) (h0 : 0 < m) :
    prefixCount y ⟨0, h0⟩ = if y ⟨0, h0⟩ = true then 1 else 0 := by
  unfold prefixCount prefixSet
  split_ifs with hy
  · rw [Finset.card_eq_one]
    refine ⟨⟨0, h0⟩, ?_⟩
    ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, -⟩; exact Fin.ext (by simpa using h1)
    · rintro rfl; exact ⟨le_refl _, hy⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a _ ⟨h1, h2⟩
    have : a = ⟨0, h0⟩ := Fin.ext (by simpa using h1)
    subst this; exact hy h2

/-- The truthful registers satisfy every clause of the bidirectional counter. -/
theorem truthful_satisfies (y : Fin m → Bool) : Clauses y (truthful y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a)
    intro i hi j _ h
    simp only [truthful, decide_eq_true_eq] at h ⊢
    by_cases hy : y ⟨i.val + 1, hi⟩ = true
    · exact Or.inr hy
    · left
      have := prefixCount_succ_of_false y i hi (by simpa using hy)
      omega
  · -- s_ii → y_i : at least i+1 among the first i+1 inputs forces y i
    intro i h
    simp only [truthful, decide_eq_true_eq] at h
    by_contra hy
    have hy' : y i = false := by simpa using hy
    have hsub : prefixSet y i ⊆ Finset.Iio i := by
      intro a ha
      rw [mem_prefixSet] at ha
      rw [Finset.mem_Iio]
      rcases Nat.lt_or_ge a.val i.val with hlt | hge
      · exact Fin.lt_def.mpr hlt
      · have : a = i := Fin.ext (by omega)
        subst this; simp [hy'] at ha
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    have hle : prefixCount y i ≤ i.val := hcard
    omega
  · -- (b)
    intro i hi j hj _ h
    simp only [truthful, decide_eq_true_eq] at h ⊢
    right
    have := prefixCount_succ_le y i hi
    omega
  · -- s_{i+1,i+1} → s_ii
    intro i hi h
    simp only [truthful, decide_eq_true_eq] at h ⊢
    have := prefixCount_succ_le y i hi
    omega
  · -- (c)
    intro i hi j _ h
    simp only [truthful, decide_eq_true_eq] at h ⊢
    exact le_trans h (prefixCount_mono y (by simp))
  · -- (d)
    intro i hi j hj _ hy h
    simp only [truthful, decide_eq_true_eq] at h ⊢
    have := prefixCount_succ y i hi hy
    omega
  · -- y_i → s_i0
    intro i h0 hy
    simp only [truthful, decide_eq_true_eq]
    simpa using one_le_prefixCount y hy

end SB.BiCounter

namespace SB.BiCounter

variable {m : ℕ}

/-- The last register row reads off the total count of true inputs. -/
theorem truthful_last (y : Fin m → Bool) (h0 : 0 < m) (k : Fin m) :
    truthful y ⟨m - 1, by omega⟩ k =
      decide (k.val + 1 ≤ ((Finset.univ : Finset (Fin m)).filter fun a => y a = true).card) := by
  unfold truthful
  congr 2
  unfold Sinz.prefixCount Sinz.prefixSet
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨by have := a.isLt; omega, h⟩

end SB.BiCounter

#print axioms SB.BiCounter.truthful_satisfies
#print axioms SB.BiCounter.truthful_last
