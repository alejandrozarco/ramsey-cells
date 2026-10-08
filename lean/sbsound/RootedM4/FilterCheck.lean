/-
# M4, part 5d: a kernel-evaluable form of `validate.fail_iii`

`failIIIL k D m U` computes `validate.fail_iii(word, k, degrees, U)` on the word with bitmask `m`
using lists over `0..k-1` only (no `Finset`), so that `decide +kernel` can evaluate it on many
words. `failIIIL_eq` proves it equal to M1's `failIIIPy k (gW k (wbits E m)) D (finU k U)`.
-/
import RootedM4.CoverSound
import RootedM4.CoverBase

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace SB.Rooted.M4.Cover
open SB.Rooted.M4 Finset

/-- The graph of a word (`cnfgen.graph_of`). -/
def gW (k : ℕ) (wb : List Bool) : Fin k → Fin k → Bool := fun a b =>
  if a.val < b.val then wb.getD (pIdx k a.val b.val) false
  else if b.val < a.val then wb.getD (pIdx k b.val a.val) false else false

/-- The vertex set of a bitmask. -/
def finU (k U : ℕ) : Finset (Fin k) := univ.filter (fun a => U.testBit a.val)

/-- The adjacency of the word with bitmask `m` (`cnfgen.graph_of`). -/
def gN (k m a b : ℕ) : Bool :=
  if a < b then m.testBit (pIdx k a b) else if b < a then m.testBit (pIdx k b a) else false

/-- `validate.fail_iii`, on lists. -/
def failIIIL (k : ℕ) (D : ℕ → ℤ) (m U : ℕ) : Bool :=
  let mm : ℤ := 21 - k
  let idx := (List.range k).filter (fun a => U.testBit a)
  let pr : ℕ → ℤ := fun a => (((List.range k).filter (fun b => gN k m a b)).length : ℤ)
  let T : ℤ := (idx.map (fun a => D a - 1 - pr a)).sum
  let q := T / mm
  let r := T % mm
  let lhs := mm * q * (q - 1) / 2 + r * q
  let rhs : ℤ := (idx.map (fun a => ((idx.filter (fun b => decide (a < b))).map (fun b =>
      (if gN k m a b then min 4 (D a + D b - 15) else 4) - 1 -
        (((List.range k).filter (fun c => gN k m a c && gN k m b c)).length : ℤ))).sum)).sum
  decide (lhs > rhs)

/-- The graph of the word of a bitmask, as `gW` reads it. -/
def gWb (k E m : ℕ) : Fin k → Fin k → Bool := gW k (wbits E m)

theorem wbits_getD (E m n : ℕ) (hn : n < E) : (wbits E m).getD n false = m.testBit n := by
  unfold wbits
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn]
  rfl

theorem gW_wbits {k : ℕ} (hp : PairFacts k) (m : ℕ) (a b : Fin k) :
    gW k (wbits (Ek k) m) a b = gN k m a.val b.val := by
  unfold gW gN
  by_cases h1 : a.val < b.val
  · rw [if_pos h1, if_pos h1, wbits_getD _ _ _ (hp.surj _ _ h1 b.isLt).1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : b.val < a.val
    · rw [if_pos h2, if_pos h2, wbits_getD _ _ _ (hp.surj _ _ h2 a.isLt).1]
    · rw [if_neg h2, if_neg h2]

theorem range_eq_map_finRange (k : ℕ) : List.range k = (List.finRange k).map Fin.val := by
  apply List.ext_getElem (by simp)
  intro i h1 h2; simp

theorem count_finK {k : ℕ} (P : Fin k → Prop) [DecidablePred P] (Q : ℕ → Bool)
    (hQ : ∀ x : Fin k, Q x.val = decide (P x)) :
    ((List.range k).filter Q).length = (univ.filter P).card := by
  rw [range_eq_map_finRange, List.filter_map, List.length_map]
  have : (List.finRange k).filter (Q ∘ Fin.val) = (List.finRange k).filter (fun x => decide (P x)) := by
    apply List.filter_congr; intro x _; simp [hQ]
  rw [this, ← List.toFinset_card_of_nodup ((List.nodup_finRange k).filter _), List.toFinset_filter,
    List.toFinset_finRange]
  simp

/-- A `Finset` sum over a filter of `Fin k` as a list sum over `0..k-1`. -/
theorem sum_fin_filter {k : ℕ} (P : ℕ → Bool) (f : ℕ → ℤ) :
    ∑ a ∈ (univ : Finset (Fin k)).filter (fun a => P a.val = true), f a.val =
      (((List.range k).filter P).map f).sum := by
  have h1 : (univ : Finset (Fin k)).filter (fun a => P a.val = true) =
      ((List.finRange k).filter (fun a => P a.val)).toFinset := by
    ext a; simp
  rw [h1, List.sum_toFinset _ ((List.nodup_finRange k).filter _)]
  rw [range_eq_map_finRange, List.filter_map, List.map_map]
  rfl

theorem failIIIL_eq {k : ℕ} (hp : PairFacts k) (D : ℕ → ℤ) (m U : ℕ) :
    failIIIL k D m U = failIIIPy k (gW k (wbits (Ek k) m)) (fun a => D a.val) (finU k U) := by
  set g := gW k (wbits (Ek k) m) with hg
  have hgN : ∀ a b : Fin k, g a b = gN k m a.val b.val := gW_wbits hp m
  have hpop : ∀ a : Fin k, (popRow g a : ℤ) =
      (((List.range k).filter (fun b => gN k m a.val b)).length : ℤ) := by
    intro a; unfold popRow
    rw [count_finK (fun b => g a b = true) (fun b => gN k m a.val b)
      (fun b => by show gN k m a.val b.val = decide (g a b = true); rw [hgN]; simp)]
  have hand : ∀ a b : Fin k, (popAnd g a b : ℤ) =
      (((List.range k).filter (fun c => gN k m a.val c && gN k m b.val c)).length : ℤ) := by
    intro a b; unfold popAnd
    rw [count_finK (fun c => g a c = true ∧ g b c = true) (fun c => gN k m a.val c && gN k m b.val c)
      (fun c => by
        show (gN k m a.val c.val && gN k m b.val c.val) = decide (g a c = true ∧ g b c = true)
        rw [hgN, hgN]; simp)]
  have hT : ∑ a ∈ finU k U, (D a.val - 1 - (popRow g a : ℤ)) =
      (((List.range k).filter (fun a => U.testBit a)).map (fun a => D a - 1 -
        (((List.range k).filter (fun b => gN k m a b)).length : ℤ))).sum := by
    unfold finU
    rw [← sum_fin_filter]
    apply Finset.sum_congr rfl; intro a _; rw [hpop]
  have hR : ∑ p ∈ ltPairs (finU k U), (UgenPy g (fun a => D a.val) p.1 p.2 - 1 - (popAnd g p.1 p.2 : ℤ)) =
      (((List.range k).filter (fun a => U.testBit a)).map (fun a =>
        ((((List.range k).filter (fun a => U.testBit a)).filter (fun b => decide (a < b))).map (fun b =>
          (if gN k m a b then min 4 (D a + D b - 15) else 4) - 1 -
            (((List.range k).filter (fun c => gN k m a c && gN k m b c)).length : ℤ))).sum)).sum := by
    unfold ltPairs
    rw [Finset.sum_filter, Finset.sum_product]
    unfold finU
    rw [← sum_fin_filter (fun a => U.testBit a) (fun a =>
        ((((List.range k).filter (fun a => U.testBit a)).filter (fun b => decide (a < b))).map (fun b =>
          (if gN k m a b then min 4 (D a + D b - 15) else 4) - 1 -
            (((List.range k).filter (fun c => gN k m a c && gN k m b c)).length : ℤ))).sum)]
    apply Finset.sum_congr rfl; intro a _
    rw [← Finset.sum_filter, List.filter_filter]
    have hset : ((univ : Finset (Fin k)).filter (fun b => U.testBit b.val = true)).filter (fun b => a < b) =
        (univ : Finset (Fin k)).filter (fun b => (decide (a.val < b.val) && U.testBit b.val) = true) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    rw [hset, ← sum_fin_filter (fun b => decide (a.val < b) && U.testBit b)
      (fun b => (if gN k m a.val b then min 4 (D a.val + D b - 15) else 4) - 1 -
        (((List.range k).filter (fun c => gN k m a.val c && gN k m b c)).length : ℤ))]
    apply Finset.sum_congr rfl; intro b _
    unfold UgenPy; rw [hgN, hand]
  unfold failIIIL failIIIPy
  simp only
  rw [hT, hR]

end SB.Rooted.M4.Cover
