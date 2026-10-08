/-
  M1 (rooted census of R(K_{2,8}, K_{2,5}) at n = 22): LEMMAS_draft.md Lemmas 2.1-2.4.

    Colouring.complement_identity     Lemma 2.1   R_ij = (N-2) - d_i - d_j + 2 A_ij + C_ij
    Colouring.deficit_sum             Lemma 2.2   sum_{u != v} delta_vu = budgetOf N b r d_v   ("(A)")
    Colouring.deficit_le_budget       consequence used by the tightening: 0 <= delta_ij <= Lambda_i
    Colouring.tight_sound             Lemma 2.3   the pair intervals of `typed_encode.add_counting`
                                                  (tight=True) contain (C_ij, R_ij)
    tightTable_eq                     Lemma 2.3   the 12-row table, by `decide`, equals the Python output
    Colouring.threshold_sum           Lemma 2.4   sum_{u != v} sum_{l=1}^{min(Lambda_v, max r b)} E_{vu,l}
                                                  = Lambda_v, E as in typed_encode's (B) block

  Every statement is about an ARBITRARY colouring `K : Colouring N` (Lemma12's vocabulary) with
  ARBITRARY caps `b` (blue) and `r` (red); the cell is `N = 22, b = 4, r = 7`. The `toE` bridge
  to `SB.NoKst` is at the bottom (`*_of_NoKst`).

  PYTHON FIDELITY. `boundsPy`, `budgetOf`, `tightPy` transcribe `typed_encode.bounds`,
  `typed_encode.budget_of` and the `if tight:` block of `typed_encode.add_counting` (identical to
  `rooted_encode.local_cover_formula.caps`) line by line, over `ℤ`, so that a later encoder proof
  can cite them. `thresholdE` is the truth value the (B) block gives the variable `E`
  (P <-> A and c_red <= r-l; Q <-> not A and c_blue <= b-l; E <-> P or Q), including the `r-l < 0`
  / `b-l < 0` branches, which coincide with the formula because codegrees are nonnegative.

  Read the `#print axioms` output at the bottom; see Lemma12.lean's REGRESSION GUARD.
-/
import Lemma12

open Finset

/-! ## Python transcriptions (ℤ) -/

/-- `typed_encode.bounds(N, b, r, di, dj, A)`: identity-only `(blue_lo, blue_hi, red_lo, red_hi)`. -/
def boundsPy (N b r di dj A : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  let base := (N - 2) - di - dj + 2 * A
  (max 0 (-base), min b (r - base), max 0 base, min r (base + b))

/-- `typed_encode.budget_of(N, b, r, d) = d (r - t) + b t`, `t = N - 1 - d`. -/
def budgetOf (N b r d : ℤ) : ℤ := d * (r - (N - 1 - d)) + b * (N - 1 - d)

/-- The `tight=True` intervals of `typed_encode.add_counting`, verbatim:
```
bl, bh, rl, rh = bounds(N, b, r, di, dj, a)
lam = min(Lam[i], Lam[j])
if a == 1: rl = max(rl, r - lam)
else: bl = max(bl, b - lam)
bl = max(bl, rl - L[a]); rl = max(rl, bl + L[a]); bh = min(bh, rh - L[a]); rh = min(rh, bh + L[a])
```
(the four reassignments are sequential; each uses the values updated before it). -/
def tightPy (N b r di dj A lami lamj : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  let L := (N - 2) - di - dj + 2 * A
  let bnd := boundsPy N b r di dj A
  let lam := min lami lamj
  let bl0 := bnd.1
  let bh0 := bnd.2.1
  let rl0 := bnd.2.2.1
  let rh0 := bnd.2.2.2
  let rl1 := if A = 1 then max rl0 (r - lam) else rl0
  let bl1 := if A = 1 then bl0 else max bl0 (b - lam)
  let bl2 := max bl1 (rl1 - L)
  let rl2 := max rl1 (bl2 + L)
  let bh2 := min bh0 (rh0 - L)
  let rh2 := min rh0 (bh2 + L)
  (bl2, bh2, rl2, rh2)

/-- The intervals `typed_encode` emits at the cell `N = 22, b = 4, r = 7`. -/
def tight22 (di dj A : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  tightPy 22 4 7 di dj A (budgetOf 22 4 7 di) (budgetOf 22 4 7 dj)

/-- **Lemma 2.3, the table.** LEMMAS_draft.md's twelve rows (as `(C_lo, C_hi, R_lo, R_hi)`, colour
    `A = 1` blue, `A = 0` red), equal to what the Python computes (checked against
    `typed_encode.py` on 2026-10-06: identical). Closed by `decide`, kernel evaluation. -/
theorem tightTable_eq :
    tight22 8 8 0 = (0, 3, 4, 7) ∧ tight22 8 8 1 = (0, 1, 6, 7) ∧
    tight22 8 9 0 = (1, 4, 4, 7) ∧ tight22 8 9 1 = (0, 2, 5, 7) ∧
    tight22 8 10 0 = (0, 4, 2, 6) ∧ tight22 8 10 1 = (0, 3, 4, 7) ∧
    tight22 9 9 0 = (1, 4, 3, 6) ∧ tight22 9 9 1 = (0, 3, 4, 7) ∧
    tight22 9 10 0 = (1, 4, 2, 5) ∧ tight22 9 10 1 = (1, 4, 4, 7) ∧
    tight22 10 10 0 = (0, 4, 0, 4) ∧ tight22 10 10 1 = (1, 4, 3, 6) := by
  and_intros <;> decide

/-- The table is symmetric in the two degrees (the Python only ever evaluates `bounds` at
    `(D[i-1], D[j-1])` with `i < j`, so both orders occur). -/
theorem tight22_symm (di dj A : ℤ) : tight22 di dj A = tight22 dj di A := by
  unfold tight22 tightPy boundsPy
  simp only [min_comm (budgetOf 22 4 7 di)]
  have h1 : (22 : ℤ) - 2 - di - dj + 2 * A = 22 - 2 - dj - di + 2 * A := by ring
  rw [h1]

/-- `Λ_d = (d - 9)^2 + 3` at the cell; `Λ_8 = 4, Λ_9 = 3, Λ_10 = 4`. -/
theorem budgetOf_22 (d : ℤ) : budgetOf 22 4 7 d = (d - 9) ^ 2 + 3 := by
  unfold budgetOf; ring

namespace Colouring
variable {N : ℕ} (K : Colouring N)

/-! ## Integer-valued quantities -/

/-- Blue adjacency as `0/1`. -/
def Aij (i j : Fin N) : ℤ := if K.C i j then 1 else 0
/-- Blue degree. -/
def dg (v : Fin N) : ℤ := (K.blueNbr v).card
/-- Blue codegree `C_ij`. -/
def cB (i j : Fin N) : ℤ := (K.blueCodeg i j).card
/-- Red codegree `R_ij`. -/
def cR (i j : Fin N) : ℤ := (K.redCodeg i j).card

lemma blueCodeg_symm (i j : Fin N) : K.blueCodeg i j = K.blueCodeg j i := by
  ext w; simp only [mem_blueCodeg]; tauto
lemma redCodeg_symm (i j : Fin N) : K.redCodeg i j = K.redCodeg j i := by
  ext w; simp only [mem_redCodeg]; tauto
lemma cB_symm (i j : Fin N) : K.cB i j = K.cB j i := by unfold cB; rw [blueCodeg_symm]
lemma cR_symm (i j : Fin N) : K.cR i j = K.cR j i := by unfold cR; rw [redCodeg_symm]
lemma Aij_symm (i j : Fin N) : K.Aij i j = K.Aij j i := by unfold Aij; rw [K.symm i j]
lemma cB_nonneg (i j : Fin N) : 0 ≤ K.cB i j := by unfold cB; positivity
lemma cR_nonneg (i j : Fin N) : 0 ≤ K.cR i j := by unfold cR; positivity

/-! ## Lemma 2.1 -/

private lemma card_filter_int (p : Fin N → Prop) [DecidablePred p] :
    ((univ.filter p).card : ℤ) = ∑ w : Fin N, (if p w then (1 : ℤ) else 0) := by
  rw [Finset.card_filter]; push_cast; rfl

/-- **Lemma 2.1 (complement identity).** For distinct `i, j`:
    `R_ij = (N - 2) - d_i - d_j + 2 A_ij + C_ij`. No goodness hypothesis. -/
theorem complement_identity {i j : Fin N} (hij : i ≠ j) :
    K.cR i j = ((N : ℤ) - 2) - K.dg i - K.dg j + 2 * K.Aij i j + K.cB i j := by
  classical
  unfold cR cB dg Aij redCodeg blueCodeg blueNbr
  rw [card_filter_int, card_filter_int, card_filter_int, card_filter_int]
  have hpt : ∀ w : Fin N,
      (if (w ≠ i ∧ w ≠ j ∧ ¬K.C i w ∧ ¬K.C j w) then (1 : ℤ) else 0)
        = (1 - (if w = i then 1 else 0) - (if w = j then 1 else 0))
          - (if (w ≠ i ∧ K.C i w) then 1 else 0) - (if (w ≠ j ∧ K.C j w) then 1 else 0)
          + (if (w ≠ i ∧ w ≠ j ∧ K.C i w ∧ K.C j w) then 1 else 0)
          + (if w = j then (if K.C i j then 1 else 0) else 0)
          + (if w = i then (if K.C i j then 1 else 0) else 0) := by
    intro w
    by_cases hwi : w = i
    · subst hwi
      have : w ≠ j := hij
      simp only [this, ne_eq, not_true_eq_false, false_and, if_false, if_true, true_and,
        not_false_eq_true]
      rw [K.symm j w]; split_ifs <;> ring
    · by_cases hwj : w = j
      · subst hwj
        simp only [hwi, ne_eq, not_true_eq_false, false_and, and_false, if_false, if_true,
          not_false_eq_true, true_and]
        split_ifs <;> ring
      · simp only [hwi, hwj, ne_eq, not_false_eq_true, true_and, if_false]
        split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun w _ => hpt w)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  simp only [ne_eq] at *
  ring_nf

/-! ## Lemma 2.2: the deficit identity (A) -/

/-- The deficit of the pair `vu` (LEMMAS_draft 2.2): `r - R` on a blue pair, `b - C` on a red one. -/
def deficit (b r : ℤ) (v u : Fin N) : ℤ := if K.C v u then r - K.cR v u else b - K.cB v u

lemma deficit_symm (b r : ℤ) (v u : Fin N) : K.deficit b r v u = K.deficit b r u v := by
  unfold deficit; rw [K.symm v u, cR_symm, cB_symm]

/-- Goodness, as integer caps. -/
def Good (b r : ℕ) : Prop :=
  (∀ i j : Fin N, i ≠ j → (K.blueCodeg i j).card ≤ b) ∧
  (∀ i j : Fin N, i ≠ j → (K.redCodeg i j).card ≤ r)

lemma deficit_nonneg {b r : ℕ} (hG : K.Good b r) {v u : Fin N} (h : v ≠ u) :
    0 ≤ K.deficit b r v u := by
  unfold deficit cR cB
  have := hG.1 v u h; have := hG.2 v u h
  split_ifs <;> omega

lemma univ_erase_eq (v : Fin N) :
    (univ : Finset (Fin N)).erase v = K.blueNbr v ∪ K.redNbr v := by
  ext x
  simp only [mem_erase, mem_univ, and_true, mem_union, mem_blueNbr, mem_redNbr]
  constructor
  · intro h; by_cases hc : K.C v x
    · exact Or.inl ⟨h, hc⟩
    · exact Or.inr ⟨h, hc⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

/-- `R_vu` for `u ∈ S` is what `u` sees red inside `T`; `C_vw` for `w ∈ T` is what `w` sees blue
    inside `S`. -/
lemma cR_root (v u : Fin N) : K.cR v u = ((K.redNbr u) ∩ K.redNbr v).card := by
  unfold cR; rw [K.red_inter_T_eq_codeg v u]
lemma cB_root (v w : Fin N) : K.cB v w = ((K.blueNbr w) ∩ K.blueNbr v).card := by
  unfold cB; rw [K.blueCodeg_eq_inter, Finset.inter_comm]

/-- **Lemma 2.2 (A), general parameters.** For every vertex `v` of ANY colouring,
    `∑_{u ≠ v} δ_vu = budget_of(N, b, r, d_v)`. Goodness is not needed for the identity. -/
theorem deficit_sum (b r : ℤ) (v : Fin N) :
    ∑ u ∈ (univ : Finset (Fin N)).erase v, K.deficit b r v u
      = budgetOf N b r (K.dg v) := by
  classical
  rw [K.univ_erase_eq v, Finset.sum_union (K.blue_red_disjoint v)]
  have hS : ∑ u ∈ K.blueNbr v, K.deficit b r v u
      = ∑ u ∈ K.blueNbr v, (r - ((K.redNbr v).card - ((K.blueNbr u) ∩ K.redNbr v).card)) := by
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have hc : K.C v u := ((K.mem_blueNbr).mp hu).2
    have huT : u ∉ K.redNbr v := fun h => ((K.mem_redNbr).mp h).2 hc
    have hsplit := K.blue_red_split_card u (K.redNbr v) huT
    simp only [deficit, hc, if_true, cR_root]
    omega
  have hT : ∑ w ∈ K.redNbr v, K.deficit b r v w
      = ∑ w ∈ K.redNbr v, (b - ((K.blueNbr w) ∩ K.blueNbr v).card) := by
    refine Finset.sum_congr rfl (fun w hw => ?_)
    have hc : ¬ K.C v w := ((K.mem_redNbr).mp hw).2
    simp only [deficit, hc, Bool.false_eq_true, if_false, cB_root]
  rw [hS, hT]
  have hx := K.blue_cross_count (K.blueNbr v) (K.redNbr v)
  have hp := K.card_partition v
  have hx' : (∑ u ∈ K.blueNbr v, (((K.blueNbr u) ∩ K.redNbr v).card : ℤ))
      = ∑ w ∈ K.redNbr v, (((K.blueNbr w) ∩ K.blueNbr v).card : ℤ) := by
    exact_mod_cast hx
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hx']
  unfold budgetOf dg
  have hT' : ((K.redNbr v).card : ℤ) = N - 1 - (K.blueNbr v).card := by omega
  rw [hT']; ring

/-- (A) in the cell's closed form `(d - 9)^2 + 3`. -/
theorem deficit_sum_22 (hN : N = 22) (v : Fin N) :
    ∑ u ∈ (univ : Finset (Fin N)).erase v, K.deficit 4 7 v u = (K.dg v - 9) ^ 2 + 3 := by
  subst hN; rw [K.deficit_sum, ← budgetOf_22]; norm_num

/-- Each deficit is at most the vertex budget (a nonnegative summand is at most the sum). -/
theorem deficit_le_budget {b r : ℕ} (hG : K.Good b r) {v u : Fin N} (h : v ≠ u) :
    K.deficit b r v u ≤ budgetOf N b r (K.dg v) := by
  rw [← K.deficit_sum]
  have hu : u ∈ (univ : Finset (Fin N)).erase v := by simp [Ne.symm h]
  exact Finset.single_le_sum (f := fun u => K.deficit b r v u)
    (fun w hw => K.deficit_nonneg hG (by simpa [eq_comm] using (Finset.mem_erase.mp hw).1)) hu

lemma budget_nonneg {b r : ℕ} (hG : K.Good b r) (v : Fin N) :
    0 ≤ budgetOf N b r (K.dg v) := by
  rw [← K.deficit_sum]
  exact Finset.sum_nonneg (fun w hw =>
    K.deficit_nonneg hG (by simpa [eq_comm] using (Finset.mem_erase.mp hw).1))

/-! ## Lemma 2.3: soundness of the identity and tightened intervals -/

/-- **Lemma 2.3, identity-only form** (`typed_encode.bounds`, used untightened by
    `rooted_encode.pair_shortfall`): in a good colouring, for distinct `i, j`, the pair's actual
    `(C_ij, R_ij)` lies in `boundsPy N b r d_i d_j A_ij`. -/
theorem bounds_sound {b r : ℕ} (hG : K.Good b r) {i j : Fin N} (hij : i ≠ j) :
    let B := boundsPy N b r (K.dg i) (K.dg j) (K.Aij i j)
    B.1 ≤ K.cB i j ∧ K.cB i j ≤ B.2.1 ∧ B.2.2.1 ≤ K.cR i j ∧ K.cR i j ≤ B.2.2.2 := by
  have hid := K.complement_identity hij
  have h1 := hG.1 i j hij; have h2 := hG.2 i j hij
  have h3 := K.cB_nonneg i j; have h4 := K.cR_nonneg i j
  simp only [boundsPy]
  unfold cB cR at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [le_max_iff, max_le_iff, le_min_iff, min_le_iff] <;> omega

/-- **Lemma 2.3, tightened form** (exactly the `tight=True` intervals of `typed_encode.add_counting`
    and of `rooted_encode.local_cover_formula.caps`): in a good colouring, for distinct `i, j`, with
    `Λ` from `budgetOf` at the two ACTUAL degrees, the pair's `(C_ij, R_ij)` lies in
    `tightPy N b r d_i d_j A_ij Λ_i Λ_j`. Hence when that interval is empty for the colour `a`,
    the pair cannot have colour `a` (the Python's unit clause `[cond]`). -/
theorem tight_sound {b r : ℕ} (hG : K.Good b r) {i j : Fin N} (hij : i ≠ j) :
    let B := tightPy N b r (K.dg i) (K.dg j) (K.Aij i j)
      (budgetOf N b r (K.dg i)) (budgetOf N b r (K.dg j))
    B.1 ≤ K.cB i j ∧ K.cB i j ≤ B.2.1 ∧ B.2.2.1 ≤ K.cR i j ∧ K.cR i j ≤ B.2.2.2 := by
  have hid := K.complement_identity hij
  have h1 := hG.1 i j hij; have h2 := hG.2 i j hij
  have h3 := K.cB_nonneg i j; have h4 := K.cR_nonneg i j
  have di := K.deficit_le_budget hG hij
  have dj := K.deficit_le_budget hG (Ne.symm hij)
  rw [K.deficit_symm] at dj
  have hA : K.Aij i j = 1 ∨ K.Aij i j = 0 := by unfold Aij; split_ifs <;> simp
  have hAc : K.Aij i j = 1 ↔ K.C i j := by unfold Aij; split_ifs with h <;> simp [h]
  simp only [tightPy, boundsPy]
  unfold deficit at di dj
  unfold cB cR at *
  rcases hA with hA | hA
  · have hc : K.C i j := hAc.mp hA
    simp only [hc, if_true] at di dj
    simp only [hA, if_true]
    have hm1 := min_le_left (budgetOf N b r (K.dg i)) (budgetOf N b r (K.dg j))
    have hm2 := min_le_right (budgetOf N b r (K.dg i)) (budgetOf N b r (K.dg j))
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [le_max_iff, max_le_iff, le_min_iff, min_le_iff] <;> omega
  · have hc : ¬ K.C i j := fun h => by have := hAc.mpr h; omega
    simp only [hc, Bool.false_eq_true, if_false] at di dj
    simp only [hA, show ¬ ((0:ℤ) = 1) by norm_num, if_false]
    have hm1 := min_le_left (budgetOf N b r (K.dg i)) (budgetOf N b r (K.dg j))
    have hm2 := min_le_right (budgetOf N b r (K.dg i)) (budgetOf N b r (K.dg j))
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [le_max_iff, max_le_iff, le_min_iff, min_le_iff] <;> omega

/-- The empty-interval branch, stated on its own: if the interval for the pair's actual colour
    were empty the colouring could not be good. -/
theorem tight_nonempty {b r : ℕ} (hG : K.Good b r) {i j : Fin N} (hij : i ≠ j) :
    let B := tightPy N b r (K.dg i) (K.dg j) (K.Aij i j)
      (budgetOf N b r (K.dg i)) (budgetOf N b r (K.dg j))
    B.1 ≤ B.2.1 ∧ B.2.2.1 ≤ B.2.2.2 := by
  have h := K.tight_sound hG hij
  simp only at h ⊢
  exact ⟨h.1.trans h.2.1, h.2.2.1.trans h.2.2.2⟩

/-! ## Lemma 2.4: the threshold encoding (B) -/

/-- The truth value the (B) block of `typed_encode.add_counting` assigns to `E_{vu,l}`:
    `(A ∧ c_red ≤ r - l) ∨ (¬A ∧ c_blue ≤ b - l)`. -/
def thresholdE (b r : ℤ) (v u : Fin N) (l : ℕ) : Prop :=
  (K.C v u ∧ K.cR v u ≤ r - l) ∨ (¬ K.C v u ∧ K.cB v u ≤ b - l)

instance (b r : ℤ) (v u : Fin N) (l : ℕ) : Decidable (K.thresholdE b r v u l) := by
  unfold thresholdE; infer_instance

lemma thresholdE_iff (b r : ℤ) (v u : Fin N) (l : ℕ) :
    K.thresholdE b r v u l ↔ (l : ℤ) ≤ K.deficit b r v u := by
  unfold thresholdE deficit
  cases hC : K.C v u
  · simp only [Bool.false_eq_true, false_and, not_false_eq_true, true_and, false_or, if_false]
    omega
  · simp only [true_and, not_true_eq_false, false_and, or_false, if_true]
    omega

/-- Counting thresholds: for `0 ≤ z ≤ L`, `∑_{l=1}^{L} [l ≤ z] = z`. -/
lemma sum_thresholds (L : ℕ) (z : ℤ) (h0 : 0 ≤ z) (hL : z ≤ L) :
    (∑ l ∈ Finset.Icc 1 L, (if (l : ℤ) ≤ z then (1 : ℤ) else 0)) = z := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (Finset.Icc 1 L).filter (fun l : ℕ => (l : ℤ) ≤ z) = Finset.Icc 1 z.toNat := by
    ext l; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [this, Nat.card_Icc]; omega

/-- **Lemma 2.4.** In a good colouring, for every vertex `v`,
    `∑_{u ≠ v} ∑_{l=1}^{min(Λ_v, max(r,b))} [E_{vu,l}] = Λ_v`, with `E` exactly as the (B) block of
    `typed_encode.add_counting` defines it, INCLUDING the implementation truncation
    `min(lam, max(r, b))`. So asserting (B) excludes no good colouring. -/
theorem threshold_sum {b r : ℕ} (hG : K.Good b r) (v : Fin N) :
    let Λ := budgetOf N b r (K.dg v)
    (∑ u ∈ (univ : Finset (Fin N)).erase v,
      ∑ l ∈ Finset.Icc 1 (min Λ.toNat (max r b)),
        (if K.thresholdE b r v u l then (1 : ℤ) else 0)) = Λ := by
  intro Λ
  have hΛ : 0 ≤ Λ := K.budget_nonneg hG v
  conv_rhs => rw [show Λ = budgetOf N b r (K.dg v) from rfl, ← K.deficit_sum]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  have hvu : v ≠ u := by simpa [eq_comm] using (Finset.mem_erase.mp hu).1
  simp_rw [K.thresholdE_iff]
  apply sum_thresholds
  · exact K.deficit_nonneg hG hvu
  · have h1 := K.deficit_le_budget hG hvu
    have h2 : K.deficit b r v u ≤ max r b := by
      have := hG.1 v u hvu; have := hG.2 v u hvu
      have := K.cB_nonneg v u; have := K.cR_nonneg v u
      unfold deficit; unfold cB cR at *; split_ifs <;> omega
    push_cast
    simp only [le_min_iff]
    exact ⟨by omega, by push_cast at h2; exact h2⟩

/-! ## Bridge to `SB.NoKst` -/

theorem good_of_NoKst (K : Colouring N) (hblue : SB.NoKst (toE K) 1 2 5)
    (hred : SB.NoKst (toE K) 0 2 8) : K.Good 4 7 :=
  ⟨fun _ _ h => cap_of_NoKst_blue K 5 hblue h, fun _ _ h => cap_of_NoKst_red K 8 hred h⟩

/-- Lemma 2.3 at the cell, in the portfolio's language: the emitted intervals (`tight22`) are
    satisfied by every pair of every colouring of `K_22` without blue `K_{2,5}` / red `K_{2,8}`. -/
theorem tight22_sound_NoKst (hN : N = 22) (K : Colouring N) (hblue : SB.NoKst (toE K) 1 2 5)
    (hred : SB.NoKst (toE K) 0 2 8) {i j : Fin N} (hij : i ≠ j) :
    let B := tight22 (K.dg i) (K.dg j) (K.Aij i j)
    B.1 ≤ K.cB i j ∧ K.cB i j ≤ B.2.1 ∧ B.2.2.1 ≤ K.cR i j ∧ K.cR i j ≤ B.2.2.2 := by
  have h := K.tight_sound (K.good_of_NoKst hblue hred) hij
  subst hN
  simpa [tight22] using h

theorem threshold_sum_NoKst (hN : N = 22) (K : Colouring N) (hblue : SB.NoKst (toE K) 1 2 5)
    (hred : SB.NoKst (toE K) 0 2 8) (v : Fin N) :
    let Λ := budgetOf N 4 7 (K.dg v)
    (∑ u ∈ (univ : Finset (Fin N)).erase v,
      ∑ l ∈ Finset.Icc 1 (min Λ.toNat (max 7 4)),
        (if K.thresholdE 4 7 v u l then (1 : ℤ) else 0)) = Λ := by
  have := K.threshold_sum (K.good_of_NoKst hblue hred) v
  simpa using this

end Colouring

#print axioms tightTable_eq
#print axioms tight22_symm
#print axioms budgetOf_22
#print axioms Colouring.complement_identity
#print axioms Colouring.deficit_sum
#print axioms Colouring.deficit_sum_22
#print axioms Colouring.deficit_le_budget
#print axioms Colouring.budget_nonneg
#print axioms Colouring.bounds_sound
#print axioms Colouring.tight_sound
#print axioms Colouring.tight_nonempty
#print axioms Colouring.thresholdE_iff
#print axioms Colouring.threshold_sum
#print axioms Colouring.good_of_NoKst
#print axioms Colouring.tight22_sound_NoKst
#print axioms Colouring.threshold_sum_NoKst
