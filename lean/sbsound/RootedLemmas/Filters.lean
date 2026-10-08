/-
  M1 (rooted census of R(K_{2,8}, K_{2,5}) at n = 22): LEMMAS_draft.md Section 4 —
  filters (i), (ii), (iii) on the root-neighbourhood graph H, and Corollary 4.3 (shortfall).

  CORE (colouring level, arbitrary N, caps b, r; root v, S = blueNbr v, W = redNbr v):
    Colouring.filter_i_core        h_i ≤ b  ∧  h_i + |W| + 1 ≤ r + d_i                  (i ∈ S)
    Colouring.filter_ii_core       Σ_S d_i - |S| - Σ_S h_i ≤ b|W|  ∧  |S||W| - Σ_S d_i + |S| + Σ_S h_i ≤ r|S|
    Colouring.filter_iii_core      m q(q-1) + 2ρq ≤ Σ_{(i,j) ∈ U.offDiag} (cap_ij - 1 - q_ij)   (U ⊆ S)
    Colouring.shortfall_core       Σ_{U.offDiag} (cap_ij - C_ij) + m q(q-1) + 2ρq ≤ Σ_{U.offDiag} (cap_ij - 1 - q_ij)
  for ANY cap function with C_ij ≤ cap_ij on U's pairs; doubled (ordered pairs) so no division.

  The Python-faithful (labelled, `Fin k`) forms are in RootedLemmas/FiltersPy.lean.
-/
import RootedLemmas.Deficit

open Finset

/-! ## Two arithmetic lemmas -/

/-- **Convexity (tangent-line form).** For integers `z_w` over a nonempty `W` with
    `T = Σ z_w`, `m = |W|`, `q = T / m`, `ρ = T % m` (Euclidean = Python floor for `m > 0`):
    `m q (q-1) + 2 ρ q ≤ Σ z_w (z_w - 1)`. This is the doubled form of
    `m C(q,2) + ρ q ≤ Σ C(z_w, 2)`, LEMMAS_draft (4). Uses `(z-q)(z-q-1) ≥ 0`, no balancing. -/
theorem convexity_floor {α : Type*} (W : Finset α) (z : α → ℤ) (hm : 0 < W.card) :
    let T := ∑ w ∈ W, z w
    let m : ℤ := W.card
    m * (T / m) * (T / m - 1) + 2 * (T % m) * (T / m) ≤ ∑ w ∈ W, z w * (z w - 1) := by
  intro T m
  set q := T / m
  have hdm : m * q + T % m = T := Int.mul_ediv_add_emod T m
  have hpt : ∀ w ∈ W, q * (q - 1) + 2 * q * (z w - q) ≤ z w * (z w - 1) := by
    intro w _
    have : 0 ≤ (z w - q) * (z w - q - 1) := by
      rcases le_or_gt (z w - q) 0 with h | h
      · nlinarith
      · nlinarith
    nlinarith
  have hs := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hs
  have hT : ∑ w ∈ W, z w = T := rfl
  rw [hT] at hs
  have : (W.card : ℤ) = m := rfl
  rw [this] at hs
  have e : T - m * q = T % m := by omega
  calc m * q * (q - 1) + 2 * (T % m) * q
      = m * (q * (q - 1)) + 2 * q * (T - m * q) := by rw [e]; ring
    _ ≤ _ := by linarith

/-- Ordered pairs vs. `i < j` pairs, for a symmetric summand. -/
theorem sum_offDiag_eq_two_sum_lt {α : Type*} [LinearOrder α] (A : Finset α)
    (F : α → α → ℤ) (hF : ∀ i j, F i j = F j i) :
    ∑ p ∈ A.offDiag, F p.1 p.2 = 2 * ∑ p ∈ (A ×ˢ A).filter (fun p => p.1 < p.2), F p.1 p.2 := by
  classical
  have hsplit : A.offDiag = (A ×ˢ A).filter (fun p => p.1 < p.2) ∪
      (A ×ˢ A).filter (fun p => p.2 < p.1) := by
    ext p
    simp only [mem_offDiag, mem_union, mem_filter, mem_product]
    constructor
    · rintro ⟨h1, h2, hne⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨⟨h1, h2⟩, h⟩
      · exact Or.inr ⟨⟨h1, h2⟩, h⟩
    · rintro (⟨⟨h1, h2⟩, h⟩ | ⟨⟨h1, h2⟩, h⟩)
      · exact ⟨h1, h2, ne_of_lt h⟩
      · exact ⟨h1, h2, ne_of_gt h⟩
  have hdisj : Disjoint ((A ×ˢ A).filter (fun p => p.1 < p.2))
      ((A ×ˢ A).filter (fun p => p.2 < p.1)) := by
    rw [Finset.disjoint_left]
    rintro p hp hp'
    simp only [mem_filter] at hp hp'
    exact absurd (hp.2.trans hp'.2) (lt_irrefl _)
  have himg : (A ×ˢ A).filter (fun p => p.2 < p.1)
      = ((A ×ˢ A).filter (fun p => p.1 < p.2)).image Prod.swap := by
    ext p
    simp only [mem_image, mem_filter, mem_product, Prod.exists, Prod.swap_prod_mk]
    constructor
    · rintro ⟨⟨h1, h2⟩, h⟩
      exact ⟨p.2, p.1, ⟨⟨h2, h1⟩, h⟩, rfl⟩
    · rintro ⟨a, b, ⟨⟨h1, h2⟩, h⟩, rfl⟩
      exact ⟨⟨h2, h1⟩, h⟩
  rw [hsplit, Finset.sum_union hdisj, himg,
    Finset.sum_image (fun x _ y _ h => Prod.swap_injective h)]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [two_mul]
  congr 1
  exact Finset.sum_congr rfl (fun p _ => hF p.2 p.1)

namespace Colouring
variable {N : ℕ} (K : Colouring N)

lemma blue_mem_symm (u w : Fin N) : w ∈ K.blueNbr u ↔ u ∈ K.blueNbr w := by
  simp only [mem_blueNbr]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h1, by rw [K.symm w u]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h1, by rw [K.symm u w]; exact h2⟩

/-! ## H-quantities -/

/-- `h_i = d_H(i)`: blue neighbours of `i` inside the root's blue neighbourhood. -/
def hdeg (v i : Fin N) : ℕ := ((K.blueNbr i) ∩ K.blueNbr v).card
/-- `q_ij`: common blue neighbours of `i, j` inside `S = N(v)`. -/
def qH (v i j : Fin N) : ℕ := ((K.blueNbr i ∩ K.blueNbr j) ∩ K.blueNbr v).card
/-- `(XᵀX)_ij`: common blue neighbours of `i, j` inside `W`. -/
def xW (v i j : Fin N) : ℕ := ((K.blueNbr i ∩ K.blueNbr j) ∩ K.redNbr v).card

/-- Splitting a set that contains the root into root / `S`-part / `W`-part. -/
lemma card_split_root (v : Fin N) (X : Finset (Fin N)) (hv : v ∈ X) :
    X.card = 1 + (X ∩ K.blueNbr v).card + (X ∩ K.redNbr v).card := by
  classical
  have hX : X = insert v ((X ∩ K.blueNbr v) ∪ (X ∩ K.redNbr v)) := by
    ext x
    simp only [mem_insert, mem_union, mem_inter]
    constructor
    · intro hx
      have hu : x ∈ (univ : Finset (Fin N)) := mem_univ x
      rw [K.univ_split v, mem_insert, mem_union] at hu
      rcases hu with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨hx, h⟩)
      · exact Or.inr (Or.inr ⟨hx, h⟩)
    · rintro (rfl | ⟨hx, _⟩ | ⟨hx, _⟩)
      · exact hv
      · exact hx
      · exact hx
  have hnv : v ∉ (X ∩ K.blueNbr v) ∪ (X ∩ K.redNbr v) := by
    simp only [mem_union, mem_inter, mem_blueNbr, mem_redNbr, ne_eq, not_true_eq_false,
      false_and, and_false, or_self, not_false_eq_true]
  have hd : Disjoint (X ∩ K.blueNbr v) (X ∩ K.redNbr v) := by
    rw [Finset.disjoint_left]
    rintro x hx hx'
    exact (Finset.disjoint_left.mp (K.blue_red_disjoint v)) (mem_inter.mp hx).2
      (mem_inter.mp hx').2
  conv_lhs => rw [hX]
  rw [card_insert_of_notMem hnv, card_union_of_disjoint hd]; ring

lemma root_mem_blue (v i : Fin N) (hi : i ∈ K.blueNbr v) : v ∈ K.blueNbr i :=
  (K.blue_mem_symm v i).mp hi

/-- `d_i = 1 + h_i + |N(i) ∩ W|` for `i ∈ S`. -/
lemma deg_split (v i : Fin N) (hi : i ∈ K.blueNbr v) :
    (K.blueNbr i).card = 1 + K.hdeg v i + ((K.blueNbr i) ∩ K.redNbr v).card :=
  K.card_split_root v _ (K.root_mem_blue v i hi)

/-- `C_ij = 1 + q_ij + (XᵀX)_ij` for `i, j ∈ S` (LEMMAS_draft (4.7) setting). -/
lemma codeg_split (v i j : Fin N) (hi : i ∈ K.blueNbr v) (hj : j ∈ K.blueNbr v) :
    (K.blueCodeg i j).card = 1 + K.qH v i j + K.xW v i j := by
  rw [K.blueCodeg_eq_inter]
  exact K.card_split_root v _ (mem_inter.mpr ⟨K.root_mem_blue v i hi, K.root_mem_blue v j hj⟩)

/-! ## Filter (i) -/

/-- **Filter (i), core.** For `i ∈ S`: `h_i = C_{vi} ≤ b`, and `R_{vi} ≤ r` reads
    `h_i + |W| + 1 ≤ r + d_i`. At `N = 22` (`|W| = 21 - k`) this is `h_i ≤ min(4, k + D_i - 15)`. -/
theorem filter_i_core {b r : ℕ} (hG : K.Good b r) (v i : Fin N) (hi : i ∈ K.blueNbr v) :
    K.hdeg v i ≤ b ∧ K.hdeg v i + (K.redNbr v).card + 1 ≤ r + (K.blueNbr i).card := by
  have hvi : v ≠ i := ((K.mem_blueNbr).mp hi).1.symm
  have hc : K.C v i := ((K.mem_blueNbr).mp hi).2
  have huT : i ∉ K.redNbr v := fun h => ((K.mem_redNbr).mp h).2 hc
  have h1 := hG.1 v i hvi
  have h2 := hG.2 v i hvi
  have hsplit := K.blue_red_split_card i (K.redNbr v) huT
  have hd := K.deg_split v i hi
  have e1 : K.hdeg v i = (K.blueCodeg v i).card := by
    unfold hdeg; rw [K.blueCodeg_eq_inter, Finset.inter_comm]
  have e2 : (K.redCodeg v i).card = ((K.redNbr i) ∩ K.redNbr v).card := by
    rw [K.red_inter_T_eq_codeg v i]
  omega

/-! ## Filter (ii) -/

/-- `Σ_{w ∈ W} C_{vw} = Σ_{i ∈ S} (d_i - 1 - h_i)` (blue walks of length two from the root). -/
lemma sum_W_codeg (v : Fin N) :
    (∑ w ∈ K.redNbr v, ((K.blueNbr w) ∩ K.blueNbr v).card : ℤ)
      = ∑ i ∈ K.blueNbr v, (((K.blueNbr i).card : ℤ) - 1 - K.hdeg v i) := by
  have hx := K.blue_cross_count (K.blueNbr v) (K.redNbr v)
  have : ∀ i ∈ K.blueNbr v, (((K.blueNbr i).card : ℤ) - 1 - K.hdeg v i)
      = ((K.blueNbr i) ∩ K.redNbr v).card := by
    intro i hi; have := K.deg_split v i hi; omega
  rw [Finset.sum_congr rfl this]
  exact_mod_cast hx.symm

/-- **Filter (ii), core** (LEMMAS_draft (4.3)/(4.4): `E ≥ 0`, `F ≥ 0`). With `k = |S|`,
    `m = |W|`, `SD = Σ_S d_i`, `P = Σ_S h_i = 2 e(H)`:
    `SD - k - P ≤ b m` and `k m - SD + k + P ≤ r k`. -/
theorem filter_ii_core {b r : ℕ} (hG : K.Good b r) (v : Fin N) :
    let S := K.blueNbr v
    let SD : ℤ := ∑ i ∈ S, ((K.blueNbr i).card : ℤ)
    let P : ℤ := ∑ i ∈ S, (K.hdeg v i : ℤ)
    SD - S.card - P ≤ b * (K.redNbr v).card ∧
    (S.card : ℤ) * (K.redNbr v).card - SD + S.card + P ≤ r * S.card := by
  intro S SD P
  constructor
  · have h := K.sum_W_codeg v
    have hle : (∑ w ∈ K.redNbr v, ((K.blueNbr w) ∩ K.blueNbr v).card : ℤ)
        ≤ ∑ _w ∈ K.redNbr v, (b : ℤ) := by
      refine Finset.sum_le_sum (fun w hw => ?_)
      exact_mod_cast K.blue_into_S_upper b hG.1 v w hw
    rw [h, Finset.sum_const, nsmul_eq_mul] at hle
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hle
    simp only [SD, P, S]; linarith
  · have hle : (∑ i ∈ S, ((K.redNbr i) ∩ K.redNbr v).card : ℤ) ≤ ∑ _i ∈ S, (r : ℤ) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      have hvi : v ≠ i := ((K.mem_blueNbr).mp hi).1.symm
      have := hG.2 v i hvi
      rw [← K.red_inter_T_eq_codeg v i] at this
      exact_mod_cast this
    have hpt : ∀ i ∈ S, (((K.redNbr i) ∩ K.redNbr v).card : ℤ)
        = (K.redNbr v).card - (((K.blueNbr i).card : ℤ) - 1 - K.hdeg v i) := by
      intro i hi
      have hc : K.C v i := ((K.mem_blueNbr).mp hi).2
      have huT : i ∉ K.redNbr v := fun h => ((K.mem_redNbr).mp h).2 hc
      have h1 := K.blue_red_split_card i (K.redNbr v) huT
      have h2 := K.deg_split v i hi
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul] at hle
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hle
    simp only [SD, P, S]; linarith

/-! ## Filter (iii) and Corollary 4.3 -/

/-- `Σ_{(i,j) ∈ U.offDiag} (XᵀX)_ij = Σ_{w ∈ W} z_w (z_w - 1)`, `z_w = |N(w) ∩ U|`, for `U ⊆ S`. -/
lemma sum_offDiag_xW (v : Fin N) (U : Finset (Fin N)) :
    (∑ p ∈ U.offDiag, (K.xW v p.1 p.2 : ℤ))
      = ∑ w ∈ K.redNbr v, (((K.blueNbr w) ∩ U).card : ℤ) * ((((K.blueNbr w) ∩ U).card : ℤ) - 1) := by
  classical
  have h1 : ∀ p ∈ U.offDiag, (K.xW v p.1 p.2 : ℤ)
      = ∑ w ∈ K.redNbr v, (if w ∈ K.blueNbr p.1 ∧ w ∈ K.blueNbr p.2 then (1 : ℤ) else 0) := by
    intro p _
    unfold xW
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 2
    ext w; simp only [mem_inter, mem_filter]; tauto
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : U.offDiag.filter (fun p => w ∈ K.blueNbr p.1 ∧ w ∈ K.blueNbr p.2)
      = ((K.blueNbr w) ∩ U).offDiag := by
    ext p
    simp only [mem_filter, mem_offDiag, mem_inter]
    rw [K.blue_mem_symm p.1 w, K.blue_mem_symm p.2 w]
    tauto
  rw [this, offDiag_card']
  have hc : 1 ≤ ((K.blueNbr w) ∩ U).card ∨ ((K.blueNbr w) ∩ U).card = 0 := by omega
  rcases hc with hc | hc
  · push_cast [Nat.cast_sub hc]; ring
  · rw [hc]; simp

/-- `Σ_{w ∈ W} z_w = T_U = Σ_{i ∈ U} (d_i - 1 - h_i)` for `U ⊆ S`. -/
lemma sum_z_eq_T (v : Fin N) (U : Finset (Fin N)) (hU : U ⊆ K.blueNbr v) :
    (∑ w ∈ K.redNbr v, (((K.blueNbr w) ∩ U).card : ℤ))
      = ∑ i ∈ U, (((K.blueNbr i).card : ℤ) - 1 - K.hdeg v i) := by
  have hx := K.blue_cross_count U (K.redNbr v)
  have : ∀ i ∈ U, (((K.blueNbr i).card : ℤ) - 1 - K.hdeg v i)
      = ((K.blueNbr i) ∩ K.redNbr v).card := by
    intro i hi; have := K.deg_split v i (hU hi); omega
  rw [Finset.sum_congr rfl this]
  exact_mod_cast hx.symm

/-- **Filter (iii), core, doubled** (LEMMAS_draft (4), Proposition 4.2's subset inequality).
    Let `U ⊆ S`, `m = |W| > 0`, `T_U = Σ_{i∈U}(d_i - 1 - h_i)`, `q = T_U / m`, `ρ = T_U % m`, and let
    `cap` be ANY function with `C_ij ≤ cap_ij` on the ordered pairs of `U` (e.g. the generator's
    `U^gen`, or `typed_encode.bounds`' blue_hi; both are proved to be caps in FiltersPy). Then
    `m q (q-1) + 2 ρ q ≤ Σ_{(i,j) ∈ U.offDiag} (cap_ij - 1 - q_ij)`. -/
theorem filter_iii_core (v : Fin N) (U : Finset (Fin N)) (hU : U ⊆ K.blueNbr v)
    (cap : Fin N → Fin N → ℤ) (hcap : ∀ p ∈ U.offDiag, ((K.blueCodeg p.1 p.2).card : ℤ) ≤ cap p.1 p.2)
    (hm : 0 < (K.redNbr v).card) :
    let T : ℤ := ∑ i ∈ U, (((K.blueNbr i).card : ℤ) - 1 - K.hdeg v i)
    let m : ℤ := (K.redNbr v).card
    m * (T / m) * (T / m - 1) + 2 * (T % m) * (T / m)
      ≤ ∑ p ∈ U.offDiag, (cap p.1 p.2 - 1 - K.qH v p.1 p.2) := by
  intro T m
  have hconv := convexity_floor (K.redNbr v) (fun w => (((K.blueNbr w) ∩ U).card : ℤ)) hm
  simp only at hconv
  rw [K.sum_z_eq_T v U hU, ← K.sum_offDiag_xW v U] at hconv
  refine le_trans hconv (Finset.sum_le_sum (fun p hp => ?_))
  have hp' := mem_offDiag.mp hp
  have hs := K.codeg_split v p.1 p.2 (hU hp'.1) (hU hp'.2.1)
  have hc := hcap p hp
  rw [hs] at hc; push_cast at hc; linarith

/-- **Corollary 4.3 (shortfall), core, doubled.** Same hypotheses with `U ⊆ S` (the corollary is
    the case `U = S`): the total shortfall `Σ (cap_ij - C_ij)` over ordered pairs of `U` plus the
    convexity floor is at most `Σ (cap_ij - 1 - q_ij)`; i.e. `Σ s_ij ≤ σ` (doubled). -/
theorem shortfall_core (v : Fin N) (U : Finset (Fin N)) (hU : U ⊆ K.blueNbr v)
    (cap : Fin N → Fin N → ℤ) (hm : 0 < (K.redNbr v).card) :
    let T : ℤ := ∑ i ∈ U, (((K.blueNbr i).card : ℤ) - 1 - K.hdeg v i)
    let m : ℤ := (K.redNbr v).card
    (∑ p ∈ U.offDiag, (cap p.1 p.2 - (K.blueCodeg p.1 p.2).card))
      + (m * (T / m) * (T / m - 1) + 2 * (T % m) * (T / m))
      ≤ ∑ p ∈ U.offDiag, (cap p.1 p.2 - 1 - K.qH v p.1 p.2) := by
  intro T m
  have hconv := convexity_floor (K.redNbr v) (fun w => (((K.blueNbr w) ∩ U).card : ℤ)) hm
  simp only at hconv
  rw [K.sum_z_eq_T v U hU, ← K.sum_offDiag_xW v U] at hconv
  have : ∀ p ∈ U.offDiag, cap p.1 p.2 - ((K.blueCodeg p.1 p.2).card : ℤ)
      = (cap p.1 p.2 - 1 - K.qH v p.1 p.2) - K.xW v p.1 p.2 := by
    intro p hp
    have hp' := mem_offDiag.mp hp
    rw [K.codeg_split v p.1 p.2 (hU hp'.1) (hU hp'.2.1)]; push_cast; ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib]
  linarith

end Colouring

#print axioms convexity_floor
#print axioms sum_offDiag_eq_two_sum_lt
#print axioms Colouring.card_split_root
#print axioms Colouring.deg_split
#print axioms Colouring.codeg_split
#print axioms Colouring.filter_i_core
#print axioms Colouring.sum_W_codeg
#print axioms Colouring.filter_ii_core
#print axioms Colouring.sum_offDiag_xW
#print axioms Colouring.sum_z_eq_T
#print axioms Colouring.filter_iii_core
#print axioms Colouring.shortfall_core
