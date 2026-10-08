/-
  M1: filters (i)-(iii) and Corollary 4.3 in the EXACT form the Python consumes, on a labelled
  root-neighbourhood graph `g : Fin k → Fin k → Bool`.

  Python sources transcribed (2026-10-06):
    runs/k28_rooted/m0_hcover/cnfgen.py   family_params: caps = min(4, k + D_i - 15),
                                          lo = max(0, -(-(S + 3k - 84) // 2)),
                                          hi = min(k(k-1)//2, (S + k(k-15)) // 2)
    runs/k28_rooted/m0_hcover/validate.py fail_iii(word, k, degrees, U)
    scripts/lemma/rooted_encode.py        pair_shortfall: sigma_raw and the emitted at-most-sigma
                                          constraint over the indicators -Ry[(i,j)][(M,t)]

  `failIIIPy`, `windowPy`, `capPy`, `sigmaRawPy` are line-by-line transcriptions over `ℤ`.
  Python's `//` and `divmod` by a POSITIVE divisor are floor division; Lean's `Int` `/`, `%` are
  Euclidean, which agrees with floor for positive divisors (`m = 21 - k ≥ 11 > 0`, `2 > 0`).
  `popRow g i` = `bin(g[i]).count('1')`, `popAnd g i j` = `bin(g[i] & g[j]).count('1')`.

  THE LINK TO A COLOURING. `RootLabel K v k` is a bijective labelling `e : Fin k → N(v)` (any one;
  the cell order of the census is a special case). `labH L a b = (a ≠ b) && K.C (e a) (e b)` is the
  labelled `H` (irreflexive, symmetric: what `graph_of(word)` gives for the word of `H`).

  MAIN THEOREMS (N = 22, Good 4 7, `D a = d(e a)` given as hypothesis `hD`):
    Colouring.filter_i_py         (popRow (labH L) a : ℤ) ≤ capPy k D a
    Colouring.filter_ii_py        (windowPy k D).1 ≤ edgesPy (labH L) ≤ (windowPy k D).2
    Colouring.filter_iii_py       failIIIPy k (labH L) D U = false         (every U)
    Colouring.shortfall_py        Σ_{a<b} (bh_ab - C_ab) ≤ sigmaRawPy k (labH L) D    (Cor. 4.3)
    Colouring.shortfall_emitted_py   the emitted at-most-max(sigma,0) constraint holds.
-/
import RootedLemmas.Filters

open Finset

/-! ## Python transcriptions on `Fin k` -/

section Py
variable {k : ℕ}

/-- `bin(g[i]).count('1')`. -/
def popRow (g : Fin k → Fin k → Bool) (a : Fin k) : ℕ := (univ.filter (fun b => g a b = true)).card

/-- `bin(g[i] & g[j]).count('1')`. -/
def popAnd (g : Fin k → Fin k → Bool) (a b : Fin k) : ℕ :=
  (univ.filter (fun c => g a c = true ∧ g b c = true)).card

/-- The pairs `a < b` of `U` in `itertools.combinations` order (as a set). -/
def ltPairs (U : Finset (Fin k)) : Finset (Fin k × Fin k) := (U ×ˢ U).filter (fun p => p.1 < p.2)

/-- `validate.fail_iii`'s `Ug`: `min(4, D_i + D_j - 15)` if `ij ∈ H`, else `4`. -/
def UgenPy (g : Fin k → Fin k → Bool) (D : Fin k → ℤ) (a b : Fin k) : ℤ :=
  if g a b = true then min 4 (D a + D b - 15) else 4

/-- `validate.fail_iii(word, k, degrees, U)[0]`, verbatim:
```
m = 21 - k
T = sum(degrees[i] - 1 - h[i] for i in idx); q, r = divmod(T, m)
lhs = m * q * (q - 1) // 2 + r * q
rhs = sum over i<j in idx of (Ug - 1 - popcount(g[i] & g[j]))
return lhs > rhs
``` -/
def failIIIPy (k : ℕ) (g : Fin k → Fin k → Bool) (D : Fin k → ℤ) (U : Finset (Fin k)) : Bool :=
  let m : ℤ := 21 - k
  let T : ℤ := ∑ a ∈ U, (D a - 1 - popRow g a)
  let q := T / m
  let r := T % m
  let lhs := m * q * (q - 1) / 2 + r * q
  let rhs := ∑ p ∈ ltPairs U, (UgenPy g D p.1 p.2 - 1 - popAnd g p.1 p.2)
  decide (lhs > rhs)

/-- `cnfgen.family_params` caps: `min(4, k + D_i - 15)` (filter (i)). -/
def capPy (k : ℕ) (D : Fin k → ℤ) (a : Fin k) : ℤ := min 4 ((k : ℤ) + D a - 15)

/-- `cnfgen.family_params` window `(lo, hi)` (filter (ii)). -/
def windowPy (k : ℕ) (D : Fin k → ℤ) : ℤ × ℤ :=
  let S := ∑ a, D a
  (max 0 (-((-(S + 3 * k - 84)) / 2)), min ((k : ℤ) * (k - 1) / 2) ((S + k * (k - 15)) / 2))

/-- Number of edges of `g` (`x_e` true, `e = (i,j)`, `i < j`). -/
def edgesPy (g : Fin k → Fin k → Bool) : ℕ := ((univ : Finset (Fin k × Fin k)).filter
  (fun p => p.1 < p.2 ∧ g p.1 p.2 = true)).card

/-- `rooted_encode.pair_shortfall`'s cap `bh = bounds(N, b, r, D_i, D_j, A)[1]` at the cell. -/
def bhPy (g : Fin k → Fin k → Bool) (D : Fin k → ℤ) (a b : Fin k) : ℤ :=
  (boundsPy 22 4 7 (D a) (D b) (if g a b = true then 1 else 0)).2.1

/-- `rooted_encode.pair_shortfall`'s `sigma_raw`, verbatim (`m = len(W) = N - 1 - k = 21 - k`):
```
sumk = sum over i<j in S of (bh - 1 - q_ij); T = sum(D[i-1] - 1 - h[i] for i in S)
q, rho = divmod(T, m); sigma_raw = sumk - (m * q * (q - 1) // 2 + rho * q)
``` -/
def sigmaRawPy (k : ℕ) (g : Fin k → Fin k → Bool) (D : Fin k → ℤ) : ℤ :=
  let m : ℤ := 21 - k
  let sumk := ∑ p ∈ ltPairs (univ : Finset (Fin k)), (bhPy g D p.1 p.2 - 1 - popAnd g p.1 p.2)
  let T : ℤ := ∑ a, (D a - 1 - popRow g a)
  let q := T / m
  let rho := T % m
  sumk - (m * q * (q - 1) / 2 + rho * q)

end Py

/-- `2 ∣ m q (q-1)`, so Python's `m * q * (q - 1) // 2` is exact. -/
lemma two_mul_half (m q : ℤ) : 2 * (m * q * (q - 1) / 2) = m * q * (q - 1) := by
  have h : Even (q * (q - 1)) := by
    have := Int.even_mul_pred_self q; simpa using this
  obtain ⟨c, hc⟩ := h
  have : m * q * (q - 1) = 2 * (m * c) := by rw [mul_assoc, hc]; ring
  rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]

namespace Colouring
variable {N : ℕ}

/-- A bijective labelling of the root's blue neighbourhood by `Fin k`. -/
structure RootLabel (K : Colouring N) (v : Fin N) (k : ℕ) where
  e : Fin k → Fin N
  inj : Function.Injective e
  mem : ∀ a, e a ∈ K.blueNbr v
  card : (K.blueNbr v).card = k

variable {K : Colouring N} {v : Fin N} {k : ℕ}

/-- The labelled root-neighbourhood graph. -/
def labH (L : RootLabel K v k) (a b : Fin k) : Bool := decide (a ≠ b) && K.C (L.e a) (L.e b)

namespace RootLabel
variable (L : RootLabel K v k)

def emb : Fin k ↪ Fin N := ⟨L.e, L.inj⟩

lemma map_univ : (univ : Finset (Fin k)).map L.emb = K.blueNbr v := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx; obtain ⟨a, _, rfl⟩ := mem_map.mp hx; exact L.mem a
  · rw [card_map, card_univ, Fintype.card_fin, L.card]

lemma mem_image_iff (x : Fin N) : x ∈ K.blueNbr v ↔ ∃ a, L.e a = x := by
  rw [← L.map_univ]; simp [emb]

lemma map_subset (U : Finset (Fin k)) : U.map L.emb ⊆ K.blueNbr v := by
  intro x hx; obtain ⟨a, _, rfl⟩ := mem_map.mp hx; exact L.mem a

lemma popRow_eq (a : Fin k) : popRow (labH L) a = K.hdeg v (L.e a) := by
  unfold popRow hdeg
  rw [← card_map L.emb]
  congr 1
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, mem_inter, labH, Bool.and_eq_true,
    decide_eq_true_eq, emb, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨b, ⟨hab, hc⟩, rfl⟩
    exact ⟨(K.mem_blueNbr).mpr ⟨fun h => hab (L.inj h).symm, hc⟩, L.mem b⟩
  · rintro ⟨hx, hS⟩
    obtain ⟨b, rfl⟩ := (L.mem_image_iff x).mp hS
    have := (K.mem_blueNbr).mp hx
    exact ⟨b, ⟨fun h => this.1 (by rw [h]), this.2⟩, rfl⟩

lemma popAnd_eq (a b : Fin k) : popAnd (labH L) a b = K.qH v (L.e a) (L.e b) := by
  unfold popAnd qH
  rw [← card_map L.emb]
  congr 1
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, mem_inter, labH, Bool.and_eq_true,
    decide_eq_true_eq, emb, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨c, ⟨⟨hac, h1⟩, ⟨hbc, h2⟩⟩, rfl⟩
    exact ⟨⟨(K.mem_blueNbr).mpr ⟨fun h => hac (L.inj h).symm, h1⟩,
      (K.mem_blueNbr).mpr ⟨fun h => hbc (L.inj h).symm, h2⟩⟩, L.mem c⟩
  · rintro ⟨⟨h1, h2⟩, hS⟩
    obtain ⟨c, rfl⟩ := (L.mem_image_iff x).mp hS
    have h1 := (K.mem_blueNbr).mp h1; have h2 := (K.mem_blueNbr).mp h2
    exact ⟨c, ⟨⟨fun h => h1.1 (by rw [h]), h1.2⟩, ⟨fun h => h2.1 (by rw [h]), h2.2⟩⟩, rfl⟩

lemma labH_symm (a b : Fin k) : labH L a b = labH L b a := by
  unfold labH; rw [K.symm (L.e a) (L.e b)]; simp [ne_comm]

lemma sum_map_offDiag (U : Finset (Fin k)) (F : Fin N × Fin N → ℤ) :
    ∑ p ∈ (U.map L.emb).offDiag, F p = ∑ p ∈ U.offDiag, F (L.e p.1, L.e p.2) := by
  classical
  let E : Fin k × Fin k ↪ Fin N × Fin N :=
    ⟨fun p => (L.e p.1, L.e p.2), fun p q h => by
      simp only [Prod.mk.injEq] at h; exact Prod.ext (L.inj h.1) (L.inj h.2)⟩
  have : (U.map L.emb).offDiag = U.offDiag.map E := by
    ext x
    simp only [mem_offDiag, mem_map, emb, Function.Embedding.coeFn_mk, E]
    constructor
    · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩, hne⟩
      refine ⟨(a, b), ⟨ha, hb, fun h => hne ?_⟩, ?_⟩
      · simp only at h; rw [← h1, ← h2, h]
      · rw [h1, h2]
    · rintro ⟨⟨a, b⟩, ⟨ha, hb, hne⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, fun h => hne (L.inj h)⟩
  rw [this, sum_map]; rfl

lemma sum_map_vert (U : Finset (Fin k)) (f : Fin N → ℤ) :
    ∑ i ∈ U.map L.emb, f i = ∑ a ∈ U, f (L.e a) := by
  rw [sum_map]; rfl

/-- `|W| = 21 - k` at `N = 22`. -/
lemma card_W (L : RootLabel K v k) (hN : N = 22) : ((K.redNbr v).card : ℤ) = 21 - k := by
  have := K.card_partition v; rw [L.card] at this; omega

end RootLabel

/-! ## Filter (i) -/

theorem filter_i_py (hN : N = 22) (hG : K.Good 4 7) (L : RootLabel K v k) (D : Fin k → ℤ)
    (hD : ∀ a, ((K.blueNbr (L.e a)).card : ℤ) = D a) (a : Fin k) :
    (popRow (labH L) a : ℤ) ≤ capPy k D a := by
  have h := K.filter_i_core hG v (L.e a) (L.mem a)
  have hW := L.card_W hN
  have hd := hD a
  rw [L.popRow_eq]
  unfold capPy
  simp only [le_min_iff]
  constructor <;> omega

/-! ## Filter (ii) -/

/-- `Σ_a popRow a = 2 · edges` for the labelled `H`. -/
lemma sum_popRow (L : RootLabel K v k) :
    (∑ a, (popRow (labH L) a : ℤ)) = 2 * (edgesPy (labH L) : ℤ) := by
  classical
  have h1 : ∀ a, (popRow (labH L) a : ℤ)
      = ∑ b, (if labH L a b = true then (1 : ℤ) else 0) := by
    intro a; unfold popRow; rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  simp_rw [h1]
  have h2 : (∑ a : Fin k, ∑ b : Fin k, (if labH L a b = true then (1 : ℤ) else 0))
      = ∑ p ∈ (univ : Finset (Fin k)).offDiag, (if labH L p.1 p.2 = true then (1 : ℤ) else 0) := by
    rw [← Finset.sum_product' (f := fun a b => if labH L a b = true then (1 : ℤ) else 0),
      ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag _)]
    have h0 : ∑ p ∈ (univ : Finset (Fin k)).diag, (if labH L p.1 p.2 = true then (1 : ℤ) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun p hp => ?_)
      have := (Finset.mem_diag.mp hp).2
      simp [labH, this]
    rw [h0, zero_add]
  have hx := sum_offDiag_eq_two_sum_lt (univ : Finset (Fin k))
    (fun a b => if labH L a b = true then (1 : ℤ) else 0) (fun a b => by simp only; rw [L.labH_symm])
  simp only at hx
  rw [h2, hx]
  congr 1
  unfold edgesPy
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext p; simp [ltPairs]

lemma edges_le (g : Fin k → Fin k → Bool) : 2 * (edgesPy g : ℤ) ≤ (k : ℤ) * (k - 1) := by
  classical
  have h := sum_offDiag_eq_two_sum_lt (univ : Finset (Fin k)) (fun _ _ => (1 : ℤ)) (fun _ _ => rfl)
  simp only [sum_const, nsmul_eq_mul, mul_one, offDiag_card', card_univ, Fintype.card_fin] at h
  have hsub : edgesPy g ≤ ((univ ×ˢ univ : Finset (Fin k × Fin k)).filter (fun p => p.1 < p.2)).card := by
    unfold edgesPy; apply card_le_card; intro p; simp only [mem_filter, mem_univ, true_and,
      mem_product]; exact fun h => h.1
  have hk : 1 ≤ k ∨ k = 0 := by omega
  rcases hk with hk | hk
  · push_cast [Nat.cast_sub hk] at h; push_cast at hsub ⊢; nlinarith
  · subst hk; simp [edgesPy]

theorem filter_ii_py (hN : N = 22) (hG : K.Good 4 7) (L : RootLabel K v k) (D : Fin k → ℤ)
    (hD : ∀ a, ((K.blueNbr (L.e a)).card : ℤ) = D a) :
    (windowPy k D).1 ≤ edgesPy (labH L) ∧ (edgesPy (labH L) : ℤ) ≤ (windowPy k D).2 := by
  have h := K.filter_ii_core hG v
  simp only at h
  have hW := L.card_W hN
  rw [← L.map_univ, L.sum_map_vert, L.sum_map_vert, card_map, card_univ, Fintype.card_fin] at h
  simp_rw [hD, ← L.popRow_eq] at h
  rw [sum_popRow, hW] at h
  have hE := edges_le (labH L)
  unfold windowPy
  simp only [le_min_iff, max_le_iff]
  set S := ∑ a, D a
  set t := (edgesPy (labH L) : ℤ)
  set kk := (k : ℤ)
  obtain ⟨h1, h2⟩ := h
  push_cast at h1 h2
  have h1' : S - kk - 2 * t ≤ 84 - 4 * kk := by linarith
  have h2' : 21 * kk - kk * kk - S + kk + 2 * t ≤ 7 * kk := by linarith
  have e3 : kk * (kk - 15) = kk * kk - 15 * kk := by ring
  have e4 : kk * (kk - 1) = kk * kk - kk := by ring
  rw [e4] at hE ⊢; rw [e3]
  have ht : 0 ≤ t := by positivity
  generalize kk * kk = KK at *
  refine ⟨⟨ht, by omega⟩, by omega, by omega⟩

/-! ## Filter (iii) -/

/-- The generator's `U^gen` is a valid blue-codegree cap at the cell. -/
lemma Ugen_valid (hN : N = 22) (hG : K.Good 4 7) {i j : Fin N} (hij : i ≠ j) :
    ((K.blueCodeg i j).card : ℤ) ≤ (if K.C i j then min 4 (K.dg i + K.dg j - 15) else 4) := by
  have hid := K.complement_identity hij
  have h1 := hG.1 i j hij; have h2 := hG.2 i j hij
  unfold cR cB Aij at hid
  subst hN
  split_ifs with hc
  · simp only [hc, if_true] at hid
    simp only [le_min_iff]; constructor <;> push_cast at * <;> omega
  · exact_mod_cast h1

/-- **Filter (iii), as `validate.fail_iii` computes it.** In a good colouring of `K_22`, for every
    labelling of `N(v)` with prescribed degrees `D`, and EVERY subset `U`, `fail_iii` is false.
    Hence a word failing `fail_iii` on some `U` is not the labelled `H` of any good colouring with
    those degrees (the M0 filter-(iii) blockers). -/
theorem filter_iii_py (hN : N = 22) (hG : K.Good 4 7) (L : RootLabel K v k) (D : Fin k → ℤ)
    (hD : ∀ a, ((K.blueNbr (L.e a)).card : ℤ) = D a) (U : Finset (Fin k)) (hk : k < 21) :
    failIIIPy k (labH L) D U = false := by
  have hW := L.card_W hN
  have hm : 0 < (K.redNbr v).card := by omega
  have h := K.filter_iii_core v (U.map L.emb) (L.map_subset U)
    (fun i j => if K.C i j then min 4 (K.dg i + K.dg j - 15) else 4)
    (fun p hp => Ugen_valid hN hG (mem_offDiag.mp hp).2.2) hm
  simp only at h
  rw [L.sum_map_vert, L.sum_map_offDiag, hW] at h
  simp only at h
  simp_rw [hD, ← L.popRow_eq, ← L.popAnd_eq] at h
  have hU : ∀ p ∈ U.offDiag, ((if K.C (L.e p.1) (L.e p.2) then min 4 (K.dg (L.e p.1) + K.dg (L.e p.2) - 15) else 4)
      - 1 - (popAnd (labH L) p.1 p.2 : ℤ)) = UgenPy (labH L) D p.1 p.2 - 1 - popAnd (labH L) p.1 p.2 := by
    intro p hp
    have hne := (mem_offDiag.mp hp).2.2
    unfold UgenPy labH dg
    rw [← hD p.1, ← hD p.2]
    simp [hne]
  rw [Finset.sum_congr rfl hU] at h
  have hx := sum_offDiag_eq_two_sum_lt U
    (fun a b => UgenPy (labH L) D a b - 1 - (popAnd (labH L) a b : ℤ)) (fun a b => by
      simp only; unfold UgenPy popAnd; rw [L.labH_symm a b]; simp only [add_comm (D a), and_comm])
  simp only at hx
  rw [hx] at h
  unfold failIIIPy
  simp only [decide_eq_false_iff_not, gt_iff_lt, not_lt]
  set T : ℤ := ∑ a ∈ U, (D a - 1 - (popRow (labH L) a : ℤ))
  set m : ℤ := 21 - k
  have := two_mul_half m (T / m)
  unfold ltPairs
  linarith

/-! ## Corollary 4.3 (shortfall) -/

lemma bh_valid (hN : N = 22) (hG : K.Good 4 7) (L : RootLabel K v k) (D : Fin k → ℤ)
    (hD : ∀ a, ((K.blueNbr (L.e a)).card : ℤ) = D a) {a b : Fin k} (hab : a ≠ b) :
    ((K.blueCodeg (L.e a) (L.e b)).card : ℤ) ≤ bhPy (labH L) D a b := by
  have hne : L.e a ≠ L.e b := fun h => hab (L.inj h)
  have h := (K.bounds_sound hG hne).2.1
  subst hN
  unfold bhPy
  have hA : (if labH L a b = true then (1 : ℤ) else 0) = K.Aij (L.e a) (L.e b) := by
    unfold labH Aij; simp [hab]
  rw [hA, ← hD a, ← hD b]
  exact h

/-- **Corollary 4.3, as `rooted_encode.pair_shortfall` computes it:**
    `Σ_{a<b} (bh_ab - C_{e a, e b}) ≤ sigma_raw`. -/
theorem shortfall_py (hN : N = 22) (hG : K.Good 4 7) (L : RootLabel K v k) (D : Fin k → ℤ)
    (hD : ∀ a, ((K.blueNbr (L.e a)).card : ℤ) = D a) (hk : k < 21) :
    ∑ p ∈ ltPairs (univ : Finset (Fin k)),
        (bhPy (labH L) D p.1 p.2 - (K.blueCodeg (L.e p.1) (L.e p.2)).card)
      ≤ sigmaRawPy k (labH L) D := by
  have hW := L.card_W hN
  have hm : 0 < (K.redNbr v).card := by omega
  -- the cap on `Fin N`, read back through the labelling
  classical
  let cap : Fin N → Fin N → ℤ := fun i j =>
    if h : (∃ a, L.e a = i) ∧ (∃ b, L.e b = j) then bhPy (labH L) D h.1.choose h.2.choose else 0
  have hcap : ∀ a b, cap (L.e a) (L.e b) = bhPy (labH L) D a b := by
    intro a b
    have hex : (∃ a', L.e a' = L.e a) ∧ (∃ b', L.e b' = L.e b) := ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    simp only [cap, dif_pos hex]
    rw [L.inj hex.1.choose_spec, L.inj hex.2.choose_spec]
  have h := K.shortfall_core v ((univ : Finset (Fin k)).map L.emb) (L.map_subset _) cap hm
  simp only at h
  rw [L.sum_map_vert, L.sum_map_offDiag, L.sum_map_offDiag, hW] at h
  simp only at h
  simp_rw [hD, ← L.popRow_eq, ← L.popAnd_eq, hcap] at h
  have hsym1 : ∀ a b : Fin k, bhPy (labH L) D a b - ((K.blueCodeg (L.e a) (L.e b)).card : ℤ)
      = bhPy (labH L) D b a - ((K.blueCodeg (L.e b) (L.e a)).card : ℤ) := by
    intro a b
    unfold bhPy boundsPy
    rw [L.labH_symm a b, K.blueCodeg_symm]
    simp only; ring_nf
  have hsym2 : ∀ a b : Fin k, bhPy (labH L) D a b - 1 - (popAnd (labH L) a b : ℤ)
      = bhPy (labH L) D b a - 1 - (popAnd (labH L) b a : ℤ) := by
    intro a b
    have : popAnd (labH L) a b = popAnd (labH L) b a := by
      unfold popAnd; simp only [and_comm]
    unfold bhPy boundsPy
    rw [L.labH_symm a b, this]
    simp only; ring_nf
  have hx1 := sum_offDiag_eq_two_sum_lt univ
    (fun a b => bhPy (labH L) D a b - ((K.blueCodeg (L.e a) (L.e b)).card : ℤ)) hsym1
  have hx2 := sum_offDiag_eq_two_sum_lt univ
    (fun a b => bhPy (labH L) D a b - 1 - (popAnd (labH L) a b : ℤ)) hsym2
  simp only at hx1 hx2
  rw [hx1, hx2] at h
  unfold sigmaRawPy
  simp only
  set T : ℤ := ∑ a, (D a - 1 - (popRow (labH L) a : ℤ))
  set m : ℤ := 21 - k
  have := two_mul_half m (T / m)
  unfold ltPairs
  linarith

/-- Each emitted per-pair count `#{t ∈ [lo, bh] : ¬(C ≥ t)}` is at most the shortfall `bh - C`. -/
lemma count_le_shortfall (lo bh C : ℤ) (hC : C ≤ bh) :
    (((Finset.Icc lo bh).filter (fun t => C < t)).card : ℤ) ≤ bh - C := by
  have : (Finset.Icc lo bh).filter (fun t => C < t) ⊆ Finset.Ioc C bh := by
    intro t; simp only [mem_filter, mem_Icc, mem_Ioc]; omega
  have h := card_le_card this
  rw [Int.card_Ioc] at h
  omega

/-- **The constraint `pair_shortfall` emits holds** (LEMMAS_draft Proposition 4.4): with
    `sigma = max(sigma_raw, 0)` and the literals `-Ry[(i,j)][(M,t)]` (true iff `C_ij < t`) for
    `t ∈ [max(1, bh - max(sigma,1) + 1), bh]`, at most `sigma` of them are true. -/
theorem shortfall_emitted_py (hN : N = 22) (hG : K.Good 4 7) (L : RootLabel K v k) (D : Fin k → ℤ)
    (hD : ∀ a, ((K.blueNbr (L.e a)).card : ℤ) = D a) (hk : k < 21) :
    let σ := max (sigmaRawPy k (labH L) D) 0
    (∑ p ∈ ltPairs (univ : Finset (Fin k)),
      ((((Finset.Icc (max 1 (bhPy (labH L) D p.1 p.2 - max σ 1 + 1)) (bhPy (labH L) D p.1 p.2)).filter
        (fun t => ((K.blueCodeg (L.e p.1) (L.e p.2)).card : ℤ) < t)).card : ℤ))) ≤ σ := by
  intro σ
  have h := shortfall_py hN hG L D hD hk
  have hle : ∀ p ∈ ltPairs (univ : Finset (Fin k)),
      ((((Finset.Icc (max 1 (bhPy (labH L) D p.1 p.2 - max σ 1 + 1)) (bhPy (labH L) D p.1 p.2)).filter
        (fun t => ((K.blueCodeg (L.e p.1) (L.e p.2)).card : ℤ) < t)).card : ℤ))
      ≤ bhPy (labH L) D p.1 p.2 - (K.blueCodeg (L.e p.1) (L.e p.2)).card := by
    intro p hp
    have hne : p.1 ≠ p.2 := by
      simp only [ltPairs, mem_filter] at hp; exact ne_of_lt hp.2
    exact count_le_shortfall _ _ _ (bh_valid hN hG L D hD hne)
  have := Finset.sum_le_sum hle
  have hσ : sigmaRawPy k (labH L) D ≤ σ := le_max_left _ _
  linarith

/-! ## Bridge to `SB.NoKst` -/

theorem filters_py_NoKst (hN : N = 22) (hblue : SB.NoKst (toE K) 1 2 5)
    (hred : SB.NoKst (toE K) 0 2 8) (L : RootLabel K v k) (D : Fin k → ℤ)
    (hD : ∀ a, ((K.blueNbr (L.e a)).card : ℤ) = D a) (hk : k < 21) :
    (∀ a, (popRow (labH L) a : ℤ) ≤ capPy k D a) ∧
    ((windowPy k D).1 ≤ edgesPy (labH L) ∧ (edgesPy (labH L) : ℤ) ≤ (windowPy k D).2) ∧
    (∀ U, failIIIPy k (labH L) D U = false) ∧
    ∑ p ∈ ltPairs (univ : Finset (Fin k)),
        (bhPy (labH L) D p.1 p.2 - (K.blueCodeg (L.e p.1) (L.e p.2)).card)
      ≤ sigmaRawPy k (labH L) D := by
  have hG := K.good_of_NoKst hblue hred
  exact ⟨filter_i_py hN hG L D hD, filter_ii_py hN hG L D hD,
    fun U => filter_iii_py hN hG L D hD U hk, shortfall_py hN hG L D hD hk⟩

end Colouring

#print axioms two_mul_half
#print axioms Colouring.RootLabel.popRow_eq
#print axioms Colouring.RootLabel.popAnd_eq
#print axioms Colouring.RootLabel.sum_map_offDiag
#print axioms Colouring.filter_i_py
#print axioms Colouring.sum_popRow
#print axioms Colouring.filter_ii_py
#print axioms Colouring.Ugen_valid
#print axioms Colouring.filter_iii_py
#print axioms Colouring.bh_valid
#print axioms Colouring.shortfall_py
#print axioms Colouring.shortfall_emitted_py
#print axioms Colouring.filters_py_NoKst
