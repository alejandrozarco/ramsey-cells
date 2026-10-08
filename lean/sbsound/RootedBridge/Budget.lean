/-
# M3: the exact deficit sums (B) of `add_counting`

For every vertex `v` (budget `Λ_v = budget_of(D_v) ≥ 0`), every `u ≠ v` and every threshold
`l = 1..min(Λ_v, 7)`: `P ↔ (vu blue ∧ R_vu ≤ 7 - l)`, `Q ↔ (vu red ∧ C_vu ≤ 4 - l)`, `E ↔ P ∨ Q`,
and a bidirectional counter forces exactly `Λ_v` of the `E` to be true. Satisfied when that count
is `Λ_v` (`BudOK`, M1 Lemma 2.4 / `threshold_sum` on the Mathlib side).
-/
import RootedBridge.Channel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

/-- The truth value of `E_{vu,l}`. -/
def thrE (col : Nat → Nat → Bool) (u v l : Nat) : Bool :=
  (col u v && decide ((Cr col (srt u v).1 (srt u v).2 : Int) ≤ 7 - l)) ||
  (!col u v && decide ((Cb col (srt u v).1 (srt u v).2 : Int) ≤ 4 - l))

/-- `min(Λ_v, max(7, 4))` as a natural number (the number of thresholds per `u`). -/
def topOf (D : Array Nat) (v : Nat) : Nat := (min (lamD D v) (max (7 : Int) (4 : Int))).toNat

/-- The `E` values for `v`, in the encoder's order (`u = 1..t`, `u ≠ v`, then `l`). -/
def budList (col : Nat → Nat → Bool) (D : Array Nat) (v t : Nat) : List Bool :=
  ((List.range' 1 t).filter (fun u => u != v)).flatMap
    (fun u => (List.range' 1 (topOf D v)).map (fun l => thrE col u v l))

/-- The budgets are nonnegative and exactly met (M1 Lemma 2.4 in the encoder's order). -/
def BudOK (col : Nat → Nat → Bool) (D : Array Nat) : Prop :=
  ∀ v, 1 ≤ v → v ≤ 22 → 0 ≤ lamD D v ∧ ((budList col D v 22).filter id).length = (lamD D v).toNat

/-- `Es` is a list of valid literals whose values are `bs`. -/
def EsOK (σ : Nat → Bool) (n : Nat) (Es : Array Int) (bs : List Bool) : Prop :=
  Es.size = bs.length ∧ ∀ i (h : i < Es.size), Es[i] ≠ 0 ∧ Es[i].natAbs ≤ n ∧
    bs[i]? = some (lv σ Es[i])

theorem EsOK.nil (σ : Nat → Bool) (n : Nat) : EsOK σ n #[] [] := ⟨rfl, fun i h => absurd h (by simp)⟩

theorem EsOK.push {σ : Nat → Bool} {n : Nat} {Es : Array Int} {bs : List Bool} (h : EsOK σ n Es bs)
    {e : Int} (he0 : e ≠ 0) (hen : e.natAbs ≤ n) : EsOK σ n (Es.push e) (bs ++ [lv σ e]) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  simp only [Array.size_push] at hi
  by_cases hlt : i < Es.size
  · rw [Array.getElem_push_lt hlt]
    obtain ⟨h1, h2, h3⟩ := h.2 i hlt
    refine ⟨h1, h2, ?_⟩
    rw [List.getElem?_append_left (by rw [← h.1]; exact hlt), h3]
  · have : i = Es.size := by omega
    subst this
    rw [Array.getElem_push_eq]
    refine ⟨he0, hen, ?_⟩
    rw [List.getElem?_append_right (by have := h.1; omega), h.1]; simp

theorem EsOK.mono {σ : Nat → Bool} {n m : Nat} {Es : Array Int} {bs : List Bool} (h : EsOK σ n Es bs)
    (hnm : n ≤ m) : EsOK σ m Es bs :=
  ⟨h.1, fun i hi => by obtain ⟨h1, h2, h3⟩ := h.2 i hi; exact ⟨h1, by omega, h3⟩⟩

theorem EsOK.agree {σ σ' : Nat → Bool} {n m : Nat} {Es : Array Int} {bs : List Bool} (h : EsOK σ n Es bs)
    (hag : Agree σ σ' m) (hnm : n ≤ m) : EsOK σ' n Es bs :=
  ⟨h.1, fun i hi => by
    obtain ⟨h1, h2, h3⟩ := h.2 i hi
    exact ⟨h1, h2, by rw [lv_congr (hag _ (by omega)), h3]⟩⟩

theorem EsOK.lits {σ : Nat → Bool} {n : Nat} {Es : Array Int} {bs : List Bool} (h : EsOK σ n Es bs) :
    ∀ l ∈ Es, l ≠ 0 ∧ l.natAbs ≤ n := by
  intro l hl
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hl
  exact ⟨(h.2 i hi).1, (h.2 i hi).2.1⟩

theorem EsOK.cnt {σ : Nat → Bool} {n : Nat} {Es : Array Int} {bs : List Bool} (h : EsOK σ n Es bs) :
    cnt σ Es Es.size = (bs.filter id).length := by
  have hl : Es.toList.map (lv σ) = bs := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < Es.size
    · rw [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hi, (h.2 i hi).2.2]
      rfl
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by rw [← h.1]; omega)]
  unfold SB.Rooted.cnt
  rw [List.take_of_length_le (by simp), ← hl, List.filter_map, List.length_map]
  rfl

/-- The membership of a literal of a short array literal. -/
theorem mem3 {l a b c : Int} : l ∈ #[a, b, c] ↔ l = a ∨ l = b ∨ l = c := by simp
theorem mem2 {l a b : Int} : l ∈ #[a, b] ↔ l = a ∨ l = b := by simp
theorem mem1 {l a : Int} : l ∈ #[a] ↔ l = a := by simp

theorem budP_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) {u v l : Nat}
    (huv : VPair u v) (hl1 : 1 ≤ l) (Rz : Array Counter) (P n : Nat) (hP : 0 < P)
    (s : St) (σ : Nat → Bool) (H : Prop)
    (hF : H → CntFacts σ Rz[edgeIdx 22 (srt u v).1 (srt u v).2]! 8 (Cr col (srt u v).1 (srt u v).2) n ∧
      EdgeOK col σ ∧ n ≤ s.nv ∧ 462 ≤ s.nv ∧ P ≤ s.nv ∧
      σ P = (col u v && decide ((Cr col (srt u v).1 (srt u v).2 : Int) ≤ 7 - l))) :
    Spec H (budP 7 (22 - 2) Rz (edgeIdx 22 (srt u v).1 (srt u v).2) (varE 22 2 u v 2) (P : Int) l) s σ
      (fun _ s' σ' => s'.nv = s.nv ∧ σ' = σ) := by
  have hA := varE_bounds huv (Or.inr rfl)
  unfold budP
  by_cases h1 : ((7 : Nat) : Int) - (l : Int) < 0
  · rw [if_pos h1]
    refine spec_add (fun hH _ _ => ?_)
    obtain ⟨cz, hE, hn, h462, hPn, hPv⟩ := hF hH
    refine ⟨fun x hx => ?_, clauseSat_of_any (fun x hx => ?_) ?_, rfl, rfl⟩
    · rw [mem1] at hx; subst hx; simp; omega
    · rw [mem1] at hx; subst hx; omega
    · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
      rw [lv_neg_natCast _ hP, hPv]
      cases col u v <;> simp; omega
  · rw [if_neg h1]
    by_cases h2 : ((7 : Nat) : Int) - (l : Int) + 1 ≤ ((22 - 2 : Nat) : Int)
    · rw [if_pos h2]
      refine spec_at_bind' (fun s₁ x hnv hcls hx => ?_)
      dsimp only
      refine spec_add_bind (fun hH hg he => ?_) (spec_add_bind (fun hH hg he => ?_)
        (spec_add (fun hH hg he => ?_)))
      all_goals
        obtain ⟨rfl, w, hw, rfl⟩ := hx (by simpa using he)
        obtain ⟨cz, hE, hn, h462, hPn, hPv⟩ := hF hH
        obtain ⟨w0, wn, wv⟩ := cz.2 _ _ hw
        have hl := lv_varE hsym hE huv (Or.inr rfl)
        simp only [colV, if_true] at hl
      · refine ⟨fun x hx => ?_, clauseSat_of_any (fun x hx => ?_) ?_⟩
        · rw [mem2] at hx; rcases hx with rfl | rfl <;> (try simp) <;> omega
        · rw [mem2] at hx; rcases hx with rfl | rfl <;> omega
        · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
          rw [lv_neg_natCast _ hP, hPv, hl]
          cases col u v <;> simp
      · refine ⟨fun x hx => ?_, clauseSat_of_any (fun x hx => ?_) ?_⟩
        · rw [mem2] at hx; rcases hx with rfl | rfl <;> (try simp) <;> omega
        · rw [mem2] at hx; rcases hx with rfl | rfl <;> omega
        · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
          rw [lv_neg_natCast _ hP, hPv, lv_neg_natCast _ w0, wv]
          cases col u v <;> simp <;> omega
      · refine ⟨fun x hx => ?_, clauseSat_of_any (fun x hx => ?_) ?_, by simp, rfl⟩
        · rw [mem3] at hx; rcases hx with rfl | rfl | rfl <;> (try simp) <;> omega
        · rw [mem3] at hx; rcases hx with rfl | rfl | rfl <;> omega
        · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
          rw [lv_natCast _ hP, hPv, lv_neg _ hA.2.2, hl, Int.neg_neg, lv_natCast _ w0, wv]
          cases col u v <;> simp <;> omega
    · exfalso; omega

theorem budQ_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) {u v l : Nat}
    (huv : VPair u v) (hl1 : 1 ≤ l) (Ry : Array Counter) (P n : Nat) (hP : 0 < P)
    (s : St) (σ : Nat → Bool) (H : Prop)
    (hF : H → CntFacts σ Ry[edgeIdx 22 (srt u v).1 (srt u v).2]! 5 (Cb col (srt u v).1 (srt u v).2) n ∧
      EdgeOK col σ ∧ n ≤ s.nv ∧ 462 ≤ s.nv ∧ P ≤ s.nv ∧
      σ P = (!col u v && decide ((Cb col (srt u v).1 (srt u v).2 : Int) ≤ 4 - l))) :
    Spec H (budQ 4 (22 - 2) Ry (edgeIdx 22 (srt u v).1 (srt u v).2) (varE 22 2 u v 2) (P : Int) l) s σ
      (fun _ s' σ' => s'.nv = s.nv ∧ σ' = σ) := by
  have hA := varE_bounds huv (Or.inr rfl)
  unfold budQ
  by_cases h1 : ((4 : Nat) : Int) - (l : Int) < 0
  · rw [if_pos h1]
    refine spec_add (fun hH _ _ => ?_)
    obtain ⟨cz, hE, hn, h462, hPn, hPv⟩ := hF hH
    refine ⟨fun x hx => ?_, clauseSat_of_any (fun x hx => ?_) ?_, rfl, rfl⟩
    · rw [mem1] at hx; subst hx; simp; omega
    · rw [mem1] at hx; subst hx; omega
    · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
      rw [lv_neg_natCast _ hP, hPv]
      cases col u v <;> simp; omega
  · rw [if_neg h1]
    by_cases h2 : ((4 : Nat) : Int) - (l : Int) + 1 ≤ ((22 - 2 : Nat) : Int)
    · rw [if_pos h2]
      refine spec_at_bind' (fun s₁ x hnv hcls hx => ?_)
      dsimp only
      refine spec_add_bind (fun hH hg he => ?_) (spec_add_bind (fun hH hg he => ?_)
        (spec_add (fun hH hg he => ?_)))
      all_goals
        obtain ⟨rfl, w, hw, rfl⟩ := hx (by simpa using he)
        obtain ⟨cz, hE, hn, h462, hPn, hPv⟩ := hF hH
        obtain ⟨w0, wn, wv⟩ := cz.2 _ _ hw
        have hl := lv_varE hsym hE huv (Or.inr rfl)
        simp only [colV, if_true] at hl
      · refine ⟨fun x hx => ?_, clauseSat_of_any (fun x hx => ?_) ?_⟩
        · rw [mem2] at hx; rcases hx with rfl | rfl <;> (try simp) <;> omega
        · rw [mem2] at hx; rcases hx with rfl | rfl <;> omega
        · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
          rw [lv_neg_natCast _ hP, hPv, lv_neg _ hA.2.2, hl]
          cases col u v <;> simp
      · refine ⟨fun x hx => ?_, clauseSat_of_any (fun x hx => ?_) ?_⟩
        · rw [mem2] at hx; rcases hx with rfl | rfl <;> (try simp) <;> omega
        · rw [mem2] at hx; rcases hx with rfl | rfl <;> omega
        · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
          rw [lv_neg_natCast _ hP, hPv, lv_neg_natCast _ w0, wv]
          cases col u v <;> simp <;> omega
      · refine ⟨fun x hx => ?_, clauseSat_of_any (fun x hx => ?_) ?_, by simp, rfl⟩
        · rw [mem3] at hx; rcases hx with rfl | rfl | rfl <;> (try simp) <;> omega
        · rw [mem3] at hx; rcases hx with rfl | rfl | rfl <;> omega
        · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
          rw [lv_natCast _ hP, hPv, hl, Int.neg_neg, lv_natCast _ w0, wv]
          cases col u v <;> simp <;> omega
    · exfalso; omega

theorem budStep'_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) {u v l : Nat}
    (huv : VPair u v) (hl1 : 1 ≤ l) (Ry Rz : Array Counter) (n : Nat) (Es : Array Int)
    (s : St) (σ : Nat → Bool) (H : Prop)
    (hF : H → CntFacts σ Ry[edgeIdx 22 (srt u v).1 (srt u v).2]! 5 (Cb col (srt u v).1 (srt u v).2) n ∧
      CntFacts σ Rz[edgeIdx 22 (srt u v).1 (srt u v).2]! 8 (Cr col (srt u v).1 (srt u v).2) n ∧
      EdgeOK col σ ∧ n ≤ s.nv ∧ 462 ≤ s.nv) :
    Spec H (budStep' 22 4 7 Ry Rz (edgeIdx 22 (srt u v).1 (srt u v).2) (varE 22 2 u v 2) l Es) s σ
      (fun r s' σ' => r = ForInStep.yield (Es.push ((s.nv + 3 : Nat) : Int)) ∧ s'.nv = s.nv + 3 ∧
        σ' (s.nv + 3) = thrE col u v l) := by
  unfold budStep'
  let pv := col u v && decide ((Cr col (srt u v).1 (srt u v).2 : Int) ≤ 7 - l)
  let qv := !col u v && decide ((Cb col (srt u v).1 (srt u v).2 : Int) ≤ 4 - l)
  refine spec_fresh_bind pv (spec_fresh_bind qv (spec_fresh_bind (pv || qv) ?_))
  dsimp only
  let σ3 := upd (upd (upd σ (s.nv + 1) pv) (s.nv + 1 + 1) qv) (s.nv + 1 + 1 + 1) (pv || qv)
  have ag3 : Agree σ σ3 s.nv := agree_trans (agree_trans (agree_upd σ s.nv pv) (agree_upd _ _ qv)
    (Nat.le_succ _)) (agree_upd _ _ _) (by omega)
  have v1 : σ3 (s.nv + 1) = pv := by simp [σ3, upd]
  have v2 : σ3 (s.nv + 1 + 1) = qv := by simp [σ3, upd]
  have v3 : σ3 (s.nv + 1 + 1 + 1) = (pv || qv) := by simp [σ3, upd]
  have hF3 : H → CntFacts σ3 Ry[edgeIdx 22 (srt u v).1 (srt u v).2]! 5 (Cb col (srt u v).1 (srt u v).2) n ∧
      CntFacts σ3 Rz[edgeIdx 22 (srt u v).1 (srt u v).2]! 8 (Cr col (srt u v).1 (srt u v).2) n ∧
      EdgeOK col σ3 ∧ n ≤ s.nv ∧ 462 ≤ s.nv := by
    intro hH
    obtain ⟨c1, c2, hE, hn, h462⟩ := hF hH
    exact ⟨c1.agree ag3 hn, c2.agree ag3 hn, EdgeOK.agree hE ag3 h462, hn, h462⟩
  refine spec_bind (budP_spec col hsym huv hl1 Rz (s.nv + 1) n (Nat.succ_pos _) _ σ3 _ (fun hH => ?_))
    (fun _ s₄ σ₄ => ?_)
  · obtain ⟨c1, c2, hE, hn, h462⟩ := hF3 hH
    exact ⟨c2, hE, by simp; omega, by simp; omega, by simp, v1⟩
  refine spec_bind (budQ_spec col hsym huv hl1 Ry (s.nv + 1 + 1) n (Nat.succ_pos _) _ σ₄ _ (fun hH => ?_))
    (fun _ s₅ σ₅ => ?_)
  · obtain ⟨hp, -, -, -, -, hs4, rfl⟩ := hH
    obtain ⟨c1, c2, hE, hn, h462⟩ := hF3 hp
    exact ⟨c1, hE, by simp at hs4; omega, by simp at hs4; omega, by simp at hs4; omega, v2⟩
  refine spec_add_bind (fun hH hg he => ?_) (spec_add_bind (fun hH hg he => ?_)
    (spec_add_bind (fun hH hg he => ?_) (spec_pure (fun hH _ _ => ?_))))
  all_goals
    obtain ⟨⟨hp, -, -, -, -, hs4, h4⟩, -, -, -, -, hs5, h5⟩ := hH
    obtain ⟨c1, c2, hE, hn, h462⟩ := hF3 hp
    have hσ := h5.trans h4
    have hnv : s₅.nv = s.nv + 1 + 1 + 1 := by rw [hs5, hs4]
  · refine ⟨fun x hx => ?_, clauseSat_of_any (fun x hx => ?_) ?_⟩
    · rw [mem3] at hx; rcases hx with rfl | rfl | rfl <;> simp <;> omega
    · rw [mem3] at hx; rcases hx with rfl | rfl | rfl <;> omega
    · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
      rw [hσ, lv_neg_natCast _ (Nat.succ_pos _), lv_natCast _ (Nat.succ_pos _),
        lv_natCast _ (Nat.succ_pos _), v1, v2, v3]
      cases pv <;> cases qv <;> simp
  · refine ⟨fun x hx => ?_, clauseSat_of_any (fun x hx => ?_) ?_⟩
    · rw [mem2] at hx; rcases hx with rfl | rfl <;> simp <;> omega
    · rw [mem2] at hx; rcases hx with rfl | rfl <;> omega
    · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
      rw [hσ, lv_neg_natCast _ (Nat.succ_pos _), lv_natCast _ (Nat.succ_pos _), v1, v3]
      cases pv <;> cases qv <;> simp
  · refine ⟨fun x hx => ?_, clauseSat_of_any (fun x hx => ?_) ?_⟩
    · rw [mem2] at hx; rcases hx with rfl | rfl <;> simp <;> omega
    · rw [mem2] at hx; rcases hx with rfl | rfl <;> omega
    · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
      rw [hσ, lv_neg_natCast _ (Nat.succ_pos _), lv_natCast _ (Nat.succ_pos _), v2, v3]
      cases pv <;> cases qv <;> simp
  · refine ⟨rfl, by simpa using hnv, ?_⟩
    rw [hσ, show s.nv + 3 = s.nv + 1 + 1 + 1 by omega, v3]
    rfl

theorem ryz_at {col : Nat → Nat → Bool} {σ : Nat → Bool} {n : Nat} {Ry Rz : Array Counter}
    (h : RyzOK col σ n 231 Ry Rz) {u v : Nat} (huv : VPair u v) :
    CntFacts σ Ry[edgeIdx 22 (srt u v).1 (srt u v).2]! 5 (Cb col (srt u v).1 (srt u v).2) n ∧
    CntFacts σ Rz[edgeIdx 22 (srt u v).1 (srt u v).2]! 8 (Cr col (srt u v).1 (srt u v).2) n := by
  obtain ⟨ha1, ha2, hb1, hb2, hne⟩ := huv
  obtain ⟨h1, h2⟩ := srt_fst_snd hne
  have hs1 : 1 ≤ (srt u v).1 := by omega
  have hs2 : (srt u v).2 ≤ 22 := by omega
  have hp := edgeIdx_lt hs1 h1 hs2
  have hget := edgesOf_get hs1 h1 hs2
  have hget' : (edgesOf 22)[edgeIdx 22 (srt u v).1 (srt u v).2]'(by rw [edgesOf_size]; exact hp) =
      ((srt u v).1, (srt u v).2) :=
    Option.some.inj ((Array.getElem?_eq_getElem _).symm.trans hget)
  have := h.2.2 _ hp (by rw [edgesOf_size]; exact hp)
  rw [hget'] at this
  exact this

theorem budU_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) (D : Array Nat)
    {u v : Nat} (hu1 : 1 ≤ u) (hu2 : u ≤ 22) (hv1 : 1 ≤ v) (hv2 : v ≤ 22)
    (Ry Rz : Array Counter) (n : Nat) (Es : Array Int) (bs : List Bool)
    (s : St) (σ : Nat → Bool) (H : Prop)
    (hF : H → RyzOK col σ n 231 Ry Rz ∧ EdgeOK col σ ∧ n ≤ s.nv ∧ 462 ≤ s.nv ∧ EsOK σ s.nv Es bs) :
    Spec H (budU 22 4 7 Ry Rz (lamD D v) v u Es) s σ
      (fun r s' σ' => ∃ Es', r = ForInStep.yield Es' ∧ EsOK σ' s'.nv Es'
        (bs ++ (if u = v then [] else (List.range' 1 (topOf D v)).map (fun l => thrE col u v l)))) := by
  unfold budU
  by_cases huv : u = v
  · subst huv
    rw [if_pos (by simp)]
    exact spec_pure (fun hH _ _ => ⟨Es, rfl, by simpa using (hF hH).2.2.2.2⟩)
  · rw [if_neg (by simpa using huv)]
    have hvp : VPair u v := ⟨hu1, hu2, hv1, hv2, huv⟩
    dsimp only
    simp only [budStep_eq]
    refine spec_bind (Q₁ := fun Es' s' σ' => EsOK σ' s'.nv Es'
        (bs ++ (List.range' 1 (topOf D v)).map (fun l => thrE col u v l))) ?_
      (fun Es' s' σ' => spec_pure (fun hH _ _ => ⟨Es', rfl, by rw [if_neg huv]; exact hH.2.2.2.2.2⟩))
    refine spec_forIn_range (I := fun t Es' s' σ' => EsOK σ' s'.nv Es'
        (bs ++ (List.range' 1 t).map (fun l => thrE col u v l)) ∧ RyzOK col σ' n 231 Ry Rz ∧
        EdgeOK col σ' ∧ n ≤ s'.nv ∧ 462 ≤ s'.nv) 1 _ _ _ ?_ ?_ ?_
    · intro hH _ _
      obtain ⟨hR, hE, hn, h462, hEs⟩ := hF hH
      exact ⟨by simpa using hEs, hR, hE, hn, h462⟩
    · intro t ht Es' s₁ σ₁
      refine spec_conseq (budStep'_spec col hsym hvp (l := 1 + t) (by omega) Ry Rz n Es' s₁ σ₁ _
        (fun hH => ?_)) (fun h => h) (fun r s₂ σ₂ hH hag hle _ _ hq => ?_)
      · obtain ⟨-, hEs, hR, hE, hn, h462⟩ := hH
        exact ⟨(ryz_at hR hvp).1, (ryz_at hR hvp).2, hE, hn, h462⟩
      · obtain ⟨-, hEs, hR, hE, hn, h462⟩ := hH
        obtain ⟨rfl, hs2, hv⟩ := hq
        show EsOK σ₂ s₂.nv (Es'.push ((s₁.nv + 3 : Nat) : Int)) _ ∧ _
        refine ⟨?_, hR.agree hag hn |>.mono (by omega), EdgeOK.agree hE hag h462, by omega, by omega⟩
        have := ((hEs.agree hag (Nat.le_refl _)).mono (m := s₂.nv) (by omega)).push
          (e := ((s₁.nv + 3 : Nat) : Int)) (by omega) (by simp; omega)
        rw [lv_natCast _ (by omega), hv] at this
        rw [show t + 1 = (1 + t) - 1 + 1 by omega, List.range'_1_concat, List.map_append,
          ← List.append_assoc]
        simpa [show 1 + t - 1 = t by omega, Nat.add_comm] using this
    · intro Es' s' σ' _ _ h
      have htop : (min (lamD D v) (max (7 : Nat) (4 : Nat) : Int)).toNat + 1 - 1 = topOf D v := by
        simp [topOf]
      rw [htop] at h
      exact h.1

theorem budList_succ (col : Nat → Nat → Bool) (D : Array Nat) (v t : Nat) :
    budList col D v (t + 1) = budList col D v t ++
      (if t + 1 = v then [] else (List.range' 1 (topOf D v)).map (fun l => thrE col (t + 1) v l)) := by
  unfold budList
  rw [List.range'_1_concat, List.filter_append, List.flatMap_append]
  by_cases h : t + 1 = v <;> simp [h, Nat.add_comm]

theorem filter_id_le (bs : List Bool) : (bs.filter id).length ≤ bs.length := List.length_filter_le _ _

theorem budV_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) (D : Array Nat)
    (hbud : BudOK col D) {v : Nat} (hv1 : 1 ≤ v) (hv2 : v ≤ 22) (Ry Rz : Array Counter) (n : Nat)
    (s : St) (σ : Nat → Bool) (H : Prop)
    (hF : H → RyzOK col σ n 231 Ry Rz ∧ EdgeOK col σ ∧ n ≤ s.nv ∧ 462 ≤ s.nv) :
    Spec H (budV 22 4 7 D Ry Rz v) s σ (fun _ _ _ => True) := by
  obtain ⟨hlam0, hcount⟩ := hbud v hv1 hv2
  have hlamD : budgetOf ((22 : Nat) : Int) ((4 : Nat) : Int) ((7 : Nat) : Int) ((D[v - 1]! : Nat) : Int) =
    lamD D v := rfl
  unfold budV
  rw [hlamD, if_neg (by omega)]
  refine spec_pure_bind ?_
  refine spec_bind (Q₁ := fun Es s₁ σ₁ => EsOK σ₁ s₁.nv Es (budList col D v 22) ∧
      RyzOK col σ₁ n 231 Ry Rz ∧ EdgeOK col σ₁ ∧ n ≤ s₁.nv ∧ 462 ≤ s₁.nv) ?_ ?_
  · refine spec_forIn_range (I := fun t Es s₁ σ₁ => EsOK σ₁ s₁.nv Es (budList col D v t) ∧
      RyzOK col σ₁ n 231 Ry Rz ∧ EdgeOK col σ₁ ∧ n ≤ s₁.nv ∧ 462 ≤ s₁.nv) 1 (22 + 1) _ _ ?_ ?_
      (fun _ _ _ _ _ h => h)
    · intro hH _ _
      obtain ⟨hR, hE, hn, h462⟩ := hF hH
      exact ⟨by simpa [budList] using EsOK.nil σ s.nv, hR, hE, hn, h462⟩
    · intro t ht Es s₁ σ₁
      refine spec_conseq (budU_spec col hsym D (u := 1 + t) (by omega) (by omega) hv1 hv2 Ry Rz n Es
        (budList col D v t) s₁ σ₁ _ (fun hH => ?_)) (fun h => h) (fun r s₂ σ₂ hH hag hle _ _ hq => ?_)
      · obtain ⟨-, hEs, hR, hE, hn, h462⟩ := hH
        exact ⟨hR, hE, hn, h462, hEs⟩
      · obtain ⟨-, hEs, hR, hE, hn, h462⟩ := hH
        obtain ⟨Es', rfl, hEs'⟩ := hq
        refine ⟨?_, hR.agree hag hn, EdgeOK.agree hE hag h462, by omega, by omega⟩
        rw [budList_succ]
        simpa [Nat.add_comm] using hEs'
  · intro Es s₁ σ₁
    by_cases hEe : Es.isEmpty = true
    · rw [if_pos hEe]
      by_cases hlp : lamD D v > 0
      · rw [if_pos hlp]
        refine spec_add_bind (fun hH hg he => ?_) (spec_pure (fun _ _ _ => trivial))
        exfalso
        obtain ⟨-, -, -, -, -, hEs, -⟩ := hH
        have h0 : Es.size = 0 := by simpa using hEe
        have := filter_id_le (budList col D v 22)
        rw [← hEs.1, h0, hcount] at this
        omega
      · rw [if_neg hlp]
        exact spec_pure_bind (spec_pure (fun _ _ _ => trivial))
    · rw [if_neg hEe]
      refine spec_pure_bind ?_
      dsimp only
      refine spec_bind (bidirCounter_spec Es _ s₁ σ₁ _ (fun hH => ?_)) (fun Rb s₂ σ₂ => ?_)
      · obtain ⟨-, -, -, -, -, hEs, -⟩ := hH
        exact hEs.lits
      -- the facts after the counter
      have key : ∀ Hp : Prop, (Hp → After (After H s σ s₁ σ₁ (EsOK σ₁ s₁.nv Es (budList col D v 22) ∧
            RyzOK col σ₁ n 231 Ry Rz ∧ EdgeOK col σ₁ ∧ n ≤ s₁.nv ∧ 462 ≤ s₁.nv)) s₁ σ₁ s₂ σ₂
            (CounterOK σ₂ Es (min Es.size ((lamD D v).toNat + 1)) Rb s₁.nv s₂.nv)) → Hp →
          CounterOK σ₂ Es (min Es.size ((lamD D v).toNat + 1)) Rb s₁.nv s₂.nv ∧
          cnt σ₂ Es Es.size = (lamD D v).toNat ∧ (lamD D v).toNat ≤ Es.size := by
        intro Hp hHp h
        obtain ⟨⟨-, -, -, -, -, hEs, -⟩, -, h12, ag12, -, hC⟩ := hHp h
        refine ⟨hC, ?_, ?_⟩
        · rw [cnt_congr ag12 (fun l hl => (hEs.lits l hl).2), hEs.cnt, hcount]
        · have := filter_id_le (budList col D v 22)
          rw [hcount, ← hEs.1] at this
          exact this
      have jp2 : ∀ (Hp : Prop) (s' : St), (Hp → After (After H s σ s₁ σ₁ (EsOK σ₁ s₁.nv Es
            (budList col D v 22) ∧ RyzOK col σ₁ n 231 Ry Rz ∧ EdgeOK col σ₁ ∧ n ≤ s₁.nv ∧
            462 ≤ s₁.nv)) s₁ σ₁ s₂ σ₂
            (CounterOK σ₂ Es (min Es.size ((lamD D v).toNat + 1)) Rb s₁.nv s₂.nv) ∧ s'.nv = s₂.nv) →
          Spec Hp (if (lamD D v).toNat + 1 ≤ Es.size then (do
              let x ← Rb.at Es.size ((lamD D v).toNat + 1) "budget"
              let y ← add #[-x]
              (fun _ => pure (ForInStep.yield ())) y) else (do
              let y ← pure PUnit.unit
              (fun _ => pure (ForInStep.yield ())) y)) s' σ₂ (fun _ _ _ => True) := by
        intro Hp s' hHp
        refine spec_optAt (c := (lamD D v).toNat + 1 ≤ Es.size) Rb Es.size ((lamD D v).toNat + 1)
          "budget" (fun x => #[-x]) _ ?_ (fun _ _ _ => spec_pure (fun _ _ _ => trivial))
        rintro x hc ⟨w, hw, rfl⟩ hH hg he
        obtain ⟨hC, hcnt, hle⟩ := key Hp (fun h => (hHp h).1) hH
        obtain ⟨w0, wn⟩ := hC.range _ _ _ hw
        have wv := hC.val _ _ _ hw
        have hs' := (hHp hH).2
        refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
        · rw [mem1] at hl; subst hl; simp; omega
        · rw [mem1] at hl; subst hl; omega
        · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
          rw [lv_neg_natCast _ (by omega), wv, hcnt]
          simp
      by_cases h1 : (lamD D v).toNat ≥ 1
      · rw [if_pos h1]
        by_cases h2 : (lamD D v).toNat ≤ Es.size
        · rw [if_pos h2]
          refine spec_at_bind' (fun s' x hnv hcls hx => spec_add_bind' (fun hH hg he => ?_)
            (fun s'' hnv' hm => jp2 _ s'' (fun hH => ⟨hH, by rw [hnv', hnv]⟩)))
          obtain ⟨rfl, w, hw, rfl⟩ := hx (by simpa using he)
          obtain ⟨hC, hcnt, hle⟩ := key _ id hH
          obtain ⟨w0, wn⟩ := hC.range _ _ _ hw
          have wv := hC.val _ _ _ hw
          refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
          · rw [mem1] at hl; subst hl; simp; omega
          · rw [mem1] at hl; subst hl; omega
          · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
            rw [lv_natCast _ (by omega), wv, hcnt]
            simp
        · rw [if_neg h2]
          refine spec_add_bind (fun hH hg he => ?_) (jp2 _ _ (fun hH => ⟨hH, rfl⟩))
          exfalso
          exact h2 (key _ id hH).2.2
      · rw [if_neg h1]
        exact spec_pure_bind (jp2 _ _ (fun hH => ⟨hH, rfl⟩))

theorem budBlock_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) (D : Array Nat)
    (hbud : BudOK col D) (Ry Rz : Array Counter) (n : Nat) (s : St) (σ : Nat → Bool) (H : Prop)
    (hF : H → RyzOK col σ n 231 Ry Rz ∧ EdgeOK col σ ∧ n ≤ s.nv ∧ 462 ≤ s.nv) :
    Spec H (budBlock 22 4 7 D Ry Rz) s σ (fun _ _ _ => True) := by
  rw [budBlock_eq]
  unfold budBlock2
  refine spec_bind (Q₁ := fun _ _ _ => True) ?_ (fun _ _ _ => spec_pure (fun _ _ _ => trivial))
  refine spec_forIn_range (I := fun _ _ s₁ σ₁ => RyzOK col σ₁ n 231 Ry Rz ∧ EdgeOK col σ₁ ∧
    n ≤ s₁.nv ∧ 462 ≤ s₁.nv) 1 (22 + 1) _ _ (fun hH _ _ => hF hH) ?_ (fun _ _ _ _ _ _ => trivial)
  intro v hv _ s₁ σ₁
  refine spec_conseq (budV_spec col hsym D hbud (v := 1 + v) (by omega) (by omega) Ry Rz n s₁ σ₁ _
    (fun hH => hH.2)) (fun h => h) (fun r s₂ σ₂ hH hag hle _ _ _ => ?_)
  obtain ⟨-, hR, hE, hn, h462⟩ := hH
  have : RyzOK col σ₂ n 231 Ry Rz ∧ EdgeOK col σ₂ ∧ n ≤ s₂.nv ∧ 462 ≤ s₂.nv :=
    ⟨hR.agree hag hn, EdgeOK.agree hE hag h462, by omega, by omega⟩
  cases r <;> exact this

end SB.Rooted

#print axioms SB.Rooted.budBlock_spec
