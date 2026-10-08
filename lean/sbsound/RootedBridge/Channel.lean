/-
# M3: the channel clauses of `add_counting`

For every pair and colour `a`: `C ≥ q ↔ R ≥ q + L` (`L = (N-2) - d_i - d_j + 2a`), where an
out-of-range right-hand side becomes a plain bound on `C`. Satisfied when, for the pair's actual
colour, `R = L + C` (M1 Lemma 2.1 at the prescribed degrees) and `R ≤ 7` (no red `K_{2,8}`).
-/
import RootedBridge.Intervals

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

/-- Lemma 2.1 at the prescribed degrees, and the red cap. -/
def ChanOK (col : Nat → Nat → Bool) (D : Array Nat) : Prop :=
  ∀ i j, 1 ≤ i → i < j → j ≤ 22 →
    (Cr col i j : Int) = 20 - ((D[i - 1]! : Nat) : Int) - ((D[j - 1]! : Nat) : Int) +
      2 * (if col i j then 1 else 0) + (Cb col i j : Int) ∧ Cr col i j ≤ 7

theorem CntFacts.none {σ : Nat → Bool} {R : Counter} {kmax C n t : Nat} (h : CntFacts σ R kmax C n)
    (hn : R.get? 20 t = none) : ¬ (1 ≤ t ∧ t ≤ min 20 kmax) := by
  intro h'
  have := (h.1 t).mpr h'
  rw [hn] at this
  simp at this

theorem cond_factsZ (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) {σ : Nat → Bool}
    (hE : EdgeOK col σ) {i j : Nat} (hv : VPair i j) {a : Int} (ha : a = 0 ∨ a = 1) :
    let cond := if (a == 1) = true then -varE 22 2 i j 2 else varE 22 2 i j 2
    cond ≠ 0 ∧ cond.natAbs ≤ 462 ∧ lv σ cond = !(decide ((if col i j then 1 else 0 : Int) = a)) := by
  intro cond
  have hb := varE_bounds hv (Or.inr rfl)
  have hl := lv_varE hsym hE hv (Or.inr rfl)
  simp only [colV, if_true] at hl
  rcases ha with rfl | rfl
  · simp only [cond, show ((0 : Int) == 1) = false from rfl, Bool.false_eq_true, if_false]
    refine ⟨hb.2.2, hb.2.1, ?_⟩
    rw [hl]; cases col i j <;> simp
  · simp only [cond, beq_self_eq_true, if_true]
    refine ⟨by omega, by rw [Int.natAbs_neg]; exact hb.2.1, ?_⟩
    rw [lv_neg _ hb.2.2, hl]; cases col i j <;> simp

theorem chanBlock_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) (D : Array Nat)
    (hch : ChanOK col D) (Ry Rz : Array Counter) (n : Nat) (s : St) (σ : Nat → Bool) (H : Prop)
    (hF : H → RyzOK col σ n 231 Ry Rz ∧ EdgeOK col σ ∧ n ≤ s.nv ∧ 462 ≤ s.nv) :
    Spec H (chanBlock 22 4 D Ry Rz) s σ (fun _ s' σ' => s'.nv = s.nv ∧ σ' = σ) := by
  unfold chanBlock
  dsimp only
  refine spec_of_co_gated (post := fun _ => True)
    (F := RyzOK col σ n 231 Ry Rz ∧ EdgeOK col σ ∧ n ≤ s.nv ∧ 462 ≤ s.nv) ?_ hF
    (fun _ _ _ _ => ⟨rfl, rfl⟩)
  refine co_bind' ?_ (fun _ _ => co_pure trivial)
  apply co_forIn_array
  intro e he _ s₁
  obtain ⟨i, j⟩ := e
  obtain ⟨hi1, hij, hj2⟩ := mem_edgesOf he
  dsimp only at hi1 hij hj2 ⊢
  have hv : VPair i j := ⟨hi1, by omega, by omega, hj2, by omega⟩
  have hp := edgeIdx_lt hi1 hij hj2
  have hget := edgesOf_get hi1 hij hj2
  refine co_bind' ?_ (fun _ _ => co_bind' (co_pure trivial) (fun _ _ => co_pure trivial))
  apply co_forIn
  intro a ha _ s₂
  have ha' : a = 0 ∨ a = 1 := by simp at ha; omega
  refine co_bind' ?_ (fun _ _ => co_bind' (co_pure trivial) (fun _ _ => co_pure trivial))
  apply co_forIn_range
  intro q hq1 hq2 _ s₃
  have hget' : (edgesOf 22)[edgeIdx 22 i j]'(by rw [edgesOf_size]; exact hp) = (i, j) :=
    Option.some.inj ((Array.getElem?_eq_getElem _).symm.trans hget)
  -- all facts a leaf can use
  have facts : RyzOK col σ n 231 Ry Rz ∧ EdgeOK col σ ∧ n ≤ s.nv ∧ 462 ≤ s.nv →
      CntFacts σ Ry[edgeIdx 22 i j]! 5 (Cb col i j) n ∧ CntFacts σ Rz[edgeIdx 22 i j]! 8 (Cr col i j) n ∧
      EdgeOK col σ ∧ n ≤ s.nv ∧ 462 ≤ s.nv := by
    intro ⟨hR, hE, hn, h462⟩
    have := hR.2.2 (edgeIdx 22 i j) hp (by rw [edgesOf_size]; exact hp)
    rw [hget'] at this
    exact ⟨this.1, this.2, hE, hn, h462⟩
  obtain ⟨hc1, hc2⟩ := hch i j hi1 hij hj2
  split
  · exact co_pure trivial
  · next lhsN hl =>
    split
    · next hq0 =>
      co_step
      intro hFF
      obtain ⟨cy, cz, hE, hn, h462⟩ := facts hFF
      obtain ⟨c0, c1, c2⟩ := cond_factsZ col hsym hE hv ha'
      obtain ⟨l0, ln, lv'⟩ := cy.2 _ _ hl
      refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
      · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_natCast]) <;> omega
      · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> omega
      · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
        rw [c2, lv_natCast _ l0, lv']
        rcases ha' with rfl | rfl <;> cases hcol : col i j <;> simp [hcol] at hc1 ⊢ <;> omega
    · split
      · next hq0 hbad =>
        co_step
        intro hFF
        obtain ⟨cy, cz, hE, hn, h462⟩ := facts hFF
        obtain ⟨c0, c1, c2⟩ := cond_factsZ col hsym hE hv ha'
        obtain ⟨l0, ln, lv'⟩ := cy.2 _ _ hl
        refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
        · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> omega
        · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl <;> omega
        · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
          rw [c2, lv_neg_natCast _ l0, lv']
          simp only [Bool.or_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hbad
          rcases hbad with hbig | hnone
          · rcases ha' with rfl | rfl <;> cases hcol : col i j <;> simp [hcol] at hc1 hbig ⊢ <;> omega
          · have hns := cz.none hnone
            rcases ha' with rfl | rfl <;> cases hcol : col i j <;> simp [hcol] at hc1 hns hq0 ⊢ <;> omega
      · next hq0 hbad =>
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Option.isNone_iff_eq_none] at hbad
        obtain ⟨hsmall, hsome⟩ := hbad
        obtain ⟨v, hv'⟩ := Option.ne_none_iff_exists'.mp hsome
        rw [hv', Option.getD_some]
        co_step
        all_goals
          intro hFF
          obtain ⟨cy, cz, hE, hn, h462⟩ := facts hFF
          obtain ⟨c0, c1, c2⟩ := cond_factsZ col hsym hE hv ha'
          obtain ⟨l0, ln, lv'⟩ := cy.2 _ _ hl
          obtain ⟨v0, vn, vv⟩ := cz.2 _ _ hv'
          refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
          · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> omega
          · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl | rfl <;> omega
          · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
            simp only [c2, lv_neg_natCast _ l0, lv_natCast _ l0, lv_neg_natCast _ v0, lv_natCast _ v0, lv', vv]
            rcases ha' with rfl | rfl <;> cases hcol : col i j <;> simp [hcol] at hc1 hq0 hsmall ⊢ <;> omega

end SB.Rooted
#print axioms SB.Rooted.chanBlock_spec
