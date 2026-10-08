/-
# M3: the exact-degree block of `add_counting`

For every vertex `v`, the literals `x_u = [vu blue]` (`u ≠ v`, ascending) feed a bidirectional
counter, and the units `R(21, d)` and `¬R(21, d+1)` assert blue degree exactly `d = D[v-1]`.
Satisfied by the truthful assignment of a colouring whose blue degrees are `D`.
-/
import RootedBridge.CountingDefs
import RootedBridge.Base

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

theorem spec_at {H : Prop} {s : St} {σ : Nat → Bool} (R : Counter) (i j : Nat) (ctx : String) :
    Spec H (R.at i j ctx) s σ (fun x s' σ' => s' = s ∧ σ' = σ ∧ ∃ v, R.get? i j = some v ∧ x = (v : Int)) := by
  unfold Counter.at
  split
  · next v hv => exact spec_pure (fun _ _ _ => ⟨rfl, rfl, v, hv, rfl⟩)
  · exact spec_fail_bind (fun _ => mono_pure)

/-- `add c` followed by more code, with the path condition unchanged. -/
theorem spec_add_bind {β : Type} {H : Prop} {s : St} {σ : Nat → Bool} {c : Array Int}
    {f : Unit → EncM β} {Q : β → St → (Nat → Bool) → Prop}
    (hc : H → Good s σ → s.errs = #[] → (∀ l ∈ c, l.natAbs ≤ s.nv) ∧ ClauseSat σ c)
    (hf : Spec H (f ()) { s with cls := s.cls.push c } σ Q) : Spec H (add c >>= f) s σ Q := by
  have hrun : (add c >>= f).run s = (f ()).run { s with cls := s.cls.push c } := rfl
  refine ⟨fun he => ?_, fun hH hg he => ?_⟩
  · rw [hrun] at he; exact hf.1 he
  · rw [hrun] at he ⊢
    have he' := hf.1 he
    obtain ⟨hv, hcs⟩ := hc hH hg he'
    exact hf.2 hH ⟨vle_push hg.1 hv, clsSat_push hg.2 hcs⟩ he

/-- `R.at i j` followed by more code: the continuation may assume the register exists. -/
theorem spec_at_bind {β : Type} {H : Prop} {s : St} {σ : Nat → Bool} {R : Counter} {i j : Nat}
    {ctx : String} {f : Int → EncM β} {Q : β → St → (Nat → Bool) → Prop}
    (hf : ∀ x s₁ σ₁, Spec (H ∧ s₁ = s ∧ σ₁ = σ ∧ ∃ v, R.get? i j = some v ∧ x = (v : Int))
      (f x) s₁ σ₁ Q) :
    Spec H (R.at i j ctx >>= f) s σ Q :=
  spec_bind (spec_at R i j ctx) (fun x s₁ σ₁ => spec_weaken (hf x s₁ σ₁)
    (fun h => ⟨h.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩))

/-- `R.at i j` followed by more code, keeping `σ`: the continuation is proved from any state with
the same variable count and clauses; the register facts are available once the state is error-free. -/
theorem spec_at_bind' {β : Type} {H : Prop} {s : St} {σ : Nat → Bool} {R : Counter} {i j : Nat}
    {ctx : String} {f : Int → EncM β} {Q : β → St → (Nat → Bool) → Prop}
    (hf : ∀ (s' : St) (x : Int), s'.nv = s.nv → s'.cls = s.cls →
      (s'.errs = #[] → s' = s ∧ ∃ v, R.get? i j = some v ∧ x = (v : Int)) → Spec H (f x) s' σ Q) :
    Spec H (R.at i j ctx >>= f) s σ Q := by
  unfold Counter.at
  split
  · next v hv => exact hf s v rfl rfl (fun _ => ⟨rfl, v, hv, rfl⟩)
  · have h := hf { s with errs := s.errs.push s!"KeyError ({i}, {j}) in {ctx}" } 0 rfl rfl
      (fun he => by have := congrArg Array.size he; simp at this)
    have hrun : ((do fail s!"KeyError ({i}, {j}) in {ctx}"; return (0 : Int)) >>= f).run s =
        (f 0).run { s with errs := s.errs.push s!"KeyError ({i}, {j}) in {ctx}" } := rfl
    refine ⟨fun he => ?_, fun _ _ he => ?_⟩ <;>
    · exfalso
      rw [hrun] at he
      have h2 := congrArg Array.size (h.1 he)
      simp at h2

/-- `add c` followed by more code, the continuation proved from any state with the same count. -/
theorem spec_add_bind' {β : Type} {H : Prop} {s : St} {σ : Nat → Bool} {c : Array Int}
    {f : Unit → EncM β} {Q : β → St → (Nat → Bool) → Prop}
    (hc : H → Good s σ → s.errs = #[] → (∀ l ∈ c, l.natAbs ≤ s.nv) ∧ ClauseSat σ c)
    (hf : ∀ s' : St, s'.nv = s.nv → (s'.errs = #[] → s.errs = #[]) → Spec H (f ()) s' σ Q) :
    Spec H (add c >>= f) s σ Q :=
  spec_add_bind hc (hf _ rfl (fun h => h))

/-- `fresh` (given the value `b`) followed by more code, with the path condition unchanged. -/
theorem spec_fresh_bind {β : Type} {H : Prop} {s : St} {σ : Nat → Bool} (b : Bool)
    {f : Nat → EncM β} {Q : β → St → (Nat → Bool) → Prop}
    (hf : Spec H (f (s.nv + 1)) { s with nv := s.nv + 1 } (upd σ (s.nv + 1) b) Q) :
    Spec H (fresh >>= f) s σ Q := by
  have hrun : (fresh >>= f).run s = (f (s.nv + 1)).run { s with nv := s.nv + 1 } := rfl
  refine ⟨fun he => ?_, fun hH hg he => ?_⟩
  · rw [hrun] at he; exact hf.1 he
  · rw [hrun] at he ⊢
    have hg' : Good { s with nv := s.nv + 1 } (upd σ (s.nv + 1) b) :=
      ⟨vle_mono hg.1 (Nat.le_succ _), clsSat_agree (agree_upd σ s.nv b) hg.1 hg.2⟩
    obtain ⟨hnv, hv, σ', hag, hs, hq⟩ := hf.2 hH hg' he
    exact ⟨by simp at hnv ⊢; omega, hv, σ', agree_trans (agree_upd σ s.nv b) hag (Nat.le_succ _), hs, hq⟩

theorem spec_pure_bind {α β : Type} {H : Prop} {s : St} {σ : Nat → Bool} {x : α}
    {f : α → EncM β} {Q : β → St → (Nat → Bool) → Prop}
    (h : Spec H (f x) s σ Q) : Spec H (pure x >>= f) s σ Q := h

/-- Blue neighbours of `v` among `1..t`. -/
def blueUpTo (col : Nat → Nat → Bool) (v t : Nat) : List Nat :=
  (List.range' 1 t).filter (fun u => u != v && col v u)

/-- The blue degrees are `D`. -/
def DegOK (col : Nat → Nat → Bool) (D : Array Nat) : Prop :=
  ∀ v, 1 ≤ v → v ≤ 22 → (blueUpTo col v 22).length = D[v - 1]!

theorem blueUpTo_succ (col : Nat → Nat → Bool) (v t : Nat) :
    blueUpTo col v (t + 1) = blueUpTo col v t ++ (if (t + 1 != v && col v (t + 1)) then [t + 1] else []) := by
  unfold blueUpTo
  rw [List.range'_1_concat, List.filter_append]
  simp only [List.filter_cons, List.filter_nil]
  split <;> simp_all [Nat.add_comm]

def chkTwentyOne : Bool := (List.range 23).all fun w =>
  !(1 ≤ w && w ≤ 22) || ((List.range' 1 22).filter (fun u => u != w)).length == 21

theorem chkTwentyOne_true : chkTwentyOne = true := by decide +kernel

theorem filter_twentyOne {w : Nat} (h1 : 1 ≤ w) (h2 : w ≤ 22) :
    ((List.range' 1 22).filter (fun u => u != w)).length = 21 := by
  have h := chkTwentyOne_true
  simp only [chkTwentyOne, List.all_eq_true, List.mem_range] at h
  have := h w (by omega)
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    beq_iff_eq] at this
  omega

theorem filter_ne_succ (w t : Nat) :
    ((List.range' 1 (t + 1)).filter (fun u => u != w)).length =
      ((List.range' 1 t).filter (fun u => u != w)).length + (if t + 1 = w then 0 else 1) := by
  rw [List.range'_1_concat, List.filter_append]
  simp only [List.filter_cons, List.filter_nil, List.length_append]
  by_cases h : t + 1 = w <;> simp [h, Nat.add_comm]

theorem degBlock_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) (D : Array Nat)
    (hdeg : DegOK col D) (s : St) (σ : Nat → Bool) (H : Prop)
    (hpre : H → 462 ≤ s.nv ∧ EdgeOK col σ) :
    Spec H (degBlock 22 D) s σ (fun _ _ _ => True) := by
  unfold degBlock
  dsimp only
  refine spec_forIn_range (I := fun _ _ s₁ σ₁ => 462 ≤ s₁.nv ∧ EdgeOK col σ₁) 1 23 _ _
    (fun hH _ _ => hpre hH) ?_ (fun _ _ _ _ _ _ => trivial)
  intro v hv _ s₁ σ₁
  have hw1 : 1 ≤ 1 + v := by omega
  have hw2 : 1 + v ≤ 22 := by omega
  generalize 1 + v = w at hw1 hw2 ⊢
  refine spec_bind (Q₁ := fun xs s₂ σ₂ => s₂.nv = s₁.nv ∧ σ₂ = σ₁ ∧
      (∀ l ∈ xs, l ≠ 0 ∧ l.natAbs ≤ 462) ∧ cnt σ₁ xs xs.size = (blueUpTo col w 22).length ∧
      xs.size = 21) ?_ ?_
  · refine spec_forIn_range (I := fun t xs s₂ σ₂ => s₂.nv = s₁.nv ∧ σ₂ = σ₁ ∧
      (∀ l ∈ xs, l ≠ 0 ∧ l.natAbs ≤ 462) ∧ cnt σ₁ xs xs.size = (blueUpTo col w t).length ∧
      xs.size = ((List.range' 1 t).filter (fun u => u != w)).length) 1 23 _ _ ?_ ?_ ?_
    · intro _ _ _; exact ⟨rfl, rfl, by simp, by simp [cnt, blueUpTo], by simp⟩
    · intro t ht xs s₂ σ₂
      split
      · next hne =>
        refine spec_bind (spec_pure (Q := fun _ s₃ σ₃ => s₃ = s₂ ∧ σ₃ = σ₂) (fun _ _ _ => ⟨rfl, rfl⟩)) ?_
        intro _ s₃ σ₃
        refine spec_pure (fun hH _ _ => ?_)
        obtain ⟨⟨⟨hH0, hn₁, hE₁⟩, hs2, hσ2, hx1, hx2, hx3⟩, -, -, -, -, hs3, hσ3⟩ := hH
        rw [hs3, hσ3]
        have hne' : t + 1 ≠ w := by simp at hne; omega
        have hv : VPair w (t + 1) := ⟨hw1, hw2, by omega, by omega, by omega⟩
        have hb := varE_bounds hv (Or.inr rfl)
        rw [Nat.add_comm 1 t]
        refine ⟨hs2, hσ2, fun l hl => ?_, ?_, ?_⟩
        · rcases Array.mem_push.mp hl with hl | rfl
          · exact hx1 l hl
          · exact ⟨hb.2.2, hb.2.1⟩
        · rw [Array.size_push, cnt_push, hx2, blueUpTo_succ, lv_varE hsym hE₁ hv (Or.inr rfl)]
          simp [colV, hne']
          split <;> simp
        · rw [Array.size_push, hx3, filter_ne_succ, if_neg hne']
      · next heq =>
        refine spec_bind (spec_pure (Q := fun _ s₃ σ₃ => s₃ = s₂ ∧ σ₃ = σ₂) (fun _ _ _ => ⟨rfl, rfl⟩)) ?_
        intro _ s₃ σ₃
        refine spec_pure (fun hH _ _ => ?_)
        obtain ⟨⟨⟨hH0, hn₁, hE₁⟩, hs2, hσ2, hx1, hx2, hx3⟩, -, -, -, -, hs3, hσ3⟩ := hH
        rw [hs3, hσ3]
        have heq' : t + 1 = w := by simp at heq; omega
        refine ⟨hs2, hσ2, hx1, ?_, ?_⟩
        · rw [hx2, blueUpTo_succ]; simp [heq']
        · rw [hx3, filter_ne_succ, if_pos heq', Nat.add_zero]
    · intro xs s₂ σ₂ _ _ h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      exact ⟨h1, h2, h3, h4, by rw [h5]; exact filter_twentyOne hw1 hw2⟩
  · intro xs s₂ σ₂
    refine spec_bind (bidirCounter_spec xs _ s₂ σ₂ _ (fun hH => ?_)) ?_
    · obtain ⟨⟨-, hn₁, -⟩, -, -, -, -, hs2, -, hx1, -⟩ := hH
      exact fun l hl => ⟨(hx1 l hl).1, by have := (hx1 l hl).2; omega⟩
    intro R s₃ σ₃
    -- the facts used by both unit clauses
    have key : ∀ (Hp : Prop), (Hp → After (After (H ∧ 462 ≤ s₁.nv ∧ EdgeOK col σ₁) s₁ σ₁ s₂ σ₂
        (s₂.nv = s₁.nv ∧ σ₂ = σ₁ ∧ (∀ l ∈ xs, l ≠ 0 ∧ l.natAbs ≤ 462) ∧
          cnt σ₁ xs xs.size = (blueUpTo col w 22).length ∧ xs.size = 21))
        s₂ σ₂ s₃ σ₃ (CounterOK σ₃ xs (min xs.size (D[w - 1]! + 1)) R s₂.nv s₃.nv)) →
        Hp → (CounterOK σ₃ xs (min xs.size (D[w - 1]! + 1)) R s₂.nv s₃.nv ∧
          cnt σ₃ xs xs.size = D[w - 1]! ∧ xs.size = 21 ∧ 462 ≤ s₃.nv ∧ EdgeOK col σ₃) := by
      intro Hp hHp h
      obtain ⟨⟨⟨-, hn₁, hE₁⟩, -, -, -, -, hs2, hσ2, hx1, hx2, hx3⟩, -, hle3, hag3, -, hC⟩ := hHp h
      subst hσ2
      refine ⟨hC, ?_, hx3, by omega, EdgeOK.agree hE₁ hag3 (by omega)⟩
      rw [cnt_congr hag3 (fun l hl => by have := (hx1 l hl).2; omega), hx2]
      exact hdeg w hw1 hw2
    -- the second unit, run from any state with σ₃'s values below `s₃.nv`
    have second : ∀ (Hp : Prop) (s₄ : St) (σ₄ : Nat → Bool),
        (Hp → After (After (H ∧ 462 ≤ s₁.nv ∧ EdgeOK col σ₁) s₁ σ₁ s₂ σ₂
          (s₂.nv = s₁.nv ∧ σ₂ = σ₁ ∧ (∀ l ∈ xs, l ≠ 0 ∧ l.natAbs ≤ 462) ∧
            cnt σ₁ xs xs.size = (blueUpTo col w 22).length ∧ xs.size = 21))
          s₂ σ₂ s₃ σ₃ (CounterOK σ₃ xs (min xs.size (D[w - 1]! + 1)) R s₂.nv s₃.nv) ∧
          s₃.nv ≤ s₄.nv ∧ Agree σ₃ σ₄ s₃.nv) →
        Spec Hp (if D[w - 1]! + 1 ≤ xs.size then do
              let x ← R.at xs.size (D[w - 1]! + 1) "degree"
              add #[-x]
              pure (ForInStep.yield PUnit.unit)
            else do
              pure PUnit.unit
              pure (ForInStep.yield PUnit.unit)) s₄ σ₄
          (StepPost (fun _ _ s₁ σ₁ => 462 ≤ s₁.nv ∧ EdgeOK col σ₁) v (23 - 1)) := by
      intro Hp s₄ σ₄ hHp
      split
      · refine spec_bind (spec_at _ _ _ _) (fun x s₅ σ₅ => ?_)
        refine spec_bind (Q₁ := fun _ s₆ σ₆ => s₆.nv = s₅.nv ∧ σ₆ = σ₅) (spec_add (fun hH _ _ => ?_)) ?_
        · obtain ⟨hp, -, -, -, -, rfl, rfl, v', hv', rfl⟩ := hH
          obtain ⟨hb, hle4, hag4⟩ := hHp hp
          obtain ⟨hC, hcnt, hsz, hn3, hE3⟩ := key _ id hb
          have hr := hC.range _ _ _ hv'
          have hvv := hC.val _ _ _ hv'
          refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_, rfl, rfl⟩
          · simp at hl; subst hl; simp; omega
          · simp at hl; subst hl; omega
          · simp [lv_neg_natCast _ (by omega : 0 < v'), hag4 v' hr.2, hvv, hcnt]
        · intro _ s₆ σ₆
          refine spec_pure (fun hH _ _ => ?_)
          obtain ⟨⟨hp, -, -, -, -, rfl, rfl, -⟩, -, -, -, -, hs6, rfl⟩ := hH
          obtain ⟨hb, hle4, hag4⟩ := hHp hp
          obtain ⟨hC, hcnt, hsz, hn3, hE3⟩ := key _ id hb
          exact ⟨by omega, EdgeOK.agree hE3 hag4 (by omega)⟩
      · refine spec_bind (spec_pure (Q := fun _ s₅ σ₅ => s₅ = s₄ ∧ σ₅ = σ₄) (fun _ _ _ => ⟨rfl, rfl⟩)) ?_
        intro _ s₅ σ₅
        refine spec_pure (fun hH _ _ => ?_)
        obtain ⟨hp, -, -, -, -, rfl, rfl⟩ := hH
        obtain ⟨hb, hle4, hag4⟩ := hHp hp
        obtain ⟨hC, hcnt, hsz, hn3, hE3⟩ := key _ id hb
        exact ⟨by omega, EdgeOK.agree hE3 hag4 (by omega)⟩
    split
    · refine spec_bind (spec_at _ _ _ _) (fun x s₄ σ₄ => ?_)
      refine spec_bind (Q₁ := fun _ s₅ σ₅ => s₅.nv = s₄.nv ∧ σ₅ = σ₄) (spec_add (fun hH _ _ => ?_)) ?_
      · obtain ⟨hb, -, -, -, -, rfl, rfl, v', hv', rfl⟩ := hH
        obtain ⟨hC, hcnt, hsz, hn3, hE3⟩ := key _ id hb
        have hr := hC.range _ _ _ hv'
        have hvv := hC.val _ _ _ hv'
        refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_, rfl, rfl⟩
        · simp at hl; subst hl; simp; omega
        · simp at hl; subst hl; omega
        · simp [lv_natCast _ (by omega : 0 < v'), hvv, hcnt]
      · intro _ s₅ σ₅
        exact second _ s₅ σ₅ (fun hH => by
          obtain ⟨⟨hb, -, -, -, -, rfl, rfl, -⟩, -, hle5, hag5, -, hs5, rfl⟩ := hH
          exact ⟨hb, by omega, agree_refl _ _⟩)
    · refine spec_bind (spec_pure (Q := fun _ s₄ σ₄ => s₄ = s₃ ∧ σ₄ = σ₃) (fun _ _ _ => ⟨rfl, rfl⟩)) ?_
      intro _ s₄ σ₄
      exact second _ s₄ σ₄ (fun hH => by
        obtain ⟨hb, -, -, -, -, rfl, rfl⟩ := hH
        exact ⟨hb, Nat.le_refl _, agree_refl _ _⟩)

end SB.Rooted
#print axioms SB.Rooted.degBlock_spec
