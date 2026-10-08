/-
# M3: `add_counting` (degree, intervals, channel, budget) as a whole
-/
import RootedBridge.Budget

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

theorem addCounting_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) (D : Array Nat)
    (tight budget channel : Bool) (hdeg : DegOK col D) (hiv : IvOK col D tight)
    (hch : channel = true → ChanOK col D) (hbud : budget = true → BudOK col D)
    (s : St) (σ : Nat → Bool) (H : Prop) (hpre : H → 462 ≤ s.nv ∧ EdgeOK col σ) :
    Spec H (addCounting 22 4 7 D tight budget channel) s σ
      (fun co s' σ' => RyzOK col σ' s'.nv 231 co.Ry co.Rz ∧ 462 ≤ s'.nv ∧ EdgeOK col σ') := by
  rw [addCounting_eq]
  unfold addCountingAlt
  refine spec_bind (spec_nclauses (Q := fun _ s₁ σ₁ => s₁ = s ∧ σ₁ = σ) (fun _ _ _ => ⟨rfl, rfl⟩))
    (fun n0 s₁ σ₁ => ?_)
  refine spec_bind (degBlock_spec col hsym D hdeg s₁ σ₁ _ (fun hH => ?_)) (fun _ s₂ σ₂ => ?_)
  · obtain ⟨hH0, -, -, -, -, rfl, rfl⟩ := hH
    exact hpre hH0
  refine spec_bind (spec_nclauses (Q := fun _ s₃ σ₃ => s₃ = s₂ ∧ σ₃ = σ₂) (fun _ _ _ => ⟨rfl, rfl⟩))
    (fun nDeg s₃ σ₃ => ?_)
  rw [ivLoop_eq]
  refine spec_bind (ivLoop2_spec col hsym D tight hiv s₃ σ₃ _ (fun hH => ?_)) (fun RR s₄ σ₄ => ?_)
  · obtain ⟨⟨⟨hH0, -, -, -, -, rfl, rfl⟩, -, h12, ag12, -, -⟩, -, -, -, -, rfl, rfl⟩ := hH
    obtain ⟨hn, hE⟩ := hpre hH0
    exact ⟨by omega, EdgeOK.agree hE ag12 hn⟩
  obtain ⟨Ry, Rz⟩ := RR
  dsimp only
  -- the facts after the interval loop
  have key : ∀ Hp : Prop, (Hp → After (After (After (After H s σ s₁ σ₁ (s₁ = s ∧ σ₁ = σ)) s₁ σ₁ s₂ σ₂
      True) s₂ σ₂ s₃ σ₃ (s₃ = s₂ ∧ σ₃ = σ₂)) s₃ σ₃ s₄ σ₄ (RyzOK col σ₄ s₄.nv 231 (Ry, Rz).1 (Ry, Rz).2 ∧
      462 ≤ s₄.nv ∧ EdgeOK col σ₄)) → Hp → RyzOK col σ₄ s₄.nv 231 Ry Rz ∧ 462 ≤ s₄.nv ∧ EdgeOK col σ₄ := by
    intro Hp h hp
    obtain ⟨-, -, -, -, -, h1, h2, h3⟩ := h hp
    exact ⟨h1, h2, h3⟩
  -- the budget part and the return, from a state agreeing with σ₄
  have tail : ∀ (Hp : Prop) (s₅ : St) (σ₅ : Nat → Bool),
      (Hp → RyzOK col σ₅ s₄.nv 231 Ry Rz ∧ 462 ≤ s₄.nv ∧ EdgeOK col σ₅ ∧ s₄.nv ≤ s₅.nv) →
      Spec Hp (do
          let __do_lift ← nclauses
          have nInt : Nat := __do_lift - n0 - (nDeg - n0)
          have counts : List (String × Nat) := [("degree", nDeg - n0), ("intervals", nInt)]
          have __do_jp : List (String × Nat) → PUnit → EncM CountOut := fun counts y =>
            pure { counts := counts, Ry := Ry, Rz := Rz }
          if budget = true then do
              budBlock 22 4 7 D Ry Rz
              let __do_lift ← nclauses
              have nB : Nat := __do_lift - n0 - (nDeg - n0) - nInt
              have counts : List (String × Nat) := counts ++ [("budget", nB)]
              let y ← pure PUnit.unit
              __do_jp counts y
            else do
              let y ← pure PUnit.unit
              __do_jp counts y) s₅ σ₅
        (fun co s' σ' => RyzOK col σ' s'.nv 231 co.Ry co.Rz ∧ 462 ≤ s'.nv ∧ EdgeOK col σ') := by
    intro Hp s₅ σ₅ hHp
    refine spec_bind (spec_nclauses (Q := fun _ s₆ σ₆ => s₆ = s₅ ∧ σ₆ = σ₅) (fun _ _ _ => ⟨rfl, rfl⟩))
      (fun nI s₆ σ₆ => ?_)
    dsimp only
    cases budget
    · simp only [Bool.false_eq_true, if_false]
      refine spec_pure_bind (spec_pure (fun hH _ _ => ?_))
      obtain ⟨hp, -, -, -, -, rfl, rfl⟩ := hH
      obtain ⟨hR, h462, hE, hle⟩ := hHp hp
      exact ⟨hR.mono hle, by omega, hE⟩
    · simp only [if_true]
      refine spec_bind (budBlock_spec col hsym D (hbud rfl) Ry Rz s₄.nv s₆ σ₆ _ (fun hH => ?_))
        (fun _ s₇ σ₇ => ?_)
      · obtain ⟨hp, -, -, -, -, rfl, rfl⟩ := hH
        obtain ⟨hR, h462, hE, hle⟩ := hHp hp
        exact ⟨hR, hE, hle, by omega⟩
      refine spec_bind (spec_nclauses (Q := fun _ s₈ σ₈ => s₈ = s₇ ∧ σ₈ = σ₇) (fun _ _ _ => ⟨rfl, rfl⟩))
        (fun nB s₈ σ₈ => ?_)
      refine spec_pure_bind (spec_pure (fun hH _ _ => ?_))
      obtain ⟨⟨⟨hp, -, -, -, -, rfl, rfl⟩, -, h67, ag67, -, -⟩, -, -, -, -, rfl, rfl⟩ := hH
      obtain ⟨hR, h462, hE, hle⟩ := hHp hp
      exact ⟨(hR.agree ag67 hle).mono (by omega), by omega, EdgeOK.agree hE ag67 (by omega)⟩
  cases channel
  · simp only [Bool.false_eq_true, if_false]
    refine spec_pure_bind (tail _ s₄ σ₄ (fun hH => ?_))
    obtain ⟨hR, h462, hE⟩ := key _ id hH
    exact ⟨hR, h462, hE, Nat.le_refl _⟩
  · simp only [if_true]
    refine spec_bind (chanBlock_spec col hsym D (hch rfl) Ry Rz s₄.nv s₄ σ₄ _ (fun hH => ?_))
      (fun _ s₅ σ₅ => tail _ s₅ σ₅ (fun hH => ?_))
    · obtain ⟨hR, h462, hE⟩ := key _ id hH
      exact ⟨hR, hE, Nat.le_refl _, h462⟩
    · obtain ⟨hp, -, h45, -, -, hs5, rfl⟩ := hH
      obtain ⟨hR, h462, hE⟩ := key _ id hp
      exact ⟨hR, h462, hE, by omega⟩

end SB.Rooted
#print axioms SB.Rooted.addCounting_spec
