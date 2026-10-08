/-
# M3 framework: satisfaction of clause arrays and a Hoare-style calculus for `EncM`

Core Lean only (no Mathlib): this keeps the elaboration of the clause-family files fast.

* `LitSat σ l` : DIMACS literal `l` is true under `σ : ℕ → Bool` (variables 1-based); identical to
  `SB.BipBridge.LitSat` (the final bridge identifies them by `Iff.rfl`).
* `ClsSat σ cls` : every clause of the array is satisfied; `VLe cls nv` : every literal's variable
  is `≤ nv`.
* `Spec p s σ Q` : if running `p` from `s` ends without a recorded error, then `s` had no error,
  the variable count only grew, every clause of the final state mentions variables `≤` the final
  count, and some assignment `σ'` that AGREES with `σ` on `1..s.nv` satisfies every clause of the
  final state and `Q`. Fresh variables are given values by the prover (`spec_fresh b`), which is how
  the "truthful assignment" of each family is built without ever naming its variable numbers.
  Errors only accumulate, so an error-free final state certifies every intermediate step.
-/
import LRATCatcher.RootedEncoder

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

/-! ## Satisfaction -/

/-- Literal `l` is true under `σ`: `l ≠ 0` and `σ |l| = (0 < l)`. -/
def LitSat (σ : Nat → Bool) (l : Int) : Prop := l ≠ 0 ∧ σ l.natAbs = decide (0 < l)

/-- Some literal of the clause is true. -/
def ClauseSat (σ : Nat → Bool) (c : Array Int) : Prop := ∃ l ∈ c, LitSat σ l

/-- Every clause is satisfied. -/
def ClsSat (σ : Nat → Bool) (cls : Array (Array Int)) : Prop := ∀ c ∈ cls, ClauseSat σ c

/-- Every literal of every clause has its variable `≤ nv`. -/
def VLe (cls : Array (Array Int)) (nv : Nat) : Prop := ∀ c ∈ cls, ∀ l ∈ c, l.natAbs ≤ nv

/-- `σ'` agrees with `σ` on the variables `≤ n`. -/
def Agree (σ σ' : Nat → Bool) (n : Nat) : Prop := ∀ v, v ≤ n → σ' v = σ v

/-- Update at one variable. -/
def upd (σ : Nat → Bool) (v : Nat) (b : Bool) : Nat → Bool := fun x => if x = v then b else σ x

theorem agree_refl (σ : Nat → Bool) (n : Nat) : Agree σ σ n := fun _ _ => rfl

theorem agree_trans {σ₁ σ₂ σ₃ : Nat → Bool} {n m : Nat} (h₁ : Agree σ₁ σ₂ n) (h₂ : Agree σ₂ σ₃ m)
    (hnm : n ≤ m) : Agree σ₁ σ₃ n := fun v hv => by rw [h₂ v (Nat.le_trans hv hnm), h₁ v hv]

theorem agree_mono {σ σ' : Nat → Bool} {n m : Nat} (h : Agree σ σ' m) (hnm : n ≤ m) :
    Agree σ σ' n := fun v hv => h v (Nat.le_trans hv hnm)

theorem agree_upd (σ : Nat → Bool) (n : Nat) (b : Bool) : Agree σ (upd σ (n + 1) b) n := by
  intro v hv; simp only [upd]; rw [if_neg (by omega)]

theorem litSat_congr {σ σ' : Nat → Bool} {l : Int} (h : σ' l.natAbs = σ l.natAbs) :
    LitSat σ l → LitSat σ' l := fun ⟨h0, h1⟩ => ⟨h0, by rw [h, h1]⟩

theorem clauseSat_agree {σ σ' : Nat → Bool} {c : Array Int} {n : Nat} (hag : Agree σ σ' n)
    (hv : ∀ l ∈ c, l.natAbs ≤ n) : ClauseSat σ c → ClauseSat σ' c := by
  rintro ⟨l, hl, hs⟩
  exact ⟨l, hl, litSat_congr (hag _ (hv l hl)) hs⟩

theorem clsSat_agree {σ σ' : Nat → Bool} {cls : Array (Array Int)} {n : Nat} (hag : Agree σ σ' n)
    (hv : VLe cls n) : ClsSat σ cls → ClsSat σ' cls :=
  fun h c hc => clauseSat_agree hag (hv c hc) (h c hc)

theorem vle_mono {cls : Array (Array Int)} {n m : Nat} (h : VLe cls n) (hnm : n ≤ m) : VLe cls m :=
  fun c hc l hl => Nat.le_trans (h c hc l hl) hnm

theorem vle_push {cls : Array (Array Int)} {c : Array Int} {n : Nat} (h : VLe cls n)
    (hc : ∀ l ∈ c, l.natAbs ≤ n) : VLe (cls.push c) n := by
  intro c' hc' l hl
  rcases Array.mem_push.mp hc' with h' | rfl
  · exact h c' h' l hl
  · exact hc l hl

theorem clsSat_push {σ : Nat → Bool} {cls : Array (Array Int)} {c : Array Int} (h : ClsSat σ cls)
    (hc : ClauseSat σ c) : ClsSat σ (cls.push c) := by
  intro c' hc'
  rcases Array.mem_push.mp hc' with h' | rfl
  · exact h c' h'
  · exact hc

/-! ### Literal helpers -/

/-- The truth value of literal `l` under `σ` (the value of a nonzero literal). -/
def lv (σ : Nat → Bool) (l : Int) : Bool := if 0 < l then σ l.natAbs else !σ l.natAbs

theorem litSat_iff {σ : Nat → Bool} {l : Int} (h0 : l ≠ 0) : LitSat σ l ↔ lv σ l = true := by
  unfold LitSat lv
  by_cases hp : 0 < l
  · simp [hp, h0]
  · simp [hp, h0]

theorem lv_neg (σ : Nat → Bool) {l : Int} (h0 : l ≠ 0) : lv σ (-l) = !lv σ l := by
  unfold lv
  have : (-l).natAbs = l.natAbs := Int.natAbs_neg l
  rw [this]
  by_cases hp : 0 < l
  · have h1 : ¬ (0 < -l) := by omega
    rw [if_neg h1, if_pos hp]
  · have h1 : 0 < -l := by omega
    rw [if_pos h1, if_neg hp, Bool.not_not]

theorem lv_natCast (σ : Nat → Bool) {x : Nat} (hx : 0 < x) : lv σ (x : Int) = σ x := by
  unfold lv
  have : (0 : Int) < (x : Int) := by omega
  rw [if_pos this, Int.natAbs_natCast]

theorem lv_neg_natCast (σ : Nat → Bool) {x : Nat} (hx : 0 < x) : lv σ (-(x : Int)) = !σ x := by
  rw [lv_neg σ (by omega), lv_natCast σ hx]

theorem lv_congr {σ σ' : Nat → Bool} {l : Int} (h : σ' l.natAbs = σ l.natAbs) : lv σ' l = lv σ l := by
  unfold lv; rw [h]

/-- A clause is satisfied as soon as one nonzero literal of it has value `true`. -/
theorem clauseSat_of_lv {σ : Nat → Bool} {c : Array Int} {l : Int} (hl : l ∈ c) (h0 : l ≠ 0)
    (hv : lv σ l = true) : ClauseSat σ c := ⟨l, hl, (litSat_iff h0).mpr hv⟩

/-- The clause `c` is satisfied when its literals are all nonzero and not all false. -/
theorem clauseSat_of_exists {σ : Nat → Bool} {c : Array Int} (h0 : ∀ l ∈ c, l ≠ 0)
    (h : ∃ l ∈ c, lv σ l = true) : ClauseSat σ c := by
  obtain ⟨l, hl, hv⟩ := h
  exact clauseSat_of_lv hl (h0 l hl) hv

/-! ## The calculus

`Spec H p s σ Q` has two parts. The first is unconditional: if the run of `p` ends error-free then
it started error-free (errors only accumulate). The second is gated by a "path condition" `H`
(the facts the caller knows at this point) and by `Good s σ`: an error-free run ends in a state
satisfied by an extension `σ'` of `σ` (agreeing on `1..s.nv`) that also satisfies `Q`. Keeping the
first part free of `H` is what lets `spec_bind` conclude that an error-free end certifies every
intermediate state. -/

/-- The standing invariant of a state under an assignment. -/
def Good (s : St) (σ : Nat → Bool) : Prop := VLe s.cls s.nv ∧ ClsSat σ s.cls

/-- The specification (see above). -/
def Spec {α : Type} (H : Prop) (p : EncM α) (s : St) (σ : Nat → Bool)
    (Q : α → St → (Nat → Bool) → Prop) : Prop :=
  ((p.run s).2.errs = #[] → s.errs = #[]) ∧
  (H → Good s σ → (p.run s).2.errs = #[] →
    s.nv ≤ (p.run s).2.nv ∧ VLe (p.run s).2.cls (p.run s).2.nv ∧
    ∃ σ', Agree σ σ' s.nv ∧ ClsSat σ' (p.run s).2.cls ∧ Q (p.run s).1 (p.run s).2 σ')

/-- The path condition accumulated by `spec_bind`. -/
def After (H : Prop) (s : St) (σ : Nat → Bool) (s₁ : St) (σ₁ : Nat → Bool) (Q₁ : Prop) : Prop :=
  H ∧ Good s₁ σ₁ ∧ s.nv ≤ s₁.nv ∧ Agree σ σ₁ s.nv ∧ s₁.errs = #[] ∧ Q₁

section Rules
variable {α β : Type} {H : Prop} {s : St} {σ : Nat → Bool}

theorem spec_bind {p : EncM α} {f : α → EncM β}
    {Q₁ : α → St → (Nat → Bool) → Prop} {Q : β → St → (Nat → Bool) → Prop}
    (h₁ : Spec H p s σ Q₁)
    (h₂ : ∀ x s₁ σ₁, Spec (After H s σ s₁ σ₁ (Q₁ x s₁ σ₁)) (f x) s₁ σ₁ Q) :
    Spec H (p >>= f) s σ Q := by
  have hrun : (p >>= f).run s = (f (p.run s).1).run (p.run s).2 := rfl
  refine ⟨fun he => ?_, fun hH hg he => ?_⟩
  · rw [hrun] at he
    exact h₁.1 ((h₂ _ _ σ).1 he)
  · rw [hrun] at he ⊢
    have he₁ := (h₂ _ _ σ).1 he
    obtain ⟨hnv₁, hv₁, σ₁, hag₁, hs₁, hq₁⟩ := h₁.2 hH hg he₁
    obtain ⟨hnv₂, hv₂, σ₂, hag₂, hs₂, hq₂⟩ :=
      (h₂ _ _ σ₁).2 ⟨hH, ⟨hv₁, hs₁⟩, hnv₁, hag₁, he₁, hq₁⟩ ⟨hv₁, hs₁⟩ he
    exact ⟨Nat.le_trans hnv₁ hnv₂, hv₂, σ₂, agree_trans hag₁ hag₂ hnv₁, hs₂, hq₂⟩

theorem spec_pure {x : α} {Q : α → St → (Nat → Bool) → Prop}
    (h : H → Good s σ → s.errs = #[] → Q x s σ) : Spec H (pure x) s σ Q :=
  ⟨fun he => he, fun hH hg he => ⟨Nat.le_refl _, hg.1, σ, agree_refl σ _, hg.2, h hH hg he⟩⟩

theorem spec_conseq {p : EncM α} {Q Q' : α → St → (Nat → Bool) → Prop} {H' : Prop}
    (h : Spec H' p s σ Q) (hH : H → H')
    (hq : ∀ x s' σ', H → Agree σ σ' s.nv → s.nv ≤ s'.nv → Good s' σ' → s'.errs = #[] →
      Q x s' σ' → Q' x s' σ') :
    Spec H p s σ Q' := by
  refine ⟨h.1, fun hH' hg he => ?_⟩
  obtain ⟨hnv, hv, σ', hag, hs, hq'⟩ := h.2 (hH hH') hg he
  exact ⟨hnv, hv, σ', hag, hs, hq _ _ _ hH' hag hnv ⟨hv, hs⟩ he hq'⟩

theorem spec_add {c : Array Int} {Q : Unit → St → (Nat → Bool) → Prop}
    (h : H → Good s σ → s.errs = #[] →
      (∀ l ∈ c, l.natAbs ≤ s.nv) ∧ ClauseSat σ c ∧ Q () { s with cls := s.cls.push c } σ) :
    Spec H (add c) s σ Q := by
  refine ⟨fun he => he, fun hH hg he => ?_⟩
  obtain ⟨hv, hc, hq⟩ := h hH hg he
  exact ⟨Nat.le_refl _, vle_push hg.1 hv, σ, agree_refl σ _, clsSat_push hg.2 hc, hq⟩

/-- `fresh` with the value `b` chosen for the new variable. -/
theorem spec_fresh (b : Bool) {Q : Nat → St → (Nat → Bool) → Prop}
    (h : H → Good s σ → s.errs = #[] →
      Q (s.nv + 1) { s with nv := s.nv + 1 } (upd σ (s.nv + 1) b)) :
    Spec H fresh s σ Q := by
  refine ⟨fun he => he, fun hH hg he => ?_⟩
  refine ⟨Nat.le_succ _, vle_mono hg.1 (Nat.le_succ _), upd σ (s.nv + 1) b, agree_upd σ s.nv b,
    clsSat_agree (agree_upd σ s.nv b) hg.1 hg.2, h hH hg he⟩

theorem spec_fail {msg : String} {Q : Unit → St → (Nat → Bool) → Prop} :
    Spec H (fail msg) s σ Q := by
  refine ⟨fun he => ?_, fun _ _ he => ?_⟩ <;>
  · exfalso
    have : (fail msg).run s = ((), { s with errs := s.errs.push msg }) := rfl
    rw [this] at he
    have h2 := congrArg Array.size he
    simp at h2

theorem spec_get {Q : St → St → (Nat → Bool) → Prop}
    (h : H → Good s σ → s.errs = #[] → Q s s σ) : Spec H get s σ Q :=
  ⟨fun he => he, fun hH hg he => ⟨Nat.le_refl _, hg.1, σ, agree_refl σ _, hg.2, h hH hg he⟩⟩

theorem spec_nclauses {Q : Nat → St → (Nat → Bool) → Prop}
    (h : H → Good s σ → s.errs = #[] → Q s.cls.size s σ) : Spec H nclauses s σ Q :=
  ⟨fun he => he, fun hH hg he => ⟨Nat.le_refl _, hg.1, σ, agree_refl σ _, hg.2, h hH hg he⟩⟩

/-- Weakening the path condition. -/
theorem spec_weaken {p : EncM α} {Q : α → St → (Nat → Bool) → Prop} {H' : Prop}
    (h : Spec H' p s σ Q) (hH : H → H') : Spec H p s σ Q :=
  spec_conseq h hH (fun _ _ _ _ _ _ _ _ hq => hq)

/-- Case split on the path condition: to prove a spec it suffices to prove its second part under
`H` (the first part, monotonicity, must still be supplied). -/
theorem spec_of_imp {p : EncM α} {Q : α → St → (Nat → Bool) → Prop}
    (hm : (p.run s).2.errs = #[] → s.errs = #[]) (h : H → Spec True p s σ Q) : Spec H p s σ Q :=
  ⟨hm, fun hH hg he => (h hH).2 trivial hg he⟩

end Rules

/-! ## Loops -/

section Loops
variable {γ β : Type} {H : Prop}

/-- The post-state of one loop body run, by step kind. -/
def StepPost (I : Nat → β → St → (Nat → Bool) → Prop) (i len : Nat) :
    ForInStep β → St → (Nat → Bool) → Prop
  | .yield b, s, σ => I (i + 1) b s σ
  | .done b, s, σ => I len b s σ

theorem spec_forIn_aux (xs : List γ) (f : γ → β → EncM (ForInStep β))
    (I : Nat → β → St → (Nat → Bool) → Prop)
    (hstep : ∀ i (hi : i < xs.length) b s σ,
      Spec (H ∧ I i b s σ) (f xs[i] b) s σ (StepPost I i xs.length)) :
    ∀ n j b s σ, xs.length - j = n → j ≤ xs.length →
      Spec (H ∧ I j b s σ) (forIn (xs.drop j) b f) s σ (fun b' s' σ' => I xs.length b' s' σ') := by
  intro n
  induction n with
  | zero =>
    intro j b s σ hn hj
    have hj' : j = xs.length := by omega
    subst hj'
    rw [List.drop_length, List.forIn_nil]
    exact spec_pure (fun hH _ _ => hH.2)
  | succ n ih =>
    intro j b s σ hn hj
    have hjl : j < xs.length := by omega
    rw [List.drop_eq_getElem_cons hjl, List.forIn_cons]
    refine spec_bind (hstep j hjl b s σ) ?_
    intro r s₁ σ₁
    cases r with
    | done b' => exact spec_pure (fun hH _ _ => hH.2.2.2.2.2)
    | yield b' =>
      exact spec_weaken (ih (j + 1) b' s₁ σ₁ (by omega) (by omega))
        (fun hH => ⟨hH.1.1, hH.2.2.2.2.2⟩)

/-- **Loop rule** for `for x in xs` (a `List`), with an invariant indexed by the number of
processed elements. A `done` (break) step must establish the final invariant directly. -/
theorem spec_forIn {s : St} {σ : Nat → Bool} (xs : List γ) (b₀ : β)
    (f : γ → β → EncM (ForInStep β)) (I : Nat → β → St → (Nat → Bool) → Prop)
    {Q : β → St → (Nat → Bool) → Prop}
    (h0 : H → Good s σ → s.errs = #[] → I 0 b₀ s σ)
    (hstep : ∀ i (hi : i < xs.length) b s σ,
      Spec (H ∧ I i b s σ) (f xs[i] b) s σ (StepPost I i xs.length))
    (hQ : ∀ b s' σ', H → Agree σ σ' s.nv → I xs.length b s' σ' → Q b s' σ') :
    Spec H (forIn xs b₀ f) s σ Q := by
  have h := spec_forIn_aux (H := H) xs f I hstep (xs.length - 0) 0 b₀ s σ rfl (Nat.zero_le _)
  rw [List.drop_zero] at h
  refine ⟨h.1, fun hH hg he => ?_⟩
  obtain ⟨hnv, hv, σ', hag, hs, hq⟩ := h.2 ⟨hH, h0 hH hg (h.1 he)⟩ hg he
  exact ⟨hnv, hv, σ', hag, hs, hQ _ _ _ hH hag hq⟩

/-- Loop rule for `for x in xs` over an `Array`. -/
theorem spec_forIn_array {s : St} {σ : Nat → Bool} (xs : Array γ) (b₀ : β)
    (f : γ → β → EncM (ForInStep β)) (I : Nat → β → St → (Nat → Bool) → Prop)
    {Q : β → St → (Nat → Bool) → Prop}
    (h0 : H → Good s σ → s.errs = #[] → I 0 b₀ s σ)
    (hstep : ∀ i (hi : i < xs.size) b s σ,
      Spec (H ∧ I i b s σ) (f xs[i] b) s σ (StepPost I i xs.size))
    (hQ : ∀ b s' σ', H → Agree σ σ' s.nv → I xs.size b s' σ' → Q b s' σ') :
    Spec H (forIn xs b₀ f) s σ Q := by
  rw [← Array.forIn_toList]
  exact spec_forIn xs.toList b₀ f I h0
    (fun i hi b s σ => by simpa using hstep i (by simpa using hi) b s σ) (by simpa using hQ)

/-- Loop rule for `for i in [a:b]` (`Std.Legacy.Range`, step 1). -/
theorem spec_forIn_range {s : St} {σ : Nat → Bool} (lo hi : Nat) (b₀ : β)
    (f : Nat → β → EncM (ForInStep β)) (I : Nat → β → St → (Nat → Bool) → Prop)
    {Q : β → St → (Nat → Bool) → Prop}
    (h0 : H → Good s σ → s.errs = #[] → I 0 b₀ s σ)
    (hstep : ∀ i (hil : i < hi - lo) b s σ,
      Spec (H ∧ I i b s σ) (f (lo + i) b) s σ (StepPost I i (hi - lo)))
    (hQ : ∀ b s' σ', H → Agree σ σ' s.nv → I (hi - lo) b s' σ' → Q b s' σ') :
    Spec H (forIn [lo:hi] b₀ f) s σ Q := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsz : ([lo:hi] : Std.Legacy.Range).size = hi - lo := by
    simp [Std.Legacy.Range.size]
  have hst : ([lo:hi] : Std.Legacy.Range).step = 1 := rfl
  have hs0 : ([lo:hi] : Std.Legacy.Range).start = lo := rfl
  rw [hsz, hst, hs0]
  refine spec_forIn _ b₀ f I h0 (fun i hi' b s σ => ?_) (by simpa using hQ)
  have hl : (List.range' lo (hi - lo) 1).length = hi - lo := List.length_range'
  have hg : (List.range' lo (hi - lo) 1)[i] = lo + i := by
    rw [List.getElem_range']; omega
  simp only [hl] at hi' ⊢
  rw [hg]
  exact hstep i hi' b s σ

end Loops

/-! ## Clause-only programs

Bodies that only `add` clauses (no `fresh`, no `fail`, no state reads) are handled by a lighter
calculus: `ClauseOnly p s ok post` says that the run of `p` from `s` appends some clauses, each
satisfying `ok`, and returns a value satisfying `post`. -/

/-- See above. -/
def ClauseOnly {α : Type} (p : EncM α) (s : St) (ok : Array Int → Prop) (post : α → Prop) : Prop :=
  ∃ x cs, p.run s = (x, { s with cls := s.cls ++ cs }) ∧ (∀ c ∈ cs, ok c) ∧ post x

section ClauseOnlyRules
variable {α β : Type} {s : St} {ok : Array Int → Prop}

theorem co_pure {x : α} {post : α → Prop} (h : post x) : ClauseOnly (pure x) s ok post :=
  ⟨x, #[], by cases s; simp; rfl, by simp, h⟩

theorem co_add {c : Array Int} {post : Unit → Prop} (h : ok c) (hp : post ()) :
    ClauseOnly (add c) s ok post :=
  ⟨(), #[c], by cases s; simp [add, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]; rfl,
    by simpa using h, hp⟩

theorem co_bind {p : EncM α} {f : α → EncM β} {P₁ : α → Prop} {post : β → Prop}
    (h₁ : ClauseOnly p s ok P₁) (h₂ : ∀ x s', P₁ x → ClauseOnly (f x) s' ok post) :
    ClauseOnly (p >>= f) s ok post := by
  obtain ⟨x, cs, hrun, hok, hP⟩ := h₁
  obtain ⟨y, cs', hrun', hok', hP'⟩ := h₂ x { s with cls := s.cls ++ cs } hP
  refine ⟨y, cs ++ cs', ?_, ?_, hP'⟩
  · have : (p >>= f).run s = (f (p.run s).1).run (p.run s).2 := rfl
    rw [this, hrun]
    simp only at hrun' ⊢
    rw [hrun', Array.append_assoc]
  · intro c hc
    rcases Array.mem_append.mp hc with h | h
    · exact hok c h
    · exact hok' c h

theorem co_bind' {p : EncM α} {f : α → EncM β} {post : β → Prop}
    (h₁ : ClauseOnly p s ok (fun _ => True)) (h₂ : ∀ x s', ClauseOnly (f x) s' ok post) :
    ClauseOnly (p >>= f) s ok post :=
  co_bind h₁ (fun x s' _ => h₂ x s')

theorem co_add' {c : Array Int} (h : ok c) : ClauseOnly (add c) s ok (fun _ => True) :=
  co_add h trivial

theorem co_conseq {p : EncM α} {P P' : α → Prop} (h : ClauseOnly p s ok P) (hP : ∀ x, P x → P' x) :
    ClauseOnly p s ok P' := by
  obtain ⟨x, cs, hrun, hok, hp⟩ := h
  exact ⟨x, cs, hrun, hok, hP x hp⟩

/-- From a clause-only run to a `Spec`, with `σ` unchanged. -/
theorem spec_of_co {H : Prop} {σ : Nat → Bool} {p : EncM α} {post : α → Prop}
    {Q : α → St → (Nat → Bool) → Prop}
    (h : ClauseOnly p s (fun c => (∀ l ∈ c, l.natAbs ≤ s.nv) ∧ ClauseSat σ c) post)
    (hQ : ∀ x cs, H → post x → Q x { s with cls := s.cls ++ cs } σ) : Spec H p s σ Q := by
  obtain ⟨x, cs, hrun, hok, hp⟩ := h
  refine ⟨fun he => ?_, fun hH hg he => ?_⟩
  · rw [hrun] at he; exact he
  · rw [hrun]
    refine ⟨Nat.le_refl _, ?_, σ, agree_refl σ _, ?_, hQ x cs hH hp⟩
    · intro c hc l hl
      rcases Array.mem_append.mp hc with h' | h'
      · exact hg.1 c h' l hl
      · exact (hok c h').1 l hl
    · intro c hc
      rcases Array.mem_append.mp hc with h' | h'
      · exact hg.2 c h'
      · exact (hok c h').2

/-- `spec_of_co` with the clause obligations gated by a fact `F` that the path condition implies:
the run equation (hence error monotonicity) needs no facts. -/
theorem spec_of_co_gated {H F : Prop} {σ : Nat → Bool} {p : EncM α} {post : α → Prop}
    {Q : α → St → (Nat → Bool) → Prop}
    (h : ClauseOnly p s (fun c => F → (∀ l ∈ c, l.natAbs ≤ s.nv) ∧ ClauseSat σ c) post)
    (hF : H → F) (hQ : ∀ x cs, H → post x → Q x { s with cls := s.cls ++ cs } σ) :
    Spec H p s σ Q := by
  obtain ⟨x, cs, hrun, hok, hp⟩ := h
  refine ⟨fun he => ?_, fun hH hg he => ?_⟩
  · rw [hrun] at he; exact he
  · rw [hrun]
    refine ⟨Nat.le_refl _, ?_, σ, agree_refl σ _, ?_, hQ x cs hH hp⟩
    · intro c hc l hl
      rcases Array.mem_append.mp hc with h' | h'
      · exact hg.1 c h' l hl
      · exact (hok c h' (hF hH)).1 l hl
    · intro c hc
      rcases Array.mem_append.mp hc with h' | h'
      · exact hg.2 c h'
      · exact (hok c h' (hF hH)).2

theorem co_forIn {γ β : Type} (xs : List γ) (b : β) (f : γ → β → EncM (ForInStep β))
    (hf : ∀ x ∈ xs, ∀ b s', ClauseOnly (f x b) s' ok (fun _ => True)) :
    ClauseOnly (forIn xs b f) s ok (fun _ => True) := by
  induction xs generalizing b s with
  | nil => rw [List.forIn_nil]; exact co_pure trivial
  | cons x rest ih =>
    rw [List.forIn_cons]
    refine co_bind' (hf x List.mem_cons_self b s) (fun r s' => ?_)
    cases r with
    | done b' => exact co_pure trivial
    | yield b' => exact ih b' (fun y hy b s => hf y (List.mem_cons_of_mem _ hy) b s)

theorem co_forIn_range {β : Type} (lo hi : Nat) (b : β) (f : Nat → β → EncM (ForInStep β))
    (hf : ∀ x, lo ≤ x → x < hi → ∀ b s', ClauseOnly (f x b) s' ok (fun _ => True)) :
    ClauseOnly (forIn [lo:hi] b f) s ok (fun _ => True) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply co_forIn
  intro x hx
  have hst : ([lo:hi] : Std.Legacy.Range).step = 1 := rfl
  have hs0 : ([lo:hi] : Std.Legacy.Range).start = lo := rfl
  have hsz : ([lo:hi] : Std.Legacy.Range).size = hi - lo := by simp [Std.Legacy.Range.size]
  rw [hst, hs0, hsz, List.mem_range'_1] at hx
  exact hf x hx.1 (by omega)

theorem co_forIn_array {γ β : Type} (xs : Array γ) (b : β) (f : γ → β → EncM (ForInStep β))
    (hf : ∀ x ∈ xs, ∀ b s', ClauseOnly (f x b) s' ok (fun _ => True)) :
    ClauseOnly (forIn xs b f) s ok (fun _ => True) := by
  rw [← Array.forIn_toList]
  exact co_forIn _ b f (fun x hx => hf x (by simpa using hx))

end ClauseOnlyRules

/-- Drive a clause-only program to its `ok` obligations. -/
macro "co_tac" : tactic => `(tactic| repeat' (first
  | exact co_pure trivial
  | exact co_pure rfl
  | refine co_bind' ?_ (fun _ _ => ?_)
  | refine co_add' ?_
  | refine co_forIn_range _ _ _ _ (fun _ _ _ _ _ => ?_)
  | (show ClauseOnly _ _ _ _; split)))

/-- `co_tac` without entering loops (loop goals are left for named `intro`s). -/
macro "co_step" : tactic => `(tactic| repeat' (first
  | exact co_pure trivial
  | exact co_pure rfl
  | refine co_bind' ?_ (fun _ _ => ?_)
  | refine co_add' ?_
  | (show ClauseOnly _ _ _ _; split)))

theorem litSat_posNat {σ : Nat → Bool} {v : Nat} (hv : 0 < v) : LitSat σ (v : Int) ↔ σ v = true := by
  unfold LitSat
  have h1 : (v : Int) ≠ 0 := by omega
  have h2 : (0 : Int) < (v : Int) := by omega
  simp only [Int.natAbs_natCast, h2, decide_true]
  exact ⟨fun h => h.2, fun h => ⟨h1, h⟩⟩

theorem litSat_negNat {σ : Nat → Bool} {v : Nat} (hv : 0 < v) :
    LitSat σ (-(v : Int)) ↔ σ v = false := by
  unfold LitSat
  have h1 : -(v : Int) ≠ 0 := by omega
  have h2 : ¬ (0 : Int) < -(v : Int) := by omega
  simp only [Int.natAbs_neg, Int.natAbs_natCast, h2, decide_false]
  exact ⟨fun h => h.2, fun h => ⟨h1, h⟩⟩

theorem litSat_neg {σ : Nat → Bool} {l : Int} : LitSat σ (-l) ↔ l ≠ 0 ∧ lv σ l = false := by
  by_cases h0 : l = 0
  · subst h0; simp [LitSat]
  · have hn : -l ≠ 0 := by omega
    rw [litSat_iff hn, lv_neg σ h0]
    simp [h0]

theorem litSat_iff_lv {σ : Nat → Bool} {l : Int} : LitSat σ l ↔ l ≠ 0 ∧ lv σ l = true := by
  by_cases h0 : l = 0
  · subst h0; simp [LitSat]
  · rw [litSat_iff h0]; simp [h0]

theorem clauseSat_iff {σ : Nat → Bool} {c : Array Int} : ClauseSat σ c ↔ ∃ l ∈ c.toList, LitSat σ l := by
  unfold ClauseSat; simp

theorem clauseSat_of_any {σ : Nat → Bool} {c : Array Int} (h0 : ∀ l ∈ c, l ≠ 0)
    (h : c.toList.any (lv σ) = true) : ClauseSat σ c := by
  rw [List.any_eq_true] at h
  obtain ⟨l, hl, hv⟩ := h
  have hl' : l ∈ c := by simpa using hl
  exact clauseSat_of_lv hl' (h0 l hl') hv

/-! ## Error monotonicity, for the code after a `fail`

`Mono p`: an error-free end of `p` certifies an error-free start. Every program of the encoder has
it (errors are only ever pushed); `mono_tac` proves it structurally. It is needed only where a
`fail` is followed by more code: `spec_fail_bind`. -/

/-- See above. -/
def Mono {α : Type} (p : EncM α) : Prop := ∀ s : St, (p.run s).2.errs = #[] → s.errs = #[]

section MonoRules
variable {α β γ : Type}

theorem mono_pure {x : α} : Mono (pure x : EncM α) := fun _ h => h
theorem mono_add {c : Array Int} : Mono (add c) := fun _ h => h
theorem mono_fresh : Mono fresh := fun _ h => h
theorem mono_get : Mono (get : EncM St) := fun _ h => h
theorem mono_nclauses : Mono nclauses := fun _ h => h
theorem mono_fail {msg : String} : Mono (fail msg) := fun s h => by
  exfalso
  have : (fail msg).run s = ((), { s with errs := s.errs.push msg }) := rfl
  rw [this] at h
  have h2 := congrArg Array.size h
  simp at h2

theorem mono_bind {p : EncM α} {f : α → EncM β} (hp : Mono p) (hf : ∀ x, Mono (f x)) :
    Mono (p >>= f) := fun s h => by
  have : (p >>= f).run s = (f (p.run s).1).run (p.run s).2 := rfl
  rw [this] at h
  exact hp s (hf _ _ h)

theorem mono_forIn {xs : List γ} {b : β} {f : γ → β → EncM (ForInStep β)}
    (hf : ∀ x b, Mono (f x b)) : Mono (forIn xs b f) := by
  induction xs generalizing b with
  | nil => rw [List.forIn_nil]; exact mono_pure
  | cons x rest ih =>
    rw [List.forIn_cons]
    refine mono_bind (hf x b) (fun r => ?_)
    cases r with
    | done b' => exact mono_pure
    | yield b' => exact ih

theorem mono_forIn_range {lo hi : Nat} {b : β} {f : Nat → β → EncM (ForInStep β)}
    (hf : ∀ x b, Mono (f x b)) : Mono (forIn [lo:hi] b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']; exact mono_forIn hf

theorem mono_forIn_array {xs : Array γ} {b : β} {f : γ → β → EncM (ForInStep β)}
    (hf : ∀ x b, Mono (f x b)) : Mono (forIn xs b f) := by
  rw [← Array.forIn_toList]; exact mono_forIn hf

theorem mono_counterAt {R : Counter} {i j : Nat} {ctx : String} : Mono (R.at i j ctx) := by
  unfold Counter.at
  split
  · exact mono_pure
  · exact mono_bind mono_fail (fun _ => mono_pure)

/-- A `fail` followed by anything: vacuous, given the continuation's monotonicity. -/
theorem spec_fail_bind {H : Prop} {s : St} {σ : Nat → Bool} {msg : String} {f : Unit → EncM β}
    {Q : β → St → (Nat → Bool) → Prop} (hf : ∀ x, Mono (f x)) : Spec H (fail msg >>= f) s σ Q := by
  have hm : Mono (fail msg >>= f) := mono_bind mono_fail hf
  have hrun : (fail msg >>= f).run s = (f ()).run { s with errs := s.errs.push msg } := rfl
  refine ⟨hm s, fun _ _ he => ?_⟩
  exfalso
  rw [hrun] at he
  have h2 := congrArg Array.size (hf () _ he)
  simp at h2

end MonoRules

/-- Prove `Mono` of a program structurally. -/
macro "mono_tac" : tactic => `(tactic| repeat' (first
  | exact mono_pure
  | exact mono_add
  | exact mono_fresh
  | exact mono_get
  | exact mono_nclauses
  | exact mono_fail
  | exact mono_counterAt
  | refine mono_bind ?_ (fun _ => ?_)
  | refine mono_forIn_range (fun _ _ => ?_)
  | refine mono_forIn_array (fun _ _ => ?_)
  | refine mono_forIn (fun _ _ => ?_)
  | (show Mono _; split)
  | (show Mono _; dsimp only)))

end SB.Rooted
