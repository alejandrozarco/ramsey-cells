/-
# M3: the bidirectional counter `bidirCounter` (Enc.bidir_counter) is satisfied by its truthful
registers

`R(i,j)` (for `1 ≤ i ≤ m`, `1 ≤ j ≤ min i kmax`) is given the value "at least `j` of the first `i`
input literals are true". Every clause the counter emits is then satisfied, whatever the inputs.
-/
import RootedBridge.Spec

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

/-- Number of true literals among the first `i` of `xs` under `σ`. -/
def cnt (σ : Nat → Bool) (xs : Array Int) (i : Nat) : Nat :=
  ((xs.toList.take i).filter (fun l => lv σ l)).length

theorem cnt_zero (σ : Nat → Bool) (xs : Array Int) : cnt σ xs 0 = 0 := by simp [cnt]

theorem cnt_succ (σ : Nat → Bool) (xs : Array Int) {i : Nat} (hi : i < xs.size) :
    cnt σ xs (i + 1) = cnt σ xs i + (if lv σ xs[i] then 1 else 0) := by
  unfold cnt
  rw [List.take_add_one]
  have : xs.toList[i]? = some xs[i] := by simp [hi]
  rw [this]
  simp only [Option.toList, List.filter_append, List.length_append]
  by_cases h : lv σ xs[i] <;> simp [h]

theorem cnt_le (σ : Nat → Bool) (xs : Array Int) (i : Nat) : cnt σ xs i ≤ i := by
  unfold cnt
  calc _ ≤ (xs.toList.take i).length := List.length_filter_le _ _
    _ ≤ i := List.length_take_le _ _

theorem cnt_congr {σ σ' : Nat → Bool} {xs : Array Int} {n : Nat} (hag : Agree σ σ' n)
    (hx : ∀ l ∈ xs, l.natAbs ≤ n) (i : Nat) : cnt σ' xs i = cnt σ xs i := by
  unfold cnt
  congr 1
  apply List.filter_congr
  intro l hl
  have hl' : l ∈ xs := by
    have := List.mem_of_mem_take hl
    simpa using this
  exact lv_congr (hag _ (hx l hl'))

/-- The facts a counter carries: shape, freshness of its variables in `(lo, hi]`, truthful values. -/
structure CounterOK (σ : Nat → Bool) (xs : Array Int) (kmax : Nat) (R : Counter) (lo hi : Nat) :
    Prop where
  some_iff : ∀ i j, (R.get? i j).isSome ↔ (1 ≤ i ∧ i ≤ xs.size ∧ 1 ≤ j ∧ j ≤ min i kmax)
  range : ∀ i j v, R.get? i j = some v → lo < v ∧ v ≤ hi
  val : ∀ i j v, R.get? i j = some v → σ v = decide (j ≤ cnt σ xs i)

theorem CounterOK.agree {σ σ' : Nat → Bool} {xs : Array Int} {kmax : Nat} {R : Counter}
    {lo hi n : Nat} (h : CounterOK σ xs kmax R lo hi) (hag : Agree σ σ' n) (hhi : hi ≤ n)
    (hx : ∀ l ∈ xs, l.natAbs ≤ n) : CounterOK σ' xs kmax R lo hi :=
  ⟨h.some_iff, h.range, fun i j v hv => by
    rw [hag v (Nat.le_trans (h.range i j v hv).2 hhi), cnt_congr hag hx, h.val i j v hv]⟩

/-- Rows allocated so far: `rows[i][j]` is fresh above `lo` and carries `j+1 ≤ cnt σ₀ xs (i+1)`. -/
def RowsOK (σ₀ σ : Nat → Bool) (xs : Array Int) (kmax : Nat) (lo hi t : Nat)
    (rows : Array (Array Nat)) : Prop :=
  rows.size = t ∧ ∀ i (hi' : i < rows.size), rows[i].size = min (i + 1) kmax ∧
    ∀ j (hj : j < rows[i].size), lo < rows[i][j] ∧ rows[i][j] ≤ hi ∧
      σ rows[i][j] = decide (j + 1 ≤ cnt σ₀ xs (i + 1))

theorem RowsOK.upd {σ₀ σ : Nat → Bool} {xs : Array Int} {kmax lo hi t : Nat}
    {rows : Array (Array Nat)} (h : RowsOK σ₀ σ xs kmax lo hi t rows) (b : Bool) :
    RowsOK σ₀ (upd σ (hi + 1) b) xs kmax lo (hi + 1) t rows := by
  refine ⟨h.1, fun i hi' => ⟨(h.2 i hi').1, fun j hj => ?_⟩⟩
  obtain ⟨h1, h2, h3⟩ := (h.2 i hi').2 j hj
  refine ⟨h1, by omega, ?_⟩
  simp only [SB.Rooted.upd]
  rw [if_neg (by omega), h3]

theorem counterOK_of_rows {σ₀ σ : Nat → Bool} {xs : Array Int} {kmax lo hi : Nat}
    {rows : Array (Array Nat)} (h : RowsOK σ₀ σ xs kmax lo hi xs.size rows)
    (hc : ∀ i, cnt σ xs i = cnt σ₀ xs i) : CounterOK σ xs kmax ⟨rows⟩ lo hi := by
  obtain ⟨hsz, hrow⟩ := h
  have hget : ∀ i j, (⟨rows⟩ : Counter).get? i j =
      if h : 1 ≤ i ∧ i ≤ xs.size ∧ 1 ≤ j ∧ j ≤ min i kmax then
        some (rows[i - 1]!)[j - 1]!
      else none := by
    intro i j
    unfold Counter.get?
    dsimp only
    by_cases h : 1 ≤ i ∧ i ≤ xs.size ∧ 1 ≤ j ∧ j ≤ min i kmax
    · rw [dif_pos h, if_neg (by omega)]
      have hi : i - 1 < rows.size := by omega
      rw [Array.getElem?_eq_getElem hi]
      simp only
      have hj : j - 1 < rows[i - 1].size := by rw [(hrow (i - 1) hi).1]; omega
      rw [Array.getElem?_eq_getElem hj, getElem!_pos rows (i - 1) hi, getElem!_pos _ (j - 1) hj]
    · rw [dif_neg h]
      by_cases h0 : i = 0 ∨ j = 0
      · rw [if_pos h0]
      · rw [if_neg h0]
        by_cases hi : i - 1 < rows.size
        · rw [Array.getElem?_eq_getElem hi]
          simp only
          have : ¬ (j - 1 < rows[i - 1].size) := by rw [(hrow (i - 1) hi).1]; omega
          rw [Array.getElem?_eq_none (by omega)]
        · rw [Array.getElem?_eq_none (by omega)]
  have hent : ∀ i j (h : 1 ≤ i ∧ i ≤ xs.size ∧ 1 ≤ j ∧ j ≤ min i kmax),
      lo < (rows[i - 1]!)[j - 1]! ∧ (rows[i - 1]!)[j - 1]! ≤ hi ∧
        σ (rows[i - 1]!)[j - 1]! = decide (j ≤ cnt σ xs i) := by
    intro i j h
    have hi : i - 1 < rows.size := by omega
    have hj : j - 1 < rows[i - 1].size := by rw [(hrow (i - 1) hi).1]; omega
    rw [getElem!_pos rows (i - 1) hi, getElem!_pos _ (j - 1) hj]
    obtain ⟨h1, h2, h3⟩ := (hrow (i - 1) hi).2 (j - 1) hj
    refine ⟨h1, h2, ?_⟩
    rw [h3, hc]
    have : i - 1 + 1 = i := by omega
    rw [this]
    congr 1
    apply propext; omega
  refine ⟨fun i j => ?_, fun i j v hv => ?_, fun i j v hv => ?_⟩
  · rw [hget]; split <;> simp_all
  · rw [hget] at hv
    split at hv
    · next h => cases hv; exact ⟨(hent i j h).1, (hent i j h).2.1⟩
    · cases hv
  · rw [hget] at hv
    split at hv
    · next h => cases hv; exact (hent i j h).2.2
    · cases hv

theorem bidirCounter_spec (xs : Array Int) (kmax : Nat) (s : St) (σ : Nat → Bool) (H : Prop)
    (hx : H → ∀ l ∈ xs, l ≠ 0 ∧ l.natAbs ≤ s.nv) :
    Spec H (bidirCounter xs kmax) s σ (fun R s' σ' => CounterOK σ' xs kmax R s.nv s'.nv) := by
  unfold bidirCounter
  refine spec_bind (Q₁ := fun rows s' σ' => RowsOK σ σ' xs kmax s.nv s'.nv xs.size rows) ?_ ?_
  · refine spec_forIn_range (I := fun t rows s₁ σ₁ =>
        RowsOK σ σ₁ xs kmax s.nv s₁.nv t rows ∧ s.nv ≤ s₁.nv) 1 (xs.size + 1) _ _ ?_ ?_ ?_
    · intro _ _ _
      refine ⟨?_, Nat.le_refl _⟩
      simp [RowsOK]
    · intro i hi rows s₁ σ₁
      dsimp only
      refine spec_bind (Q₁ := fun row s₂ σ₂ => RowsOK σ σ₂ xs kmax s.nv s₂.nv i rows ∧
          s.nv ≤ s₂.nv ∧ row.size = min (1 + i) kmax ∧ ∀ j (hj : j < row.size),
            s.nv < row[j] ∧ row[j] ≤ s₂.nv ∧ σ₂ row[j] = decide (j + 1 ≤ cnt σ xs (i + 1))) ?_ ?_
      · refine spec_forIn_range (I := fun t row s₂ σ₂ => RowsOK σ σ₂ xs kmax s.nv s₂.nv i rows ∧
          s.nv ≤ s₂.nv ∧ row.size = t ∧ ∀ j (hj : j < row.size),
            s.nv < row[j] ∧ row[j] ≤ s₂.nv ∧ σ₂ row[j] = decide (j + 1 ≤ cnt σ xs (i + 1)))
          1 (min (1 + i) kmax + 1) _ _ ?_ ?_ ?_
        · intro hH _ _
          exact ⟨hH.2.1, hH.2.2, rfl, fun j hj => absurd hj (by simp)⟩
        · intro j hj row s₂ σ₂
          refine spec_bind (spec_fresh (decide (j + 1 ≤ cnt σ xs (i + 1)))
            (Q := fun v s₃ σ₃ => v = s₂.nv + 1 ∧ s₃.nv = s₂.nv + 1 ∧ σ₃ = upd σ₂ (s₂.nv + 1)
              (decide (j + 1 ≤ cnt σ xs (i + 1)))) (fun _ _ _ => ⟨rfl, rfl, rfl⟩)) ?_
          intro v s₃ σ₃
          refine spec_bind (spec_pure (Q := fun _ s₄ σ₄ => s₄ = s₃ ∧ σ₄ = σ₃)
            (fun _ _ _ => ⟨rfl, rfl⟩)) ?_
          intro _ s₄ σ₄
          refine spec_pure (fun hH _ _ => ?_)
          obtain ⟨⟨⟨hH0, hR, hle, hsz, hrow⟩, _, _, _, _, hv, hnv, hσ⟩, _, _, _, _, hs4, hσ4⟩ := hH
          rw [hs4, hσ4, hσ, hv]
          show RowsOK σ _ xs kmax s.nv _ i rows ∧ _
          rw [hnv]
          refine ⟨hR.upd _, by omega, by simp [hsz], fun j' hj' => ?_⟩
          simp only [Array.size_push] at hj'
          by_cases hj'' : j' < row.size
          · rw [Array.getElem_push_lt hj'']
            obtain ⟨h1, h2, h3⟩ := hrow j' hj''
            refine ⟨h1, by omega, ?_⟩
            simp only [SB.Rooted.upd]; rw [if_neg (by omega), h3]
          · have : j' = row.size := by omega
            subst this
            rw [Array.getElem_push_eq]
            refine ⟨by omega, Nat.le_refl _, ?_⟩
            simp only [SB.Rooted.upd, if_pos]
            rw [hsz]
        · intro row s₂ σ₂ _ _ h
          simpa using h
      · intro row s₂ σ₂
        refine spec_bind (spec_pure (Q := fun _ s₄ σ₄ => s₄ = s₂ ∧ σ₄ = σ₂)
            (fun _ _ _ => ⟨rfl, rfl⟩)) ?_
        intro _ s₄ σ₄
        refine spec_pure (fun hH _ _ => ?_)
        obtain ⟨⟨⟨hH0, hR, hle⟩, _, _, _, _, hR2, hle2, hsz, hrow⟩, _, _, _, _, hs4, hσ4⟩ := hH
        rw [hs4, hσ4]
        show RowsOK σ σ₂ xs kmax s.nv s₂.nv (i + 1) (rows.push row) ∧ s.nv ≤ s₂.nv
        refine ⟨⟨by simp [hR2.1], fun i' hi' => ?_⟩, hle2⟩
        simp only [Array.size_push] at hi'
        by_cases hi'' : i' < rows.size
        · rw [Array.getElem_push_lt hi'']
          exact hR2.2 i' hi''
        · have : i' = rows.size := by omega
          subst this
          rw [Array.getElem_push_eq]
          refine ⟨?_, fun j hj => ?_⟩
          · rw [hsz, hR2.1, Nat.add_comm]
          · rw [hR2.1]; exact hrow j hj
    · intro rows s' σ' _ _ h
      simpa using h.1
  · intro rows s₁ σ₁
    dsimp only
    refine spec_bind (Q₁ := fun _ s₂ σ₂ => s₂.nv = s₁.nv ∧ σ₂ = σ₁) ?_ ?_
    · refine spec_of_co_gated (F := CounterOK σ₁ xs kmax ⟨rows⟩ s.nv s₁.nv ∧
          ∀ l ∈ xs, l ≠ 0 ∧ l.natAbs ≤ s.nv) (post := fun _ => True) ?_ ?_
        (fun _ _ _ _ => ⟨rfl, rfl⟩)
      · apply co_forIn_range
        intro i hi1 hi2 _ s'
        dsimp only
        refine co_bind' ?_ (fun _ _ => co_pure trivial)
        apply co_forIn_range
        intro j hj1 hj2 _ s''
        dsimp only
        have hm : 1 ≤ i ∧ i ≤ xs.size ∧ 1 ≤ j ∧ j ≤ min i kmax := by omega
        cases h1 : (⟨rows⟩ : Counter).get? (i - 1) j <;>
        cases h2 : (⟨rows⟩ : Counter).get? (i - 1) (j - 1) <;>
        simp only [ Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some,
          Option.bind_none, Option.map_none, beq_self_eq_true, beq_iff_eq, if_true, if_false,
          Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false] <;>
        co_tac
        all_goals
          intro ⟨hC, hx⟩
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((hC.some_iff i j).mpr hm)
          have hvr := hC.range i j v hv
          have hvv := hC.val i j v hv
          have hxi : i - 1 < xs.size := by omega
          have hxx := hx xs[i - 1] (Array.getElem_mem hxi)
          try rw [getElem!_pos xs (i - 1) hxi]
          have hcnt : cnt σ₁ xs i = cnt σ₁ xs (i - 1) + (if lv σ₁ xs[i - 1] then 1 else 0) := by
            have := cnt_succ σ₁ xs hxi; rwa [Nat.sub_add_cancel hi1] at this
          simp only [hv, Option.getD_some]
          have hn1 := hC.some_iff (i - 1) j
          have hn2 := hC.some_iff (i - 1) (j - 1)
          rw [h1] at hn1
          rw [h2] at hn2
          have hv0 : 0 < v := by omega
          try (have hpr := hC.range _ _ _ h1; have hpv := hC.val _ _ _ h1;
               have hp0 := Nat.lt_of_le_of_lt (Nat.zero_le _) hpr.1)
          try (have hqr := hC.range _ _ _ h2; have hqv := hC.val _ _ _ h2;
               have hq0 := Nat.lt_of_le_of_lt (Nat.zero_le _) hqr.1)
          simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, false_iff,
            true_iff] at hn1 hn2
          refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
          · simp at hl
            rcases hl with rfl | rfl | rfl | rfl <;> (try simp) <;> omega
          · simp at hl
            rcases hl with rfl | rfl | rfl | rfl <;> omega
          · have hcl := cnt_le σ₁ xs (i - 1)
            simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at *
            cases hlx : lv σ₁ xs[i - 1] <;>
            simp [lv_neg_natCast, lv_natCast, lv_neg _ hxx.1, hlx, hvv, hcnt, *] <;>
            omega
      · intro hH
        obtain ⟨hH0, ⟨hv₁, hs₁⟩, hle₁, hag₁, he₁, hrows⟩ := hH
        have hx' : ∀ l ∈ xs, l.natAbs ≤ s.nv := fun l hl => (hx hH0 l hl).2
        exact ⟨counterOK_of_rows hrows (cnt_congr hag₁ hx'), hx hH0⟩
    · intro _ s₂ σ₂
      refine spec_pure (fun hH _ _ => ?_)
      obtain ⟨⟨hH0, ⟨hv₁, hs₁⟩, hle₁, hag₁, he₁, hrows⟩, _, _, _, _, hs2, hσ2⟩ := hH
      rw [hs2, hσ2]
      have hx' : ∀ l ∈ xs, l.natAbs ≤ s.nv := fun l hl => (hx hH0 l hl).2
      exact counterOK_of_rows hrows (cnt_congr hag₁ hx')

end SB.Rooted
namespace SB.Rooted
open LRATCatcher.Rooted

theorem mono_bidirCounter (xs : Array Int) (kmax : Nat) : Mono (bidirCounter xs kmax) :=
  fun s => (bidirCounter_spec xs kmax s (fun _ => false) False (fun h => h.elim)).1

/-- Use a spec whose hypothesis is only known along the path condition. -/
theorem spec_gate {α : Type} {H P : Prop} {p : EncM α} {s : St} {σ : Nat → Bool}
    {Q : α → St → (Nat → Bool) → Prop} (hm : Mono p) (h : P → Spec H p s σ Q) (hP : H → P) :
    Spec H p s σ Q :=
  ⟨hm s, fun hH => (h (hP hH)).2 hH⟩

end SB.Rooted

#print axioms SB.Rooted.bidirCounter_spec
