/-
# M3: the base layer (`gen_ramsey.build`, `buildBase`) and its edge-only variant

* edge clauses: exactly one colour per edge (`[x₁, x₂]`, `[-x₁, -x₂]`): satisfied by any colouring;
* the codegree layer, for colour `c ∈ {1 (red, K2x8), 2 (blue, K2x5)}` and every pair `S = {u,v}`:
  `y_w ⇐ (u,w) and (v,w) both have colour c` (`y_w` truthful: the conjunction), and a one-directional
  Sinz counter `R(i,j) = [at least j of y_1..y_i]` (`i = 1..m-1`, `j = 1..k`) whose last clauses
  forbid `k+1` true `y`s. Satisfied when the pair has at most `k = t - 1` common neighbours in colour
  `c`, i.e. by every colouring with no red `K_{2,8}` (`k = 7`) and no blue `K_{2,5}` (`k = 4`).
-/
import RootedBridge.Lex
import RootedBridge.Counter

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

/-- The common colour-`c` neighbours of the vertex list `S` (outside `S`), among `1..t`. -/
def commonC (col : Nat → Nat → Bool) (c : Nat) (S : List Nat) (t : Nat) : List Nat :=
  (List.range' 1 t).filter (fun w => !S.contains w && S.all (fun x => colV col x w c))

/-- The codegree caps in the base layer's form: every pair `u < v` has at most `k` common
neighbours in colour `c`. -/
def CapC (col : Nat → Nat → Bool) (c k : Nat) : Prop :=
  ∀ u v, 1 ≤ u → u < v → v ≤ 22 → (commonC col c [u, v] 22).length ≤ k

theorem combos_sub : ∀ (k : Nat) (l : List Nat), ∀ S ∈ combos k l, S.Sublist l ∧ S.length = k
  | 0, l, S, h => by
    unfold combos at h; simp at h; subst h; exact ⟨List.nil_sublist _, rfl⟩
  | k + 1, [], S, h => by unfold combos at h; simp at h
  | k + 1, x :: xs, S, h => by
    unfold combos at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨S', hS', rfl⟩ := List.mem_map.mp h
      obtain ⟨h1, h2⟩ := combos_sub k xs S' hS'
      exact ⟨h1.cons_cons x, by simp [h2]⟩
    · obtain ⟨h1, h2⟩ := combos_sub (k + 1) xs S h
      exact ⟨h1.cons x, h2⟩

theorem combos_two_mem {S : List Nat} (hS : S ∈ combos 2 (List.range' 1 22)) :
    ∃ u v, S = [u, v] ∧ 1 ≤ u ∧ u < v ∧ v ≤ 22 := by
  obtain ⟨hsub, hlen⟩ := combos_sub 2 _ S hS
  match S, hlen with
  | [u, v], _ =>
    have hp := (List.pairwise_lt_range' (s := 1) (n := 22)).sublist hsub
    have hu : u ∈ List.range' 1 22 := hsub.subset (by simp)
    have hv : v ∈ List.range' 1 22 := hsub.subset (by simp)
    simp only [List.mem_range'_1] at hu hv
    simp at hp
    exact ⟨u, v, rfl, by omega, hp, by omega⟩

theorem cnt_mono (σ : Nat → Bool) (xs : Array Int) {i j : Nat} (h : i ≤ j) :
    cnt σ xs i ≤ cnt σ xs j := by
  unfold cnt
  have : xs.toList.take i = (xs.toList.take j).take i := by
    rw [List.take_take, Nat.min_eq_left h]
  rw [this]
  exact (List.take_sublist _ _).filter _ |>.length_le

theorem edgeLayer_co (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) (σ : Nat → Bool)
    (s : St) :
    ClauseOnly (forIn (edgesOf 22) PUnit.unit fun e r_1 => do
      add (List.map (fun c => varE 22 2 e.fst e.snd c) (List.range' 1 2)).toArray
      forIn [1:2 + 1] PUnit.unit fun c1 r_2 => do
          forIn [c1 + 1:2 + 1] PUnit.unit fun c2 r_3 => do
              add #[-varE 22 2 e.fst e.snd c1, -varE 22 2 e.fst e.snd c2]
              pure (ForInStep.yield PUnit.unit)
          pure PUnit.unit
          pure (ForInStep.yield PUnit.unit)
      pure PUnit.unit
      pure (ForInStep.yield PUnit.unit)) s
      (fun c => EdgeOK col σ ∧ 462 ≤ s.nv → (∀ l ∈ c, l.natAbs ≤ s.nv) ∧ ClauseSat σ c)
      (fun _ => True) := by
  apply co_forIn_array
  intro e he _ s'
  obtain ⟨he1, he2, he3⟩ := mem_edgesOf he
  have hv : VPair e.1 e.2 := ⟨he1, by omega, by omega, he3, by omega⟩
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range'_succ,
    List.range'_zero, List.forIn_cons, List.forIn_nil, List.map_cons, List.map_nil,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv]
  co_tac
  all_goals
    intro ⟨hE, hs⟩
    have b1 := varE_bounds hv (Or.inl rfl)
    have b2 := varE_bounds hv (Or.inr rfl)
    have l1 := lv_varE hsym hE hv (Or.inl rfl)
    have l2 := lv_varE hsym hE hv (Or.inr rfl)
    refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
    · simp at hl; rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_neg]) <;> omega
    · simp at hl; rcases hl with rfl | rfl <;> omega
    · simp [lv_neg _ b1.2.2, lv_neg _ b2.2.2, l1, l2, colV]

theorem commonC_succ (col : Nat → Nat → Bool) (c : Nat) (S : List Nat) (t : Nat) :
    commonC col c S (t + 1) = commonC col c S t ++
      (if (!S.contains (t + 1) && S.all (fun x => colV col x (t + 1) c)) then [t + 1] else []) := by
  unfold commonC
  rw [List.range'_1_concat, List.filter_append]
  simp only [List.filter_cons, List.filter_nil]
  split <;> simp_all [Nat.add_comm]

theorem filter_succ (S : List Nat) (t : Nat) :
    ((List.range' 1 (t + 1)).filter (fun w => !S.contains w)).length =
      ((List.range' 1 t).filter (fun w => !S.contains w)).length + (if S.contains (t + 1) then 0 else 1) := by
  rw [List.range'_1_concat, List.filter_append]
  simp only [List.filter_cons, List.filter_nil, List.length_append]
  split <;> simp_all [Nat.add_comm]

theorem cnt_push (σ : Nat → Bool) (xs : Array Int) (y : Int) :
    cnt σ (xs.push y) (xs.size + 1) = cnt σ xs xs.size + (if lv σ y then 1 else 0) := by
  have h := cnt_succ σ (xs.push y) (i := xs.size) (by simp)
  rw [h]
  simp only [Array.getElem_push_eq]
  congr 1
  unfold cnt
  simp only [Array.toList_push]
  rw [List.take_append_of_le_length (by simp)]
  try (have : xs.toList.take xs.size = xs.toList := List.take_of_length_le (by simp); rw [this])

/-- `S = {u,v}` leaves 20 candidate common neighbours (kernel check over all pairs). -/
def chkTwenty : Bool := (List.range 23).all fun u => (List.range 23).all fun v =>
  !(1 ≤ u && u < v && v ≤ 22) || ((List.range' 1 22).filter (fun w => ![u, v].contains w)).length == 20

theorem chkTwenty_true : chkTwenty = true := by decide +kernel

theorem filter_twenty {u v : Nat} (hu : 1 ≤ u) (huv : u < v) (hv : v ≤ 22) :
    ((List.range' 1 22).filter (fun w => ![u, v].contains w)).length = 20 := by
  have h := chkTwenty_true
  simp only [chkTwenty, List.all_eq_true, List.mem_range] at h
  have := h u (by omega) v (by omega)
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    beq_iff_eq] at this
  omega

theorem ys_lit {ys : Array Int} {n : Nat} {σ₄ σ₆ : Nat → Bool}
    (hy1 : ∀ l ∈ ys, l ≠ 0 ∧ l.natAbs ≤ n) (hag : Agree σ₄ σ₆ n) {i : Nat} (hi : i < ys.size) :
    ys[i]! ≠ 0 ∧ ys[i]!.natAbs ≤ n ∧ lv σ₆ ys[i]! = lv σ₄ ys[i]! ∧
      cnt σ₄ ys (i + 1) = cnt σ₄ ys i + (if lv σ₄ ys[i]! then 1 else 0) := by
  rw [getElem!_pos ys i hi]
  have h := hy1 _ (Array.getElem_mem hi)
  exact ⟨h.1, h.2, lv_congr (hag _ h.2), cnt_succ σ₄ ys hi⟩

theorem parse_K2x8 : parseKst "K2x8" = some (2, 8) := by decide
theorem parse_K2x5 : parseKst "K2x5" = some (2, 5) := by decide

/-- The Sinz registers allocated so far (rows of `k`). -/
def RegsOK (σ₀ σ : Nat → Bool) (ys : Array Int) (k lo hi t : Nat) (R : Array (Array Int)) : Prop :=
  R.size = t ∧ ∀ i (hi' : i < R.size), R[i].size = k ∧ ∀ j (hj : j < R[i].size),
    ∃ v : Nat, R[i][j] = (v : Int) ∧ lo < v ∧ v ≤ hi ∧ σ v = decide (j + 1 ≤ cnt σ₀ ys (i + 1))

theorem RegsOK.upd {σ₀ σ : Nat → Bool} {ys : Array Int} {k lo hi t : Nat} {R : Array (Array Int)}
    (h : RegsOK σ₀ σ ys k lo hi t R) (b : Bool) : RegsOK σ₀ (upd σ (hi + 1) b) ys k lo (hi + 1) t R := by
  refine ⟨h.1, fun i hi' => ⟨(h.2 i hi').1, fun j hj => ?_⟩⟩
  obtain ⟨v, hv, h1, h2, h3⟩ := (h.2 i hi').2 j hj
  refine ⟨v, hv, h1, by omega, ?_⟩
  simp only [SB.Rooted.upd]
  rw [if_neg (by omega), h3]

theorem RegsOK.get {σ₀ σ : Nat → Bool} {ys : Array Int} {k lo hi t : Nat} {R : Array (Array Int)}
    (h : RegsOK σ₀ σ ys k lo hi t R) {i j : Nat} (hi1 : 1 ≤ i) (hit : i ≤ t) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    ∃ v : Nat, R[i - 1]![j - 1]! = (v : Int) ∧ lo < v ∧ v ≤ hi ∧ σ v = decide (j ≤ cnt σ₀ ys i) := by
  have hi' : i - 1 < R.size := by rw [h.1]; omega
  have hj' : j - 1 < R[i - 1].size := by rw [(h.2 _ hi').1]; omega
  obtain ⟨v, hv, h1, h2, h3⟩ := (h.2 _ hi').2 _ hj'
  refine ⟨v, ?_, h1, h2, ?_⟩
  · rw [getElem!_pos R (i - 1) hi', getElem!_pos _ (j - 1) hj', hv]
  · rw [h3, Nat.sub_add_cancel hi1]; congr 1; apply propext; omega

/-- The `y` literals collected so far for the pair `S` in colour `c`, after the vertices `1..t`. -/
def YsOK (col : Nat → Nat → Bool) (c : Nat) (S : List Nat) (σ : Nat → Bool) (n t : Nat)
    (ys : Array Int) : Prop :=
  (∀ l ∈ ys, l ≠ 0 ∧ l.natAbs ≤ n) ∧
  cnt σ ys ys.size = (commonC col c S t).length ∧
  ys.size = ((List.range' 1 t).filter (fun w => !S.contains w)).length

/-- The base layer is satisfied by the truthful assignment of any colouring meeting both caps. -/
theorem buildBase_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a)
    (hcap1 : CapC col 1 7) (hcap2 : CapC col 2 4)
    (s : St) (σ : Nat → Bool) (H : Prop) (hpre : H → 462 ≤ s.nv ∧ EdgeOK col σ) :
    Spec H (buildBase 22 ["K2x8", "K2x5"]) s σ (fun _ _ _ => True) := by
  unfold buildBase
  dsimp only
  refine spec_bind (Q₁ := fun _ s₁ σ₁ => σ₁ = σ ∧ s₁.nv = s.nv)
    (spec_of_co_gated (F := EdgeOK col σ ∧ 462 ≤ s.nv) (edgeLayer_co col hsym σ s)
      (fun hH => ⟨(hpre hH).2, (hpre hH).1⟩)
      (fun _ _ _ _ => ⟨rfl, rfl⟩)) ?_
  intro _ s₁ σ₁
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
  refine spec_bind (Q₁ := fun _ _ _ => True) ?_ (fun _ _ _ => ?_)
  rotate_left
  · exact spec_pure (fun _ _ _ => trivial)
  refine spec_forIn ["K2x8", "K2x5"] _ _
    (fun i st s₂ σ₂ => st.1 = i + 1 ∧ 462 ≤ s₂.nv ∧ EdgeOK col σ₂) ?_ ?_ (fun _ _ _ _ _ _ => trivial)
  · intro hH _ _
    obtain ⟨hH0, -, -, -, -, hσ₁, hs₁⟩ := hH
    obtain ⟨hn, hE⟩ := hpre hH0
    exact ⟨rfl, by omega, by rw [hσ₁]; exact hE⟩
  intro i hi st s₂ σ₂
  obtain ⟨t, hp, ht, hcap⟩ : ∃ t, parseKst ["K2x8", "K2x5"][i] = some (2, t) ∧ (t = 8 ∨ t = 5) ∧
      (i = 0 → CapC col 1 (t - 1)) ∧ (i = 1 → CapC col 2 (t - 1)) := by
    simp at hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact ⟨8, parse_K2x8, Or.inl rfl, fun _ => hcap1, fun h => absurd h (by omega)⟩
    · exact ⟨5, parse_K2x5, Or.inr rfl, fun h => absurd h (by omega), fun _ => hcap2⟩
  rw [hp]
  dsimp only
  refine spec_bind (Q₁ := fun _ s₃ σ₃ => 462 ≤ s₃.nv ∧ EdgeOK col σ₃) ?_ ?_
  · refine spec_forIn _ _ _ (fun _ _ s₃ σ₃ => 462 ≤ s₃.nv ∧ EdgeOK col σ₃ ∧
        (st.fst = 1 ∨ st.fst = 2) ∧ CapC col st.fst (t - 1) ∧ 1 ≤ t - 1 ∧ t - 1 < 20) ?_ ?_
      (fun _ _ _ _ _ h => ⟨h.1, h.2.1⟩)
    · intro hH _ _
      obtain ⟨-, hst, h1, h2⟩ := hH
      have hi2 : i < 2 := by simpa using hi
      refine ⟨h1, h2, by omega, ?_, by omega, by omega⟩
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · rw [hst]; exact hcap.1 rfl
      · rw [hst]; exact hcap.2 rfl
    · intro j hj nsets s₃ σ₃
      obtain ⟨u, v, hS, hu, huv, hv⟩ := combos_two_mem (List.getElem_mem hj)
      generalize (combos 2 (List.range' 1 22))[j] = S at hS ⊢
      subst hS
      refine spec_bind (Q₁ := fun ys s₄ σ₄ => 462 ≤ s₄.nv ∧ EdgeOK col σ₄ ∧ s₃.nv ≤ s₄.nv ∧
          YsOK col st.fst [u, v] σ₄ s₄.nv 22 ys) ?_ ?_
      · refine spec_forIn_range (I := fun w ys s₄ σ₄ => 462 ≤ s₄.nv ∧ EdgeOK col σ₄ ∧ s₃.nv ≤ s₄.nv ∧
          YsOK col st.fst [u, v] σ₄ s₄.nv w ys ∧ (st.fst = 1 ∨ st.fst = 2)) 1 23 _ _ ?_ ?_
          (fun _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)
        · intro hH _ _
          exact ⟨hH.2.1, hH.2.2.1, Nat.le_refl _, by simp [YsOK, cnt, commonC], hH.2.2.2.1⟩
        · intro w hw ys s₄ σ₄
          split
          · next hcont =>
            refine spec_pure (fun hH _ _ => ?_)
            obtain ⟨-, h1, h2, h3, ⟨hy1, hy2, hy3⟩, hc⟩ := hH
            refine ⟨h1, h2, h3, ⟨hy1, ?_, ?_⟩, hc⟩
            · rw [Nat.add_comm] at hcont
              rw [hy2, commonC_succ, if_neg (by rw [hcont]; simp), List.append_nil]
            · rw [Nat.add_comm] at hcont; rw [hy3, filter_succ, if_pos hcont, Nat.add_zero]
          · next hcont =>
            refine spec_bind (spec_pure (Q := fun _ s₅ σ₅ => s₅ = s₄ ∧ σ₅ = σ₄) (fun _ _ _ => ⟨rfl, rfl⟩)) ?_
            intro _ s₅ σ₅
            refine spec_bind (spec_fresh ([u, v].all (fun x => colV col x (1 + w) st.fst))
              (Q := fun y s₆ σ₆ => y = s₅.nv + 1 ∧ s₆.nv = s₅.nv + 1 ∧
                σ₆ = upd σ₅ (s₅.nv + 1) ([u, v].all (fun x => colV col x (1 + w) st.fst)))
              (fun _ _ _ => ⟨rfl, rfl, rfl⟩)) ?_
            intro y s₆ σ₆
            have hw' : 1 + w = w + 1 := Nat.add_comm _ _
            rw [hw'] at hcont ⊢
            simp only [Bool.not_eq_true] at hcont
            have huw : w + 1 ≠ u := by intro h; simp [h] at hcont
            have hvw : w + 1 ≠ v := by intro h; simp [h] at hcont
            have hw22 : w + 1 ≤ 22 := by omega
            refine spec_bind (Q₁ := fun _ s₇ σ₇ => s₇.nv = s₆.nv ∧ σ₇ = σ₆)
              (spec_add (fun hH hg he => ?_)) ?_
            · obtain ⟨H5, -, -, -, -, hy, hs6, hσ6⟩ := hH
              obtain ⟨⟨-, h1, hE4, h3, ⟨hy1, hy2, hy3⟩, hc⟩, -, -, -, -, rfl, rfl⟩ := H5
              subst hy hσ6
              have hc' : st.fst = 1 ∨ st.fst = 2 := hc
              have hvu : VPair u (w + 1) := ⟨hu, by omega, by omega, hw22, by omega⟩
              have hvv : VPair v (w + 1) := ⟨by omega, hv, by omega, hw22, by omega⟩
              have hE6 := EdgeOK.agree hE4 (agree_upd _ _
                ([u, v].all (fun x => colV col x (w + 1) st.fst))) (by omega)
              have bu := varE_bounds hvu hc'
              have bv := varE_bounds hvv hc'
              have lu := lv_varE hsym hE6 hvu hc'
              have lvv := lv_varE hsym hE6 hvv hc'
              refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_, rfl, rfl⟩
              · simp at hl
                rcases hl with rfl | rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> omega
              · simp at hl; rcases hl with rfl | rfl | rfl <;> omega
              · rw [List.any_eq_true]
                have ly := lv_upd_self σ₅ (s₅.nv + 1)
                  ([u, v].all (fun x => colV col x (w + 1) st.fst)) (Nat.succ_pos _)
                cases h1 : colV col u (w + 1) st.fst <;> cases h2 : colV col v (w + 1) st.fst
                · exact ⟨-varE 22 2 u (w + 1) st.fst, by simp, by rw [lv_neg _ bu.2.2, lu, h1]; rfl⟩
                · exact ⟨-varE 22 2 u (w + 1) st.fst, by simp, by rw [lv_neg _ bu.2.2, lu, h1]; rfl⟩
                · exact ⟨-varE 22 2 v (w + 1) st.fst, by simp, by rw [lv_neg _ bv.2.2, lvv, h2]; rfl⟩
                · exact ⟨((s₅.nv + 1 : Nat) : Int), by simp, by rw [ly]; simp [h1, h2]⟩
            · intro _ s₇ σ₇
              refine spec_bind (spec_pure (Q := fun _ s₈ σ₈ => s₈ = s₇ ∧ σ₈ = σ₇)
                (fun _ _ _ => ⟨rfl, rfl⟩)) ?_
              intro _ s₈ σ₈
              refine spec_pure (fun hH _ _ => ?_)
              obtain ⟨H7, -, -, -, -, rfl, rfl⟩ := hH
              obtain ⟨H6, -, -, -, -, hs7, rfl⟩ := H7
              obtain ⟨H5, -, -, -, -, hy, hs6, rfl⟩ := H6
              obtain ⟨⟨-, h1, hE4, h3, ⟨hy1, hy2, hy3⟩, hc⟩, -, -, -, -, rfl, rfl⟩ := H5
              subst hy
              refine ⟨by omega, EdgeOK.agree hE4 (agree_upd _ _ _) (by omega), by omega, ⟨?_, ?_, ?_⟩, hc⟩
              · intro l hl
                rcases Array.mem_push.mp hl with hl | rfl
                · exact ⟨(hy1 l hl).1, by have := (hy1 l hl).2; omega⟩
                · exact ⟨by omega, by simp only [Int.natAbs_natCast]; omega⟩
              · rw [Array.size_push, cnt_push, lv_natCast _ (by omega)]
                rw [cnt_congr (agree_upd _ _ _) (fun l hl => (hy1 l hl).2), hy2, commonC_succ]
                simp only [upd, if_pos, hcont, Bool.not_false, Bool.true_and]
                split <;> simp
              · rw [Array.size_push, hy3, filter_succ, hcont]
                rfl
      · intro ys s₄ σ₄
        split
        · exact spec_fail_bind (fun _ => by mono_tac)
        · next hm =>
          refine spec_bind (spec_pure (Q := fun _ s₅ σ₅ => s₅ = s₄ ∧ σ₅ = σ₄) (fun _ _ _ => ⟨rfl, rfl⟩)) ?_
          intro _ s₅ σ₅
          refine spec_bind (Q₁ := fun R s₆ σ₆ => RegsOK σ₄ σ₆ ys (t - 1) s₄.nv s₆.nv (ys.size - 1) R ∧
              s₄.nv ≤ s₆.nv ∧ Agree σ₄ σ₆ s₄.nv) ?_ ?_
          · refine spec_forIn_range (I := fun i R s₆ σ₆ =>
                RegsOK σ₄ σ₆ ys (t - 1) s₄.nv s₆.nv i R ∧ s₄.nv ≤ s₆.nv ∧ Agree σ₄ σ₆ s₄.nv)
              1 ys.size _ _ ?_ ?_ (fun _ _ _ _ _ h => h)
            · intro hH _ _
              obtain ⟨-, -, -, -, -, rfl, rfl⟩ := hH
              exact ⟨⟨rfl, fun i hi => absurd hi (by simp)⟩, Nat.le_refl _, agree_refl _ _⟩
            · intro i hi R s₆ σ₆
              refine spec_bind (Q₁ := fun row s₇ σ₇ => RegsOK σ₄ σ₇ ys (t - 1) s₄.nv s₇.nv i R ∧
                  s₄.nv ≤ s₇.nv ∧ Agree σ₄ σ₇ s₄.nv ∧ row.size = t - 1 ∧
                  ∀ jj (hjj : jj < row.size), ∃ v : Nat, row[jj] = (v : Int) ∧ s₄.nv < v ∧ v ≤ s₇.nv ∧
                    σ₇ v = decide (jj + 1 ≤ cnt σ₄ ys (i + 1))) ?_ ?_
              · refine spec_forIn_range (I := fun jj row s₇ σ₇ => RegsOK σ₄ σ₇ ys (t - 1) s₄.nv s₇.nv i R ∧
                  s₄.nv ≤ s₇.nv ∧ Agree σ₄ σ₇ s₄.nv ∧ row.size = jj ∧
                  ∀ jj (hjj : jj < row.size), ∃ v : Nat, row[jj] = (v : Int) ∧ s₄.nv < v ∧ v ≤ s₇.nv ∧
                    σ₇ v = decide (jj + 1 ≤ cnt σ₄ ys (i + 1))) 1 (t - 1 + 1) _ _ ?_ ?_
                    (fun _ _ _ _ _ h => by simpa using h)
                · intro hH _ _
                  obtain ⟨-, h1, h2, h3⟩ := hH
                  exact ⟨h1, h2, h3, rfl, fun jj hjj => absurd hjj (by simp)⟩
                · intro jj hjj row s₇ σ₇
                  refine spec_bind (spec_fresh (decide (jj + 1 ≤ cnt σ₄ ys (i + 1)))
                    (Q := fun x s₈ σ₈ => x = s₇.nv + 1 ∧ s₈.nv = s₇.nv + 1 ∧
                      σ₈ = upd σ₇ (s₇.nv + 1) (decide (jj + 1 ≤ cnt σ₄ ys (i + 1))))
                    (fun _ _ _ => ⟨rfl, rfl, rfl⟩)) ?_
                  intro x s₈ σ₈
                  refine spec_bind (spec_pure (Q := fun _ s₉ σ₉ => s₉ = s₈ ∧ σ₉ = σ₈)
                    (fun _ _ _ => ⟨rfl, rfl⟩)) ?_
                  intro _ s₉ σ₉
                  refine spec_pure (fun hH _ _ => ?_)
                  obtain ⟨H8, -, -, -, -, hs9, hσ9⟩ := hH
                  obtain ⟨⟨-, hR, hle, hag, hsz, hrow⟩, -, -, -, -, hx, hs8, hσ8⟩ := H8
                  rw [hs9, hσ9, hσ8, hx]
                  refine ⟨?_, by omega, agree_trans hag (agree_upd _ _ _) (by omega), by simp [hsz], ?_⟩
                  · rw [hs8]; exact hR.upd _
                  · intro jj' hjj'
                    simp only [Array.size_push] at hjj'
                    by_cases hlt : jj' < row.size
                    · rw [Array.getElem_push_lt hlt]
                      obtain ⟨w, hw, h1, h2, h3⟩ := hrow jj' hlt
                      refine ⟨w, hw, h1, by omega, ?_⟩
                      simp only [SB.Rooted.upd]; rw [if_neg (by omega), h3]
                    · have : jj' = row.size := by omega
                      subst this
                      rw [Array.getElem_push_eq]
                      refine ⟨s₇.nv + 1, rfl, by omega, by omega, ?_⟩
                      simp only [SB.Rooted.upd, if_pos, hsz]
              · intro row s₇ σ₇
                refine spec_bind (spec_pure (Q := fun _ s₈ σ₈ => s₈ = s₇ ∧ σ₈ = σ₇)
                  (fun _ _ _ => ⟨rfl, rfl⟩)) ?_
                intro _ s₈ σ₈
                refine spec_pure (fun hH _ _ => ?_)
                obtain ⟨⟨-, -, -, -, -, hR, hle, hag, hsz, hrow⟩, -, -, -, -, hs8, hσ8⟩ := hH
                rw [hs8, hσ8]
                refine ⟨⟨by simp [hR.1], fun i' hi' => ?_⟩, hle, hag⟩
                simp only [Array.size_push] at hi'
                by_cases hlt : i' < R.size
                · rw [Array.getElem_push_lt hlt]; exact hR.2 i' hlt
                · have : i' = R.size := by omega
                  subst this
                  rw [Array.getElem_push_eq]
                  refine ⟨hsz, fun jj hjj => ?_⟩
                  rw [hR.1]; exact hrow jj hjj
          · intro R s₆ σ₆
            refine spec_of_co_gated (post := fun _ => True)
              (F := (∀ l ∈ ys, l ≠ 0 ∧ l.natAbs ≤ s₄.nv) ∧ Agree σ₄ σ₆ s₄.nv ∧
                RegsOK σ₄ σ₆ ys (t - 1) s₄.nv s₆.nv (ys.size - 1) R ∧ ys.size = 20 ∧
                cnt σ₄ ys 20 ≤ t - 1 ∧ 1 ≤ t - 1 ∧ s₄.nv ≤ s₆.nv) ?_ ?_ ?_
            · co_step
              · rintro ⟨hy1, hag, hR, hsz, hcnt, hk, hle⟩
                obtain ⟨y0, yb, yl, yc⟩ := ys_lit hy1 hag (i := 0) (by omega)
                obtain ⟨v1, hv1, h1, h2, h3⟩ := hR.get (i := 1) (j := 1) (by omega) (by omega) (by omega) hk
                rw [hv1]
                refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
                · simp at hl; rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> omega
                · simp at hl; rcases hl with rfl | rfl <;> omega
                · simp [lv_neg _ y0, yl, lv_natCast _ (by omega : 0 < v1), h3, yc, cnt_zero]
                  cases lv σ₄ ys[0]! <;> simp
              · apply co_forIn_range
                intro i hi1 hi2 _ s'
                co_step
                · rintro ⟨hy1, hag, hR, hsz, hcnt, hk, hle⟩
                  obtain ⟨y0, yb, yl, yc⟩ := ys_lit hy1 hag (i := i - 1) (by omega)
                  obtain ⟨v1, hv1, h1, h2, h3⟩ := hR.get (i := i) (j := 1) (by omega) (by omega) (by omega) hk
                  rw [hv1]
                  have hi' : i - 1 + 1 = i := by omega
                  rw [hi'] at yc
                  refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
                  · simp at hl; rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> omega
                  · simp at hl; rcases hl with rfl | rfl <;> omega
                  · simp [lv_neg _ y0, yl, lv_natCast _ (by omega : 0 < v1), h3, yc]
                    cases lv σ₄ ys[i - 1]! <;> simp
                · apply co_forIn_range
                  intro j hj1 hj2 _ s''
                  co_step
                  rintro ⟨hy1, hag, hR, hsz, hcnt, hk, hle⟩
                  obtain ⟨y0, yb, yl, yc⟩ := ys_lit hy1 hag (i := i - 1) (by omega)
                  obtain ⟨v1, hv1, h1, h2, h3⟩ := hR.get (i := i - 1) (j := j) (by omega) (by omega) (by omega) (by omega)
                  obtain ⟨v2, hv2, h4, h5, h6⟩ := hR.get (i := i) (j := j) (by omega) (by omega) (by omega) (by omega)
                  rw [hv1, hv2]
                  have hi' : i - 1 + 1 = i := by omega
                  rw [hi'] at yc
                  refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
                  · simp at hl; rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> omega
                  · simp at hl; rcases hl with rfl | rfl <;> omega
                  · simp [lv_neg_natCast _ (by omega : 0 < v1), lv_natCast _ (by omega : 0 < v2), h3, h6, yc]
                    omega
                · apply co_forIn_range
                  intro j hj1 hj2 _ s''
                  co_step
                  rintro ⟨hy1, hag, hR, hsz, hcnt, hk, hle⟩
                  obtain ⟨y0, yb, yl, yc⟩ := ys_lit hy1 hag (i := i - 1) (by omega)
                  obtain ⟨v1, hv1, h1, h2, h3⟩ := hR.get (i := i - 1) (j := j - 1) (by omega) (by omega) (by omega) (by omega)
                  obtain ⟨v2, hv2, h4, h5, h6⟩ := hR.get (i := i) (j := j) (by omega) (by omega) (by omega) (by omega)
                  rw [hv1, hv2]
                  have hi' : i - 1 + 1 = i := by omega
                  rw [hi'] at yc
                  refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
                  · simp at hl; rcases hl with rfl | rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> omega
                  · simp at hl; rcases hl with rfl | rfl | rfl <;> omega
                  · simp [lv_neg _ y0, yl, lv_neg_natCast _ (by omega : 0 < v1), lv_natCast _ (by omega : 0 < v2), h3, h6, yc]
                    cases lv σ₄ ys[i - 1]! <;> simp <;> omega
              · apply co_forIn_range
                intro i hi1 hi2 _ s'
                co_step
                rintro ⟨hy1, hag, hR, hsz, hcnt, hk, hle⟩
                obtain ⟨y0, yb, yl, yc⟩ := ys_lit hy1 hag (i := i - 1) (by omega)
                obtain ⟨v1, hv1, h1, h2, h3⟩ := hR.get (i := i - 1) (j := t - 1) (by omega) (by omega) (by omega) (Nat.le_refl _)
                rw [hv1]
                have hi' : i - 1 + 1 = i := by omega
                rw [hi'] at yc
                have hmono := cnt_mono σ₄ ys (i := i) (j := 20) (by omega)
                refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
                · simp at hl; rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> omega
                · simp at hl; rcases hl with rfl | rfl <;> omega
                · simp [lv_neg _ y0, yl, lv_neg_natCast _ (by omega : 0 < v1), h3]
                  cases hyv : lv σ₄ ys[i - 1]! <;> simp [hyv] at yc ⊢ <;> omega
            · intro hH
              obtain ⟨X, -, -, -, -, hRg, hle6, hag6⟩ := hH
              obtain ⟨Y, -, -, -, -, -, -⟩ := X
              obtain ⟨Z, -, -, -, -, h462, hE4, hle4, ⟨hy1, hy2, hy3⟩⟩ := Y
              obtain ⟨-, -, -, hc, hcapc, hk1, hk20⟩ := Z
              have hsz : ys.size = 20 := by rw [hy3]; exact filter_twenty hu huv hv
              refine ⟨hy1, hag6, hRg, hsz, ?_, hk1, hle6⟩
              rw [← hsz, hy2]
              exact hcapc u v hu huv hv
            · intro x cs hH _
              obtain ⟨X, -, -, -, -, hRg, hle6, hag6⟩ := hH
              obtain ⟨Y, -, -, -, -, -, -⟩ := X
              obtain ⟨Z, -, -, -, -, h462, hE4, hle4, ⟨hy1, hy2, hy3⟩⟩ := Y
              obtain ⟨-, -, -, hc, hcapc, hk1, hk20⟩ := Z
              have hfin : 462 ≤ s₆.nv ∧ EdgeOK col σ₆ ∧ (st.fst = 1 ∨ st.fst = 2) ∧
                  CapC col st.fst (t - 1) ∧ 1 ≤ t - 1 ∧ t - 1 < 20 :=
                ⟨by omega, EdgeOK.agree hE4 hag6 h462, hc, hcapc, hk1, hk20⟩
              cases x <;> exact hfin
  · intro _ s₃ σ₃
    refine spec_bind (spec_pure (Q := fun _ s₄ σ₄ => s₄ = s₃ ∧ σ₄ = σ₃) (fun _ _ _ => ⟨rfl, rfl⟩)) ?_
    intro _ s₄ σ₄
    refine spec_pure (fun hH _ _ => ?_)
    obtain ⟨⟨⟨-, hst, -⟩, -, -, -, -, h1, h2⟩, -, -, -, -, rfl, rfl⟩ := hH
    exact ⟨by simp [hst], h1, h2⟩

end SB.Rooted
#print axioms SB.Rooted.buildBase_spec
