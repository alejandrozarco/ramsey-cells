/-
# M3: the whole rooted formula, at the core level

`rootedFormula_sat_core`: if the encoder returns a formula `F` for the cell `K2x8,K2x5` at `N = 22`,
and the colouring `col` meets `CoreCanon` (every family's semantic premise, stated about `col`
alone), then an assignment satisfies every clause of `F`.
-/
import RootedBridge.Counting
import RootedBridge.Autos
import RootedBridge.TopDefs

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

/-- The encoder's normalised `H` (sorted, deduplicated `srt` pairs). -/
def normH (H : List (Nat × Nat)) : Array (Nat × Nat) :=
  ((H.map fun (a, b) => srt a b).eraseDups.mergeSort
    (fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 ≤ y.2))).toArray

/-- The wallpairs comparison list of the transposition `(p q)`. -/
def wallPairs (p q : Nat) : Array ((Nat × Nat) × (Nat × Nat)) :=
  (((List.range' 1 22).filter (fun x => x != p && x != q)).map (fun x => (srt p x, srt q x))).toArray

/-- The auth comparison list of an enumerated automorphism. -/
def authPairs (asg : Array (Nat × Nat)) : Array ((Nat × Nat) × (Nat × Nat)) :=
  (edgesOf 22).filterMap fun e =>
    let f := srt (imgA asg e.1) (imgA asg e.2)
    if f != e then some (e, f) else none

/-- The N-cells as vertex arrays (the encoder's `cl`). -/
def nCellArrays (cells : Cells) : Array (Array Nat) :=
  cells.ncells.map fun (lo, hi, _) => (List.range' lo (hi + 1 - lo)).toArray

/-- Run a spec from the initial state to a satisfying assignment of the final clauses. -/
theorem spec_run {α : Type} {P : EncM α} {init : St} {σ : Nat → Bool} {Q : α → St → (Nat → Bool) → Prop}
    {x : α} {st : St} (h : Spec True P init σ Q) (heq : P.run init = (x, st)) (he : st.errs = #[])
    (hg : Good init σ) : ∃ σ', ClsSat σ' st.cls := by
  have h2 := h.2 trivial hg (by rw [heq]; exact he)
  rw [heq] at h2
  obtain ⟨-, -, σ', -, hs, -⟩ := h2
  exact ⟨σ', hs⟩

/-- Every family's semantic premise, about the colouring `col` (1-based, blue = `true`). -/
structure CoreCanon (col : Nat → Nat → Bool) (k : Nat) (cells : Cells) (Hs : Array (Nat × Nat))
    (o : Opts) : Prop where
  symm : ∀ a b, col a b = col b a
  row1 : ∀ u, 2 ≤ u → u ≤ 22 → col 1 u = (decide (2 ≤ u) && decide (u ≤ k + 1))
  hunits : ∀ i j, 1 ≤ i → i < j → j ≤ 22 → 2 ≤ i → j ≤ k + 1 → col i j = Hs.contains (i, j)
  deg : DegOK col cells.D
  iv : IvOK col cells.D o.tight
  chan : o.channel = true → ChanOK col cells.D
  bud : o.budget = true → BudOK col cells.D
  capR : o.baseCodegree = true → CapC col 1 7
  capB : o.baseCodegree = true → CapC col 2 4
  wcellsIn : ∀ c ∈ cells.wcells, 1 ≤ c.1 ∧ c.2.1 ≤ 22
  wlex : ∀ c ∈ cells.wcells, ∀ v, c.1 ≤ v → v < c.2.1 →
    LexOK col (movedPairs (edgesOf 22) v (v + 1))
  wall : o.wallpairs = true → ∀ c ∈ cells.wcells, ∀ p q, c.1 ≤ p → p < q → q ≤ c.2.1 →
    LexOK col (wallPairs p q)
  ncellsIn : ∀ v ∈ cellVerts (nCellArrays cells), 1 ≤ v ∧ v ≤ 22
  ncellsNodup : (cellVerts (nCellArrays cells)).Nodup
  auth : o.auth = true → ∀ asg ∈ autos (nCellArrays cells) Hs, LexOK col (authPairs asg)
  noShortfall : o.shortfall = false

theorem row1Block_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) (k : Nat)
    (hrow : ∀ u, 2 ≤ u → u ≤ 22 → col 1 u = (decide (2 ≤ u) && decide (u ≤ k + 1)))
    (s : St) (σ : Nat → Bool) (H : Prop) (hpre : H → 462 ≤ s.nv ∧ EdgeOK col σ) :
    Spec H (row1Block 22 k) s σ (fun _ s' σ' => s'.nv = s.nv ∧ σ' = σ) := by
  unfold row1Block
  dsimp only
  refine spec_of_co_gated (post := fun _ => True) (F := 462 ≤ s.nv ∧ EdgeOK col σ) ?_ hpre
    (fun _ _ _ _ => ⟨rfl, rfl⟩)
  apply co_forIn_range
  intro u hu1 hu2 _ s'
  co_step
  intro ⟨hn, hE⟩
  have hv : VPair 1 u := ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hc : (if (decide (2 ≤ u) && decide (u ≤ k + 1)) = true then 2 else 1) = 1 ∨
      (if (decide (2 ≤ u) && decide (u ≤ k + 1)) = true then 2 else 1) = 2 := by split <;> simp
  have hb := varE_bounds hv hc
  have hl := lv_varE hsym hE hv hc
  refine ⟨fun l hl' => ?_, clauseSat_of_any (fun l hl' => ?_) ?_⟩
  · simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hl'; subst hl'; omega
  · simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hl'; subst hl'; exact hb.2.2
  · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
    rw [hl]
    unfold colV
    rw [hrow u (by omega) (by omega)]
    split <;> simp_all

theorem hBlock_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) (k : Nat)
    (Hs : Array (Nat × Nat))
    (hun : ∀ i j, 1 ≤ i → i < j → j ≤ 22 → 2 ≤ i → j ≤ k + 1 → col i j = Hs.contains (i, j))
    (s : St) (σ : Nat → Bool) (H : Prop) (hpre : H → 462 ≤ s.nv ∧ EdgeOK col σ) :
    Spec H (hBlock 22 k Hs) s σ (fun _ s' σ' => s'.nv = s.nv ∧ σ' = σ) := by
  unfold hBlock
  dsimp only
  refine spec_of_co_gated (post := fun _ => True) (F := 462 ≤ s.nv ∧ EdgeOK col σ) ?_ hpre
    (fun _ _ _ _ => ⟨rfl, rfl⟩)
  apply co_forIn_array
  intro e he _ s'
  obtain ⟨i, j⟩ := e
  obtain ⟨hi1, hij, hj2⟩ := mem_edgesOf he
  dsimp only at hi1 hij hj2 ⊢
  co_step
  intro ⟨hn, hE⟩
  next hnb =>
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hnb
  have hv : VPair i j := ⟨hi1, by omega, by omega, hj2, by omega⟩
  have hc : (if Hs.contains (i, j) = true then 2 else 1) = 1 ∨
      (if Hs.contains (i, j) = true then 2 else 1) = 2 := by split <;> simp
  have hb := varE_bounds hv hc
  have hl := lv_varE hsym hE hv hc
  refine ⟨fun l hl' => ?_, clauseSat_of_any (fun l hl' => ?_) ?_⟩
  · simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hl'; subst hl'; omega
  · simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hl'; subst hl'; exact hb.2.2
  · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
    rw [hl]
    unfold colV
    rw [hun i j hi1 hij hj2 hnb.1.1 hnb.2.2]
    split <;> simp_all

theorem pairsOK_of_mem {pairs : Array ((Nat × Nat) × (Nat × Nat))}
    (h : ∀ x ∈ pairs, VPair x.1.1 x.1.2 ∧ VPair x.2.1 x.2.2) : PairsOK pairs :=
  fun t ht => h _ (Array.getElem_mem ht)

theorem vpair_srt {a b : Nat} (h : VPair a b) : VPair (srt a b).1 (srt a b).2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold srt; split <;> exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem movedPairs_ok {a b : Nat} (hab : VPair a b) : PairsOK (movedPairs (edgesOf 22) a b) := by
  apply pairsOK_of_mem
  intro x hx
  unfold movedPairs at hx
  rw [Array.mem_filterMap] at hx
  obtain ⟨e, he, hfe⟩ := hx
  obtain ⟨he1, he2, he3⟩ := mem_edgesOf he
  obtain ⟨ha1, ha2, hb1, hb2, hne⟩ := hab
  dsimp only at hfe
  generalize hs1 : (if (e.fst == a) = true then b else if (e.fst == b) = true then a else e.fst) = u at hfe
  generalize hs2 : (if (e.snd == a) = true then b else if (e.snd == b) = true then a else e.snd) = w at hfe
  have hu : 1 ≤ u ∧ u ≤ 22 := by
    rw [← hs1]; split <;> (try split) <;> omega
  have hw : 1 ≤ w ∧ w ≤ 22 := by
    rw [← hs2]; split <;> (try split) <;> omega
  have huw : u ≠ w := by
    rw [← hs1, ← hs2]
    simp only [beq_iff_eq]
    split <;> split <;> (try split) <;> (try split) <;> omega
  by_cases hf : (srt u w != e) = true
  · rw [if_pos hf] at hfe
    cases hfe
    show VPair e.1 e.2 ∧ VPair (srt u w).1 (srt u w).2
    exact ⟨⟨he1, by omega, by omega, he3, by omega⟩, vpair_srt ⟨hu.1, hu.2, hw.1, hw.2, huw⟩⟩
  · rw [if_neg hf] at hfe
    cases hfe

theorem wallPairs_ok {p q : Nat} (hp : 1 ≤ p) (hpq : p < q) (hq : q ≤ 22) : PairsOK (wallPairs p q) := by
  apply pairsOK_of_mem
  intro y hy
  unfold wallPairs at hy
  simp only [List.mem_toArray, List.mem_map, List.mem_filter, List.mem_range'_1] at hy
  obtain ⟨x, ⟨hx, hxpq⟩, rfl⟩ := hy
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hxpq
  exact ⟨vpair_srt ⟨hp, by omega, by omega, by omega, by omega⟩,
    vpair_srt ⟨by omega, hq, by omega, by omega, by omega⟩⟩

theorem wlexBlock_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a)
    (wcells : Array (Nat × Nat × Nat)) (hin : ∀ c ∈ wcells, 1 ≤ c.1 ∧ c.2.1 ≤ 22)
    (hlex : ∀ c ∈ wcells, ∀ v, c.1 ≤ v → v < c.2.1 → LexOK col (movedPairs (edgesOf 22) v (v + 1)))
    (s : St) (σ : Nat → Bool) (H : Prop) (hpre : H → 462 ≤ s.nv ∧ EdgeOK col σ) :
    Spec H (wlexBlock 22 wcells) s σ (fun _ s' σ' => 462 ≤ s'.nv ∧ EdgeOK col σ') := by
  unfold wlexBlock
  refine spec_forIn_array (I := fun _ _ s' σ' => 462 ≤ s'.nv ∧ EdgeOK col σ') _ _ _
    (fun hH _ _ => hpre hH) ?_ (fun _ _ _ _ _ h => h)
  intro i hi _ s₁ σ₁
  obtain ⟨hlo, hhi⟩ := hin _ (Array.getElem_mem hi)
  have hl := hlex _ (Array.getElem_mem hi)
  generalize wcells[i] = c at hlo hhi hl ⊢
  obtain ⟨lo, hi', d⟩ := c
  dsimp only at hlo hhi hl ⊢
  refine spec_bind (Q₁ := fun _ s' σ' => 462 ≤ s'.nv ∧ EdgeOK col σ') ?_
    (fun _ s₂ σ₂ => spec_pure_bind (spec_pure (fun hH _ _ => hH.2.2.2.2.2)))
  refine spec_forIn_range (I := fun _ _ s' σ' => 462 ≤ s'.nv ∧ EdgeOK col σ') lo hi' _ _
    (fun hH _ _ => hH.2) ?_ (fun _ _ _ _ _ h => h)
  intro v hv _ s₂ σ₂
  refine spec_bind (lexLeq_spec' col hsym _ (movedPairs_ok ⟨by omega, by omega, by omega, by omega, by omega⟩)
    (hl (lo + v) (by omega) (by omega)) s₂ σ₂ _ (fun hH => hH.2)) (fun _ s₃ σ₃ => ?_)
  refine spec_pure (fun hH _ _ => ?_)
  obtain ⟨⟨-, h462, hE⟩, -, h23, ag23, -, -⟩ := hH
  exact ⟨by omega, EdgeOK.agree hE ag23 h462⟩

theorem wallBlock_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a)
    (wcells : Array (Nat × Nat × Nat)) (hin : ∀ c ∈ wcells, 1 ≤ c.1 ∧ c.2.1 ≤ 22)
    (hwall : ∀ c ∈ wcells, ∀ p q, c.1 ≤ p → p < q → q ≤ c.2.1 → LexOK col (wallPairs p q))
    (s : St) (σ : Nat → Bool) (H : Prop) (hpre : H → 462 ≤ s.nv ∧ EdgeOK col σ) :
    Spec H (wallBlock 22 wcells) s σ (fun _ s' σ' => 462 ≤ s'.nv ∧ EdgeOK col σ') := by
  unfold wallBlock
  refine spec_forIn_array (I := fun _ _ s' σ' => 462 ≤ s'.nv ∧ EdgeOK col σ') _ _ _
    (fun hH _ _ => hpre hH) ?_ (fun _ _ _ _ _ h => h)
  intro i hi _ s₁ σ₁
  obtain ⟨hlo, hhi⟩ := hin _ (Array.getElem_mem hi)
  have hl := hwall _ (Array.getElem_mem hi)
  generalize wcells[i] = c at hlo hhi hl ⊢
  obtain ⟨lo, hi', d⟩ := c
  dsimp only at hlo hhi hl ⊢
  refine spec_bind (Q₁ := fun _ s' σ' => 462 ≤ s'.nv ∧ EdgeOK col σ') ?_
    (fun _ s₂ σ₂ => spec_pure_bind (spec_pure (fun hH _ _ => hH.2.2.2.2.2)))
  refine spec_forIn_range (I := fun _ _ s' σ' => 462 ≤ s'.nv ∧ EdgeOK col σ') lo (hi' + 1) _ _
    (fun hH _ _ => hH.2) ?_ (fun _ _ _ _ _ h => h)
  intro p hp _ s₂ σ₂
  refine spec_bind (Q₁ := fun _ s' σ' => 462 ≤ s'.nv ∧ EdgeOK col σ') ?_
    (fun _ s₃ σ₃ => spec_pure_bind (spec_pure (fun hH _ _ => hH.2.2.2.2.2)))
  refine spec_forIn_range (I := fun _ _ s' σ' => 462 ≤ s'.nv ∧ EdgeOK col σ') (lo + p + 1) (hi' + 1)
    _ _ (fun hH _ _ => hH.2) ?_ (fun _ _ _ _ _ h => h)
  intro q hq _ s₃ σ₃
  -- the comparison list is `wallPairs`
  refine spec_bind (Q₁ := fun pairs s' σ' => pairs = wallPairs (lo + p) (lo + p + 1 + q) ∧ s' = s₃ ∧
      σ' = σ₃) ?_ (fun pairs s₄ σ₄ => ?_)
  · refine spec_forIn_range (I := fun t pairs s' σ' => pairs.toList =
        (((List.range' 1 t).filter (fun x => x != lo + p && x != lo + p + 1 + q)).map
          (fun x => (srt (lo + p) x, srt (lo + p + 1 + q) x))) ∧ s' = s₃ ∧ σ' = σ₃) 1 (22 + 1) _ _
      (fun _ _ _ => ⟨rfl, rfl, rfl⟩) ?_ (fun pairs s' σ' _ _ h => ⟨?_, h.2⟩)
    · intro x hx pairs s₄ σ₄
      rw [show 1 + x = x + 1 from Nat.add_comm _ _]
      split
      · next hc =>
        refine spec_pure_bind (spec_pure (fun hH _ _ => ?_))
        obtain ⟨-, h1, h2, h3⟩ := hH
        refine ⟨?_, h2, h3⟩
        rw [Array.toList_push, h1, List.range'_1_concat, List.filter_append, List.map_append]
        simp only [List.filter_cons, List.filter_nil, show 1 + x = x + 1 from Nat.add_comm _ _, hc, if_true,
          List.map_cons, List.map_nil]
      · next hc =>
        refine spec_pure_bind (spec_pure (fun hH _ _ => ?_))
        obtain ⟨-, h1, h2, h3⟩ := hH
        refine ⟨?_, h2, h3⟩
        rw [h1, List.range'_1_concat, List.filter_append, List.map_append]
        simp only [List.filter_cons, List.filter_nil, show 1 + x = x + 1 from Nat.add_comm _ _, hc,
          Bool.false_eq_true, if_false, List.map_nil, List.append_nil]
    · apply Array.toList_inj.mp
      rw [h.1]; unfold wallPairs; simp
  · refine spec_bind (lexLeq_spec_gated col hsym pairs s₄ σ₄ _ (fun hH => ?_)) (fun _ s₅ σ₅ => ?_)
    · obtain ⟨⟨-, h462, hE⟩, -, -, -, -, hpe, rfl, rfl⟩ := hH
      subst hpe
      exact ⟨wallPairs_ok (by omega) (by omega) (by omega), hl _ _ (by omega) (by omega) (by omega),
        h462, hE⟩
    · refine spec_pure (fun hH _ _ => ?_)
      obtain ⟨⟨⟨-, h462, hE⟩, -, -, -, -, -, rfl, rfl⟩, -, h45, ag45, -, -⟩ := hH
      exact ⟨by omega, EdgeOK.agree hE ag45 h462⟩

theorem authPairs_ok (cl : Array (Array Nat)) (Hs : Array (Nat × Nat)) (hnd : (cellVerts cl).Nodup)
    (hin : ∀ v ∈ cellVerts cl, 1 ≤ v ∧ v ≤ 22) (asg : Array (Nat × Nat)) (hasg : asg ∈ autos cl Hs) :
    PairsOK (authPairs asg) := by
  obtain ⟨hcell, hoff, hinj, -⟩ := autos_img cl Hs hnd asg hasg
  have hrange : ∀ v, 1 ≤ v → v ≤ 22 → 1 ≤ imgA asg v ∧ imgA asg v ≤ 22 := by
    intro v h1 h2
    by_cases hv : v ∈ cellVerts cl
    · obtain ⟨c, hc, hvc, hic⟩ := hcell v hv
      exact hin _ (mem_cellVerts.mpr ⟨c, hc, hic⟩)
    · rw [hoff v hv]; exact ⟨h1, h2⟩
  apply pairsOK_of_mem
  intro x hx
  unfold authPairs at hx
  rw [Array.mem_filterMap] at hx
  obtain ⟨e, he, hfe⟩ := hx
  obtain ⟨he1, he2, he3⟩ := mem_edgesOf he
  dsimp only at hfe
  by_cases hf : (srt (imgA asg e.1) (imgA asg e.2) != e) = true
  · rw [if_pos hf] at hfe
    cases hfe
    show VPair e.1 e.2 ∧ VPair (srt (imgA asg e.1) (imgA asg e.2)).1 (srt (imgA asg e.1) (imgA asg e.2)).2
    have r1 := hrange e.1 he1 (by omega)
    have r2 := hrange e.2 (by omega) he3
    have hne : imgA asg e.1 ≠ imgA asg e.2 := fun h => by have := hinj _ _ h; omega
    exact ⟨⟨he1, by omega, by omega, he3, by omega⟩, vpair_srt ⟨r1.1, r1.2, r2.1, r2.2, hne⟩⟩
  · rw [if_neg hf] at hfe
    cases hfe

theorem edgeOnly_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) (s : St)
    (σ : Nat → Bool) (H : Prop) (hpre : H → 462 ≤ s.nv ∧ EdgeOK col σ) :
    Spec H (edgeOnlyBlock 22 2) s σ (fun _ s' σ' => s'.nv = s.nv ∧ σ' = σ) := by
  unfold edgeOnlyBlock
  refine spec_of_co_gated (post := fun _ => True) (F := EdgeOK col σ ∧ 462 ≤ s.nv)
    (edgeLayer_co col hsym σ s) (fun hH => ⟨(hpre hH).2, (hpre hH).1⟩) (fun _ _ _ _ => ⟨rfl, rfl⟩)

theorem progOf_spec (k : Nat) (cells : Cells) (H : List (Nat × Nat)) (o : Opts)
    (col : Nat → Nat → Bool) (hc : CoreCanon col k cells (normH H) o) (s : St) (σ : Nat → Bool)
    (hn : 462 ≤ s.nv) (hE : EdgeOK col σ) :
    Spec True (progOf 22 ["K2x8", "K2x5"] k cells (normH H) o 4 7) s σ (fun _ _ _ => True) := by
  have hsym := hc.symm
  unfold progOf
  extract_lets D E es com0 nauts0 cl jp rr com1
  -- the code after the base layer, proved once
  have hjp : ∀ (Hp : Prop) (cm : List String) (s₁ : St) (σ₁ : Nat → Bool),
      (Hp → 462 ≤ s₁.nv ∧ EdgeOK col σ₁) → Spec Hp (jp cm ()) s₁ σ₁ (fun _ _ _ => True) := by
    intro Hp cm s₁ σ₁ hpre
    simp (config := { zeta := false }) only [jp]
    refine spec_bind (spec_get (Q := fun st s₂ σ₂ => st = s₁ ∧ s₂ = s₁ ∧ σ₂ = σ₁)
      (fun _ _ _ => ⟨rfl, rfl, rfl⟩)) (fun st s₂ σ₂ => ?_)
    refine spec_bind (row1Block_spec col hsym k hc.row1 s₂ σ₂ _ (fun hH => ?_)) (fun _ s₃ σ₃ => ?_)
    · obtain ⟨hp, -, -, -, -, -, rfl, rfl⟩ := hH; exact hpre hp
    refine spec_bind (addCounting_spec col hsym cells.D o.tight o.budget o.channel hc.deg hc.iv hc.chan
      hc.bud s₃ σ₃ _ (fun hH => ?_)) (fun co s₄ σ₄ => ?_)
    · obtain ⟨⟨hp, -, -, -, -, -, rfl, rfl⟩, -, -, -, -, hs3, rfl⟩ := hH
      obtain ⟨h1, h2⟩ := hpre hp; exact ⟨by omega, h2⟩
    refine spec_bind (hBlock_spec col hsym k (normH H) hc.hunits s₄ σ₄ _ (fun hH => ?_)) (fun _ s₅ σ₅ => ?_)
    · exact ⟨hH.2.2.2.2.2.2.1, hH.2.2.2.2.2.2.2⟩
    refine spec_bind (wlexBlock_spec col hsym cells.wcells hc.wcellsIn hc.wlex s₅ σ₅ _ (fun hH => ?_))
      (fun _ s₆ σ₆ => ?_)
    · obtain ⟨⟨-, -, -, -, -, -, h1, h2⟩, -, -, -, -, hs5, rfl⟩ := hH
      exact ⟨by omega, h2⟩
    extract_lets jp3 jp2
    have hjp3 : ∀ (n : Nat) (Hr : Prop) (s₈ : St) (σ₈ : Nat → Bool),
        Spec Hr (jp3 n ()) s₈ σ₈ (fun _ _ _ => True) := by
      intro n Hr s₈ σ₈
      simp (config := { zeta := false }) only [jp3]
      extract_lets jp4
      rw [if_neg (by rw [hc.noShortfall]; simp)]
      exact spec_pure_bind (spec_pure (fun _ _ _ => trivial))
    have hjp2 : ∀ (Hq : Prop) (s₇ : St) (σ₇ : Nat → Bool), (Hq → 462 ≤ s₇.nv ∧ EdgeOK col σ₇) →
        Spec Hq (jp2 ()) s₇ σ₇ (fun _ _ _ => True) := by
      intro Hq s₇ σ₇ hq
      simp (config := { zeta := false }) only [jp2]
      cases ha : o.auth
      · rw [if_neg (by simp)]
        exact spec_pure_bind (hjp3 _ _ _ _)
      · rw [if_pos rfl]
        refine spec_bind (Q₁ := fun _ _ _ => True) ?_ (fun r s₈ σ₈ => spec_pure_bind (hjp3 _ _ _ _))
        refine spec_forIn_array (I := fun _ _ s' σ' => 462 ≤ s'.nv ∧ EdgeOK col σ') _ _ _
          (fun hH _ _ => hq hH) ?_ (fun _ _ _ _ _ _ => trivial)
        intro i hi n s₈ σ₈
        have hasg : (autos cl (normH H))[i] ∈ autos (nCellArrays cells) (normH H) :=
          Array.getElem_mem hi
        generalize (autos cl (normH H))[i] = asg at hasg ⊢
        dsimp only
        split
        · refine spec_bind (lexLeq_spec_gated col hsym (authPairs asg) s₈ σ₈ _ (fun hH => ?_))
            (fun _ s₉ σ₉ => spec_pure_bind (spec_pure (fun hH _ _ => ?_)))
          · exact ⟨authPairs_ok _ _ hc.ncellsNodup hc.ncellsIn asg hasg, hc.auth ha asg hasg, hH.2.1, hH.2.2⟩
          · obtain ⟨⟨-, h462, hE⟩, -, h89, ag89, -, -⟩ := hH
            exact ⟨by omega, EdgeOK.agree hE ag89 h462⟩
        · exact spec_pure_bind (spec_pure (fun hH _ _ => hH.2))
    have h6 : (After (After (After (After (After Hp s₁ σ₁ s₂ σ₂ (st = s₁ ∧ s₂ = s₁ ∧ σ₂ = σ₁))
        s₂ σ₂ s₃ σ₃ (s₃.nv = s₂.nv ∧ σ₃ = σ₂)) s₃ σ₃ s₄ σ₄
        (RyzOK col σ₄ s₄.nv 231 co.Ry co.Rz ∧ 462 ≤ s₄.nv ∧ EdgeOK col σ₄)) s₄ σ₄ s₅ σ₅
        (s₅.nv = s₄.nv ∧ σ₅ = σ₄)) s₅ σ₅ s₆ σ₆ (462 ≤ s₆.nv ∧ EdgeOK col σ₆)) →
        462 ≤ s₆.nv ∧ EdgeOK col σ₆ := fun h => h.2.2.2.2.2
    cases hw : o.wallpairs
    · rw [if_neg (by simp)]
      exact spec_pure_bind (hjp2 _ _ _ h6)
    · rw [if_pos rfl]
      refine spec_bind (wallBlock_spec col hsym cells.wcells hc.wcellsIn (hc.wall hw) s₆ σ₆ _ h6)
        (fun _ s₇ σ₇ => hjp2 _ _ _ (fun hH => hH.2.2.2.2.2))
  cases hb : o.baseCodegree
  · rw [if_neg (by simp)]
    refine spec_bind (edgeOnly_spec col hsym s σ _ (fun _ => ⟨hn, hE⟩)) (fun _ s₁ σ₁ => ?_)
    refine spec_pure_bind (hjp _ _ _ _ (fun hH => ?_))
    obtain ⟨-, -, -, -, -, hs1, rfl⟩ := hH
    exact ⟨by omega, hE⟩
  · rw [if_pos rfl]
    refine spec_bind (buildBase_spec col hsym (hc.capR hb) (hc.capB hb) s σ _ (fun _ => ⟨hn, hE⟩))
      (fun _ s₁ σ₁ => ?_)
    refine spec_pure_bind (hjp _ _ _ _ (fun hH => ?_))
    obtain ⟨-, -, h1, ag1, -, -⟩ := hH
    exact ⟨by omega, EdgeOK.agree hE ag1 hn⟩

theorem rootedFormula_sat_core (degs : List Nat) (k : Nat) (comp H : List (Nat × Nat)) (o : Opts)
    (F : Formula) (hF : rootedFormula 22 ["K2x8", "K2x5"] degs k comp H o = .ok F)
    (cells : Cells) (hcells : cellsOf 22 degs k comp = .ok cells)
    (col : Nat → Nat → Bool) (hc : CoreCanon col k cells (normH H) o) :
    ∃ σ, ClsSat σ F.clauses := by
  rw [rootedFormula_eq] at hF
  unfold rootedFormulaAlt at hF
  simp (config := { zeta := false }) only [parse_K2x8, parse_K2x5] at hF
  simp only [hcells] at hF
  have hok : (Except.ok cells : Except String Cells) = pure cells := rfl
  simp only [hok, pure_bind] at hF
  split at hF
  next com nv0 counts nauts sf st heq =>
    split at hF
    · cases hF
    · next herr =>
      have he : st.errs = #[] := by
        have : st.errs.isEmpty = true := by
          cases h : st.errs.isEmpty
          · rw [h] at herr; exact absurd rfl herr
          · rfl
        exact Array.isEmpty_iff.mp this
      have hFc : F.clauses = st.cls := by cases hF; rfl
      rw [hFc]
      have hinit : (22 * (22 - 1) / 2 * ["K2x8", "K2x5"].length : Nat) = 462 := by decide
      refine spec_run (progOf_spec k cells H o col hc _ (σE col) ?_ (agree_refl _ _)) heq he ⟨?_, ?_⟩
      · show 462 ≤ 22 * (22 - 1) / 2 * ["K2x8", "K2x5"].length; rw [hinit]; exact Nat.le_refl _
      · intro c hc'; simp at hc'
      · intro c hc'; simp at hc'

end SB.Rooted
#print axioms SB.Rooted.rootedFormula_sat_core
