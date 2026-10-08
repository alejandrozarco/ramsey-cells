/-
# M3: the codegree indicators, codegree counters and conditional intervals of `add_counting`

For every pair `i < j`: `y_w ↔ (iw, jw blue)`, `z_w ↔ (iw, jw red)` (`w ∉ {i,j}`, ascending), two
bidirectional counters `ry` (blue codegree `C_ij`) and `rz` (red codegree `R_ij`), and for each
colour `a ∈ {0,1}` of the pair the clauses `[cond, C ≥ bl]`, `[cond, C ≤ bh]`, `[cond, R ≥ rl]`,
`[cond, R ≤ rh]` (or the unit `[cond]` when the interval is empty), `cond` false exactly when the
pair has colour `a`. Satisfied when the pair's actual `(C, R)` lies in the interval the encoder
computes for its actual colour (`IvOK`, M1 Lemma 2.3 on the Mathlib side).
-/
import RootedBridge.Degree

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

/-- Common blue neighbours of `i, j` among `1..t`. -/
def cbList (col : Nat → Nat → Bool) (i j t : Nat) : List Nat :=
  (List.range' 1 t).filter (fun w => w != i && w != j && col i w && col j w)

/-- Common red neighbours of `i, j` among `1..t`. -/
def crList (col : Nat → Nat → Bool) (i j t : Nat) : List Nat :=
  (List.range' 1 t).filter (fun w => w != i && w != j && !col i w && !col j w)

/-- Blue and red codegree. -/
def Cb (col : Nat → Nat → Bool) (i j : Nat) : Nat := (cbList col i j 22).length
def Cr (col : Nat → Nat → Bool) (i j : Nat) : Nat := (crList col i j 22).length

/-- The budget `Λ_v` of `typed_encode.budget_of` at the prescribed degree. -/
def lamD (D : Array Nat) (v : Nat) : Int := budgetOf 22 4 7 ((D[v - 1]! : Nat) : Int)

/-- The pair's `(C, R)` lies in the interval the encoder computes for its actual colour. -/
def IvOK (col : Nat → Nat → Bool) (D : Array Nat) (tight : Bool) : Prop :=
  ∀ i j, 1 ≤ i → i < j → j ≤ 22 →
    let v := ivVals 22 4 7 (lamD D i) (lamD D j) ((D[i - 1]! : Nat) : Int) ((D[j - 1]! : Nat) : Int)
      tight (if col i j then 1 else 0)
    v.1 ≤ (Cb col i j : Int) ∧ (Cb col i j : Int) ≤ v.2.1 ∧
      v.2.2.1 ≤ (Cr col i j : Int) ∧ (Cr col i j : Int) ≤ v.2.2.2

/-- What a codegree counter tells about its last row (`i = 20`): `R(20, t) ↔ t ≤ C`. -/
def CntFacts (σ : Nat → Bool) (R : Counter) (kmax C n : Nat) : Prop :=
  (∀ t, (R.get? 20 t).isSome ↔ (1 ≤ t ∧ t ≤ min 20 kmax)) ∧
  (∀ t v, R.get? 20 t = some v → 0 < v ∧ v ≤ n ∧ σ v = decide (t ≤ C))

theorem CntFacts.agree {σ σ' : Nat → Bool} {R : Counter} {kmax C n m : Nat}
    (h : CntFacts σ R kmax C n) (hag : Agree σ σ' m) (hnm : n ≤ m) : CntFacts σ' R kmax C n :=
  ⟨h.1, fun t v hv => by
    obtain ⟨h1, h2, h3⟩ := h.2 t v hv
    exact ⟨h1, h2, by rw [hag v (by omega), h3]⟩⟩

theorem CntFacts.mono {σ : Nat → Bool} {R : Counter} {kmax C n m : Nat}
    (h : CntFacts σ R kmax C n) (hnm : n ≤ m) : CntFacts σ R kmax C m :=
  ⟨h.1, fun t v hv => by obtain ⟨h1, h2, h3⟩ := h.2 t v hv; exact ⟨h1, by omega, h3⟩⟩

theorem cntFacts_of_counterOK {σ : Nat → Bool} {xs : Array Int} {kmax lo hi C : Nat}
    (h : CounterOK σ xs kmax R lo hi) (hsz : xs.size = 20) (hc : cnt σ xs 20 = C) :
    CntFacts σ R kmax C hi := by
  refine ⟨fun t => ?_, fun t v hv => ?_⟩
  · rw [h.some_iff, hsz]; omega
  · obtain ⟨h1, h2⟩ := h.range _ _ _ hv
    refine ⟨by omega, h2, ?_⟩
    rw [h.val _ _ _ hv, hc]

end SB.Rooted

namespace SB.Rooted
open LRATCatcher.Rooted

/-- The join-point shape `if c then (x ← R.at; add (mk x); jp) else jp`. -/
theorem spec_optAt {β : Type} {c : Prop} [Decidable c] {H : Prop} {s : St} {σ : Nat → Bool}
    {Q : β → St → (Nat → Bool) → Prop} (R : Counter) (i j : Nat) (ctx : String)
    (mk : Int → Array Int) (jp : Unit → EncM β)
    (hadd : ∀ x, c → (∃ v, R.get? i j = some v ∧ x = (v : Int)) → H → Good s σ → s.errs = #[] →
      (∀ l ∈ mk x, l.natAbs ≤ s.nv) ∧ ClauseSat σ (mk x))
    (hjp : ∀ s' : St, s'.nv = s.nv → (s'.errs = #[] → s.errs = #[]) → Spec H (jp ()) s' σ Q) :
    Spec H (if c then (do let x ← R.at i j ctx; let y ← add (mk x); jp y)
      else (do let y ← pure PUnit.unit; jp y)) s σ Q := by
  split
  · next hc =>
    refine spec_at_bind' (fun s' x hnv hcls hfx => spec_add_bind' (fun hH hg he => ?_)
      (fun s'' hnv' hm => hjp s'' (by rw [hnv', hnv]) (fun he'' => ?_)))
    · obtain ⟨rfl, hx⟩ := hfx he
      exact hadd x hc hx hH hg he
    · have he' := hm he''
      exact (hfx he').1 ▸ he'
  · exact spec_pure_bind (hjp s rfl id)

theorem cond_facts (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) {σ : Nat → Bool}
    (hE : EdgeOK col σ) {i j : Nat} (hv : VPair i j) {a : Nat} (ha : a = 0 ∨ a = 1) :
    let cond := if (a == 1) = true then -varE 22 2 i j 2 else varE 22 2 i j 2
    cond ≠ 0 ∧ cond.natAbs ≤ 462 ∧ lv σ cond = !(decide ((if col i j then 1 else 0) = a)) := by
  intro cond
  have hb := varE_bounds hv (Or.inr rfl)
  have hl := lv_varE hsym hE hv (Or.inr rfl)
  simp only [colV, if_true] at hl
  rcases ha with rfl | rfl
  · simp only [cond, Nat.zero_ne_one, beq_iff_eq, if_false, Bool.false_eq_true]
    refine ⟨hb.2.2, hb.2.1, ?_⟩
    rw [hl]; cases col i j <;> simp
  · simp only [cond, beq_self_eq_true, if_true]
    refine ⟨by omega, by rw [Int.natAbs_neg]; exact hb.2.1, ?_⟩
    rw [lv_neg _ hb.2.2, hl]; cases col i j <;> simp

theorem ivEmit_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) {i j : Nat}
    (hv : VPair i j) (a : Nat) (ha : a = 0 ∨ a = 1) (ry rz : Counter) (C R n : Nat)
    (bl bh rl rh : Int)
    (hiv : (if col i j then 1 else 0) = a → bl ≤ C ∧ (C : Int) ≤ bh ∧ rl ≤ R ∧ (R : Int) ≤ rh)
    (s : St) (σ : Nat → Bool) (H : Prop)
    (hF : H → CntFacts σ ry 5 C n ∧ CntFacts σ rz 8 R n ∧ EdgeOK col σ ∧ n ≤ s.nv ∧ 462 ≤ s.nv) :
    Spec H (ivEmit 20 (varE 22 2 i j 2) a ry rz bl bh rl rh) s σ
      (fun _ s' σ' => s'.nv = s.nv ∧ σ' = σ) := by
  have hcf := fun σ' hE' => cond_facts col hsym (σ := σ') hE' hv ha
  unfold ivEmit
  by_cases hemp : (decide (bl > bh) || decide (rl > rh)) = true
  · rw [if_pos hemp]
    refine spec_add_bind (fun hH hg he => ?_) (spec_pure (fun _ _ _ => ⟨rfl, rfl⟩))
    obtain ⟨hry, hrz, hE, hn, h462⟩ := hF hH
    obtain ⟨c0, c1, c2⟩ := hcf σ hE
    refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
    · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
      subst hl; omega
    · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
      subst hl; exact c0
    · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
      rw [c2]
      by_cases hact : (if col i j then 1 else 0) = a
      · obtain ⟨h1, h2, h3, h4⟩ := hiv hact
        simp at hemp; omega
      · simp [hact]
  · rw [if_neg hemp]
    refine spec_pure_bind ?_
    refine spec_optAt (c := bl ≥ 1) ry 20 bl.toNat "intervals" _ _ ?_ (fun s₁ h₁ h₁' => ?_)
    · rintro x hc ⟨v, hv', rfl⟩ hH hg he
      obtain ⟨hry, hrz, hE, hn, h462⟩ := hF hH
      obtain ⟨c0, c1, c2⟩ := hcf σ hE
      obtain ⟨v0, vn, vv⟩ := hry.2 _ _ hv'
      refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
      · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_natCast]) <;> omega
      · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> omega
      · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
        rw [c2, lv_natCast _ v0, vv]
        by_cases hact : (if col i j then 1 else 0) = a
        · obtain ⟨h1, h2, h3, h4⟩ := hiv hact
          simp [hact]; omega
        · simp [hact]
    refine spec_optAt (c := bh + 1 ≤ ((20 : Nat) : Int)) ry 20 (bh + 1).toNat "intervals" _ _ ?_
      (fun s₂ h₂ h₂' => ?_)
    · rintro x hc ⟨v, hv', rfl⟩ hH hg he
      obtain ⟨hry, hrz, hE, hn, h462⟩ := hF hH
      obtain ⟨c0, c1, c2⟩ := hcf σ hE
      obtain ⟨v0, vn, vv⟩ := hry.2 _ _ hv'
      refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
      · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> omega
      · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> omega
      · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
        rw [c2, lv_neg_natCast _ v0, vv]
        by_cases hact : (if col i j then 1 else 0) = a
        · obtain ⟨h1, h2, h3, h4⟩ := hiv hact
          simp [hact]; omega
        · simp [hact]
    refine spec_optAt (c := rl ≥ 1) rz 20 rl.toNat "intervals" _ _ ?_ (fun s₃ h₃ h₃' => ?_)
    · rintro x hc ⟨v, hv', rfl⟩ hH hg he
      obtain ⟨hry, hrz, hE, hn, h462⟩ := hF hH
      obtain ⟨c0, c1, c2⟩ := hcf σ hE
      obtain ⟨v0, vn, vv⟩ := hrz.2 _ _ hv'
      refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
      · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_natCast]) <;> omega
      · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> omega
      · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
        rw [c2, lv_natCast _ v0, vv]
        by_cases hact : (if col i j then 1 else 0) = a
        · obtain ⟨h1, h2, h3, h4⟩ := hiv hact
          simp [hact]; omega
        · simp [hact]
    refine spec_optAt (c := rh + 1 ≤ ((20 : Nat) : Int)) rz 20 (rh + 1).toNat "intervals" _ _ ?_
      (fun s₄ h₄ h₄' => ?_)
    · rintro x hc ⟨v, hv', rfl⟩ hH hg he
      obtain ⟨hry, hrz, hE, hn, h462⟩ := hF hH
      obtain ⟨c0, c1, c2⟩ := hcf σ hE
      obtain ⟨v0, vn, vv⟩ := hrz.2 _ _ hv'
      refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
      · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> omega
      · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;> omega
      · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
        rw [c2, lv_neg_natCast _ v0, vv]
        by_cases hact : (if col i j then 1 else 0) = a
        · obtain ⟨h1, h2, h3, h4⟩ := hiv hact
          simp [hact]; omega
        · simp [hact]
    exact spec_pure (fun _ _ _ => ⟨by omega, rfl⟩)

end SB.Rooted

namespace SB.Rooted
open LRATCatcher.Rooted

/-- Facts of the codegree counters of the first `t` pairs. -/
def RyzOK (col : Nat → Nat → Bool) (σ : Nat → Bool) (n t : Nat) (Ry Rz : Array Counter) : Prop :=
  Ry.size = t ∧ Rz.size = t ∧ ∀ p (hp : p < t) (hp' : p < (edgesOf 22).size),
    CntFacts σ Ry[p]! 5 (Cb col (edgesOf 22)[p].1 (edgesOf 22)[p].2) n ∧
    CntFacts σ Rz[p]! 8 (Cr col (edgesOf 22)[p].1 (edgesOf 22)[p].2) n

theorem RyzOK.agree {col : Nat → Nat → Bool} {σ σ' : Nat → Bool} {n t m : Nat} {Ry Rz : Array Counter}
    (h : RyzOK col σ n t Ry Rz) (hag : Agree σ σ' m) (hnm : n ≤ m) : RyzOK col σ' n t Ry Rz :=
  ⟨h.1, h.2.1, fun p hp hp' => ⟨(h.2.2 p hp hp').1.agree hag hnm, (h.2.2 p hp hp').2.agree hag hnm⟩⟩

theorem RyzOK.mono {col : Nat → Nat → Bool} {σ : Nat → Bool} {n t m : Nat} {Ry Rz : Array Counter}
    (h : RyzOK col σ n t Ry Rz) (hnm : n ≤ m) : RyzOK col σ m t Ry Rz :=
  ⟨h.1, h.2.1, fun p hp hp' => ⟨(h.2.2 p hp hp').1.mono hnm, (h.2.2 p hp hp').2.mono hnm⟩⟩

theorem cbList_succ (col : Nat → Nat → Bool) (i j t : Nat) :
    cbList col i j (t + 1) = cbList col i j t ++
      (if (t + 1 != i && t + 1 != j && col i (t + 1) && col j (t + 1)) then [t + 1] else []) := by
  unfold cbList
  rw [List.range'_1_concat, List.filter_append]
  simp only [List.filter_cons, List.filter_nil]
  split <;> simp_all [Nat.add_comm]

theorem crList_succ (col : Nat → Nat → Bool) (i j t : Nat) :
    crList col i j (t + 1) = crList col i j t ++
      (if (t + 1 != i && t + 1 != j && !col i (t + 1) && !col j (t + 1)) then [t + 1] else []) := by
  unfold crList
  rw [List.range'_1_concat, List.filter_append]
  simp only [List.filter_cons, List.filter_nil]
  split <;> simp_all [Nat.add_comm]

/-- Invariant of the indicator loop of one pair `(i, j)` after the vertices `1..t`. -/
def WInv (col : Nat → Nat → Bool) (i j n₀ t : Nat) (yz : MProd (Array Int) (Array Int)) (s : St)
    (σ : Nat → Bool) : Prop :=
  n₀ ≤ s.nv ∧ EdgeOK col σ ∧
  (∀ l ∈ yz.1, l ≠ 0 ∧ l.natAbs ≤ s.nv) ∧ (∀ l ∈ yz.2, l ≠ 0 ∧ l.natAbs ≤ s.nv) ∧
  cnt σ yz.1 yz.1.size = (cbList col i j t).length ∧ cnt σ yz.2 yz.2.size = (crList col i j t).length ∧
  yz.1.size = ((List.range' 1 t).filter (fun w => ![i, j].contains w)).length ∧
  yz.2.size = ((List.range' 1 t).filter (fun w => ![i, j].contains w)).length

theorem filter2_succ (i j t : Nat) :
    ((List.range' 1 (t + 1)).filter (fun w => ![i, j].contains w)).length =
      ((List.range' 1 t).filter (fun w => ![i, j].contains w)).length +
        (if (t + 1 == i || t + 1 == j) = true then 0 else 1) := by
  rw [List.range'_1_concat, List.filter_append]
  simp only [List.filter_cons, List.filter_nil, List.length_append]
  by_cases h1 : t + 1 = i <;> by_cases h2 : t + 1 = j <;> simp [h1, h2, Nat.add_comm]

/-- The literal facts used by the indicator clauses of `(i, j)` at `w`. -/
theorem lit_ijw (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) {σ : Nat → Bool}
    (hE : EdgeOK col σ) {i j w : Nat} (hi1 : 1 ≤ i) (hij : i < j) (hj2 : j ≤ 22) (hw1 : 1 ≤ w)
    (hw2 : w ≤ 22) (hwi : w ≠ i) (hwj : w ≠ j) (c : Nat) (hc : c = 1 ∨ c = 2) :
    varE 22 2 i w c ≠ 0 ∧ (varE 22 2 i w c).natAbs ≤ 462 ∧ lv σ (varE 22 2 i w c) = colV col i w c ∧
    varE 22 2 j w c ≠ 0 ∧ (varE 22 2 j w c).natAbs ≤ 462 ∧ lv σ (varE 22 2 j w c) = colV col j w c := by
  have hvi : VPair i w := ⟨hi1, by omega, hw1, hw2, by omega⟩
  have hvj : VPair j w := ⟨by omega, hj2, hw1, hw2, by omega⟩
  have bi := varE_bounds hvi hc
  have bj := varE_bounds hvj hc
  exact ⟨bi.2.2, bi.2.1, lv_varE hsym hE hvi hc, bj.2.2, bj.2.1, lv_varE hsym hE hvj hc⟩

theorem ivLoop2_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) (D : Array Nat)
    (tight : Bool) (hiv : IvOK col D tight) (s : St) (σ : Nat → Bool) (H : Prop)
    (hpre : H → 462 ≤ s.nv ∧ EdgeOK col σ) :
    Spec H (ivLoop2 22 4 7 D tight) s σ
      (fun RR s' σ' => RyzOK col σ' s'.nv 231 RR.1 RR.2 ∧ 462 ≤ s'.nv ∧ EdgeOK col σ') := by
  unfold ivLoop2
  dsimp only
  refine spec_bind (Q₁ := fun RR s' σ' => RyzOK col σ' s'.nv 231 RR.1 RR.2 ∧ 462 ≤ s'.nv ∧
      EdgeOK col σ') ?_ (fun RR s' σ' => spec_pure (fun hH _ _ => hH.2.2.2.2.2))
  refine spec_forIn_array (I := fun p RR s' σ' => RyzOK col σ' s'.nv p RR.1 RR.2 ∧ 462 ≤ s'.nv ∧
      EdgeOK col σ') _ _ _ ?_ ?_ ?_
  · intro hH _ _
    exact ⟨⟨rfl, rfl, fun p hp => absurd hp (by omega)⟩, (hpre hH).1, (hpre hH).2⟩
  · intro p hp RR s₁ σ₁
    obtain ⟨hi1, hij, hj2, hidx⟩ := edgesOf_getElem hp
    generalize hpe : (edgesOf 22)[p] = e at hi1 hij hj2 hidx ⊢
    obtain ⟨i, j⟩ := e
    dsimp only at hi1 hij hj2 hidx ⊢
    refine spec_bind (Q₁ := fun yz s₂ σ₂ => WInv col i j s₁.nv 22 yz s₂ σ₂) ?_ ?_
    · refine spec_forIn_range (I := fun t yz s₂ σ₂ => WInv col i j s₁.nv t yz s₂ σ₂) 1 (22 + 1) _ _
        ?_ ?_ (fun _ _ _ _ _ h => h)
      · intro hH _ _
        exact ⟨Nat.le_refl _, hH.2.2.2, by simp, by simp, by simp [cnt, cbList],
          by simp [cnt, crList], by simp, by simp⟩
      · intro t ht yz s₂ σ₂
        have hw1 : 1 ≤ 1 + t := by omega
        have hw2 : 1 + t ≤ 22 := by omega
        rw [show 1 + t = t + 1 from Nat.add_comm _ _] at hw1 hw2 ⊢
        split
        · next hc =>
          refine spec_pure (fun hH _ _ => ?_)
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hH.2
          have hc' : (t + 1 = i ∨ t + 1 = j) := by simp at hc; omega
          refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_⟩
          · rw [h5, cbList_succ, if_neg (by simp; omega), List.append_nil]
          · rw [h6, crList_succ, if_neg (by simp; omega), List.append_nil]
          · rw [h7, filter2_succ, if_pos hc, Nat.add_zero]
          · rw [h8, filter2_succ, if_pos hc, Nat.add_zero]
        · next hc =>
          have hwi : t + 1 ≠ i := by simp at hc; omega
          have hwj : t + 1 ≠ j := by simp at hc; omega
          refine spec_pure_bind (spec_fresh_bind (col i (t + 1) && col j (t + 1)) ?_)
          refine spec_add_bind (fun hH hg he => ?_) ?_
          · obtain ⟨⟨-, -, h462, -⟩, h0, h1, -⟩ := hH
            have hE' := EdgeOK.agree h1 (agree_upd σ₂ s₂.nv (col i (t + 1) && col j (t + 1))) (by omega)
            obtain ⟨a0, a1, a2, b0, b1, b2⟩ := lit_ijw col hsym hE' hi1 hij hj2 hw1 hw2 hwi hwj 2 (by omega)
            refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
            · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> (try simp) <;> omega
            · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl | rfl <;> omega
            · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
              simp only [lv_neg _ a0, lv_neg _ b0, a2, b2, lv_neg_natCast _ (Nat.succ_pos _),
                lv_natCast _ (Nat.succ_pos _), colV, upd]
              cases col i (t + 1) <;> cases col j (t + 1) <;> simp
          refine spec_add_bind (fun hH hg he => ?_) ?_
          · obtain ⟨⟨-, -, h462, -⟩, h0, h1, -⟩ := hH
            have hE' := EdgeOK.agree h1 (agree_upd σ₂ s₂.nv (col i (t + 1) && col j (t + 1))) (by omega)
            obtain ⟨a0, a1, a2, b0, b1, b2⟩ := lit_ijw col hsym hE' hi1 hij hj2 hw1 hw2 hwi hwj 2 (by omega)
            refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
            · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> (try simp) <;> omega
            · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl <;> omega
            · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
              simp only [lv_neg _ a0, lv_neg _ b0, a2, b2, lv_neg_natCast _ (Nat.succ_pos _),
                lv_natCast _ (Nat.succ_pos _), colV, upd]
              cases col i (t + 1) <;> cases col j (t + 1) <;> simp
          refine spec_add_bind (fun hH hg he => ?_) ?_
          · obtain ⟨⟨-, -, h462, -⟩, h0, h1, -⟩ := hH
            have hE' := EdgeOK.agree h1 (agree_upd σ₂ s₂.nv (col i (t + 1) && col j (t + 1))) (by omega)
            obtain ⟨a0, a1, a2, b0, b1, b2⟩ := lit_ijw col hsym hE' hi1 hij hj2 hw1 hw2 hwi hwj 2 (by omega)
            refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
            · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> (try simp) <;> omega
            · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl <;> omega
            · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
              simp only [lv_neg _ a0, lv_neg _ b0, a2, b2, lv_neg_natCast _ (Nat.succ_pos _),
                lv_natCast _ (Nat.succ_pos _), colV, upd]
              cases col i (t + 1) <;> cases col j (t + 1) <;> simp
          refine spec_fresh_bind (!col i (t + 1) && !col j (t + 1)) ?_
          refine spec_add_bind (fun hH hg he => ?_) ?_
          · obtain ⟨⟨-, -, h462, -⟩, h0, h1, -⟩ := hH
            have hE' := EdgeOK.agree h1 (agree_trans (agree_upd σ₂ s₂.nv (col i (t + 1) && col j (t + 1))) (agree_upd _ (s₂.nv + 1) (!col i (t + 1) && !col j (t + 1))) (Nat.le_succ _)) (by omega)
            obtain ⟨a0, a1, a2, b0, b1, b2⟩ := lit_ijw col hsym hE' hi1 hij hj2 hw1 hw2 hwi hwj 1 (by omega)
            refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
            · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> (try simp) <;> omega
            · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl | rfl <;> omega
            · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
              simp only [lv_neg _ a0, lv_neg _ b0, a2, b2, lv_neg_natCast _ (Nat.succ_pos _),
                lv_natCast _ (Nat.succ_pos _), colV, upd]
              cases col i (t + 1) <;> cases col j (t + 1) <;> simp
          refine spec_add_bind (fun hH hg he => ?_) ?_
          · obtain ⟨⟨-, -, h462, -⟩, h0, h1, -⟩ := hH
            have hE' := EdgeOK.agree h1 (agree_trans (agree_upd σ₂ s₂.nv (col i (t + 1) && col j (t + 1))) (agree_upd _ (s₂.nv + 1) (!col i (t + 1) && !col j (t + 1))) (Nat.le_succ _)) (by omega)
            obtain ⟨a0, a1, a2, b0, b1, b2⟩ := lit_ijw col hsym hE' hi1 hij hj2 hw1 hw2 hwi hwj 1 (by omega)
            refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
            · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> (try simp) <;> omega
            · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl <;> omega
            · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
              simp only [lv_neg _ a0, lv_neg _ b0, a2, b2, lv_neg_natCast _ (Nat.succ_pos _),
                lv_natCast _ (Nat.succ_pos _), colV, upd]
              cases col i (t + 1) <;> cases col j (t + 1) <;> simp
          refine spec_add_bind (fun hH hg he => ?_) ?_
          · obtain ⟨⟨-, -, h462, -⟩, h0, h1, -⟩ := hH
            have hE' := EdgeOK.agree h1 (agree_trans (agree_upd σ₂ s₂.nv (col i (t + 1) && col j (t + 1))) (agree_upd _ (s₂.nv + 1) (!col i (t + 1) && !col j (t + 1))) (Nat.le_succ _)) (by omega)
            obtain ⟨a0, a1, a2, b0, b1, b2⟩ := lit_ijw col hsym hE' hi1 hij hj2 hw1 hw2 hwi hwj 1 (by omega)
            refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
            · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> (try simp) <;> omega
            · simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl <;> omega
            · simp only [List.toList_toArray, List.any_cons, List.any_nil, Bool.or_false]
              simp only [lv_neg _ a0, lv_neg _ b0, a2, b2, lv_neg_natCast _ (Nat.succ_pos _),
                lv_natCast _ (Nat.succ_pos _), colV, upd]
              cases col i (t + 1) <;> cases col j (t + 1) <;> simp
          refine spec_pure (fun hH _ _ => ?_)
          obtain ⟨⟨-, -, h462, -⟩, h0, h1, h2, h3, h4, h5, h6, h7⟩ := hH
          have ag := agree_trans (agree_upd σ₂ s₂.nv (col i (t + 1) && col j (t + 1)))
            (agree_upd _ (s₂.nv + 1) (!col i (t + 1) && !col j (t + 1))) (Nat.le_succ _)
          refine ⟨by simp; omega, EdgeOK.agree h1 ag (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro l hl
            rcases Array.mem_push.mp hl with hl | rfl
            · exact ⟨(h2 l hl).1, by have := (h2 l hl).2; simp; omega⟩
            · exact ⟨by omega, by rw [Int.natAbs_natCast]; dsimp only; omega⟩
          · intro l hl
            rcases Array.mem_push.mp hl with hl | rfl
            · exact ⟨(h3 l hl).1, by have := (h3 l hl).2; simp; omega⟩
            · exact ⟨by omega, by rw [Int.natAbs_natCast]; dsimp only; omega⟩
          · rw [Array.size_push, cnt_push, cnt_congr ag (fun l hl => (h2 l hl).2), h4, cbList_succ,
              lv_natCast _ (Nat.succ_pos _)]
            simp only [upd, if_neg (show s₂.nv + 1 ≠ s₂.nv + 1 + 1 by omega), if_pos]
            simp [hwi, hwj]
            cases col i (t + 1) <;> cases col j (t + 1) <;> simp
          · rw [Array.size_push, cnt_push, cnt_congr ag (fun l hl => (h3 l hl).2), h5, crList_succ,
              lv_natCast _ (Nat.succ_pos _)]
            simp only [upd, if_pos]
            simp [hwi, hwj]
            cases col i (t + 1) <;> cases col j (t + 1) <;> simp
          · rw [Array.size_push, h6, filter2_succ, if_neg hc]
          · rw [Array.size_push, h7, filter2_succ, if_neg hc]
    · intro yz s₂ σ₂
      refine spec_bind (bidirCounter_spec yz.1 _ s₂ σ₂ _ (fun hH => by
        obtain ⟨-, -, -, -, -, ⟨-, -, h2, -⟩⟩ := hH
        exact h2)) (fun ry s₃ σ₃ => ?_)
      refine spec_bind (bidirCounter_spec yz.2 _ s₃ σ₃ _ (fun hH => fun l hl => ?_)) (fun rz s₄ σ₄ => ?_)
      · obtain ⟨⟨-, -, -, -, -, ⟨-, -, -, h3, -⟩⟩, -, h23, -⟩ := hH
        exact ⟨(h3 l hl).1, by have := (h3 l hl).2; omega⟩
      -- the facts available after both counters
      have key : After (After (After (H ∧ RyzOK col σ₁ s₁.nv p RR.fst RR.snd ∧ 462 ≤ s₁.nv ∧
            EdgeOK col σ₁) s₁ σ₁ s₂ σ₂ (WInv col i j s₁.nv 22 yz s₂ σ₂)) s₂ σ₂ s₃ σ₃
            (CounterOK σ₃ yz.fst (min (22 - 2) (4 + 1)) ry s₂.nv s₃.nv)) s₃ σ₃ s₄ σ₄
            (CounterOK σ₄ yz.snd (min (22 - 2) (7 + 1)) rz s₃.nv s₄.nv) →
          H ∧ RyzOK col σ₄ s₄.nv p RR.fst RR.snd ∧ 462 ≤ s₄.nv ∧ EdgeOK col σ₄ ∧
            CntFacts σ₄ ry 5 (Cb col i j) s₄.nv ∧ CntFacts σ₄ rz 8 (Cr col i j) s₄.nv := by
        intro hH
        obtain ⟨⟨⟨⟨hH0, hR, h462, hE₁⟩, -, h12, ag12, -, hW⟩, -, h23, ag23, -, hC3⟩, -, h34, ag34, -,
          hC4⟩ := hH
        obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8⟩ := hW
        have hsz1 : yz.1.size = 20 := by rw [w7]; exact filter_twenty hi1 hij hj2
        have hsz2 : yz.2.size = 20 := by rw [w8]; exact filter_twenty hi1 hij hj2
        have ag24 := agree_trans ag23 ag34 h23
        have ag14 := agree_trans (agree_trans ag12 ag23 h12) ag34 (by omega)
        refine ⟨hH0, (hR.agree ag14 (Nat.le_refl _)).mono (by omega), by omega,
          EdgeOK.agree hE₁ ag14 (by omega), ?_, ?_⟩
        · have c3 := cntFacts_of_counterOK hC3 hsz1
            (by rw [← hsz1, cnt_congr (agree_trans ag23 (agree_refl _ _) (Nat.le_refl _))
              (fun l hl => (w3 l hl).2), w5])
          exact (c3.agree ag34 (Nat.le_refl _)).mono h34
        · exact cntFacts_of_counterOK hC4 hsz2
            (by rw [← hsz2, cnt_congr ag24 (fun l hl => (w4 l hl).2), w6]; rfl)
      simp only [ivBodyOrig_eq]
      have hv : VPair i j := ⟨hi1, by omega, by omega, hj2, by omega⟩
      refine spec_bind (Q₁ := fun _ s₅ σ₅ => s₅.nv = s₄.nv ∧ σ₅ = σ₄) ?_ ?_
      · refine spec_forIn [0, 1] _ _ (fun _ _ s₅ σ₅ => s₅.nv = s₄.nv ∧ σ₅ = σ₄)
          (fun _ _ _ => ⟨rfl, rfl⟩) ?_ (fun _ _ _ _ _ h => h)
        intro k hk _ s₅ σ₅
        have ha : [0, 1][k] = 0 ∨ [0, 1][k] = 1 := by
          simp at hk; rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> simp
        generalize [0, 1][k] = a at ha ⊢
        unfold ivStep
        have hiv' : let V := (ivVals 22 4 7 (budgetOf 22 4 7 ((D[i - 1]! : Nat) : Int)) (budgetOf 22 4 7 ((D[j - 1]! : Nat) : Int)) ((D[i - 1]! : Nat) : Int) ((D[j - 1]! : Nat) : Int) tight a)
            (if col i j then 1 else 0) = a →
            V.1 ≤ (Cb col i j : Int) ∧ (Cb col i j : Int) ≤ V.2.1 ∧ V.2.2.1 ≤ (Cr col i j : Int) ∧
              (Cr col i j : Int) ≤ V.2.2.2 := by
          intro V hact
          subst hact
          exact hiv i j hi1 hij hj2
        refine spec_conseq (ivEmit_spec col hsym hv a ha ry rz (Cb col i j) (Cr col i j) s₄.nv _ _ _ _
          hiv' s₅ σ₅ _ (fun hH => ?_)) (fun h => h) (fun x s' σ' hH _ _ _ _ hq => ?_)
        · obtain ⟨hp, hs5, hσ5⟩ := hH
          obtain ⟨-, -, h462, hE4, c1, c2⟩ := key hp
          rw [hσ5]
          exact ⟨c1, c2, hE4, by omega, by omega⟩
        · obtain ⟨hp, hs5, hσ5⟩ := hH
          obtain ⟨h1, h2⟩ := hq
          cases x <;> exact ⟨by omega, by rw [h2, hσ5]⟩
      · intro _ s₅ σ₅
        refine spec_pure_bind (spec_pure (fun hH _ _ => ?_))
        obtain ⟨hp, -, -, -, -, hs5, hσ5⟩ := hH
        obtain ⟨-, ⟨hRs1, hRs2, hR⟩, h462, hE4, c1, c2⟩ := key hp
        rw [hσ5]
        refine ⟨⟨by simp [hRs1], by simp [hRs2], fun p' hp' hp'' => ?_⟩, by omega, hE4⟩
        rw [hs5]
        by_cases hlt : p' < p
        · rw [getElem!_pos _ p' (by simp; omega), getElem!_pos _ p' (by simp; omega),
            Array.getElem_push_lt (by omega), Array.getElem_push_lt (by omega)]
          have := hR p' hlt hp''
          rw [getElem!_pos _ p' (by omega), getElem!_pos _ p' (by omega)] at this
          exact this
        · have hpp : p' = p := by omega
          subst hpp
          rw [getElem!_pos _ p' (by simp; omega), getElem!_pos _ p' (by simp; omega)]
          have e1 : (RR.fst.push ry)[p']'(by simp; omega) = ry := by
            simp only [show p' = RR.fst.size by omega, Array.getElem_push_eq]
          have e2 : (RR.snd.push rz)[p']'(by simp; omega) = rz := by
            simp only [show p' = RR.snd.size by omega, Array.getElem_push_eq]
          rw [e1, e2, hpe]
          exact ⟨c1, c2⟩
  · intro RR s' σ' _ _ h
    rw [edgesOf_size] at h
    exact h

end SB.Rooted

#print axioms SB.Rooted.ivEmit_spec
#print axioms SB.Rooted.ivLoop2_spec
