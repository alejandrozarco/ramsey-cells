/-
# M4, part 2: degrees, root and the cell-ordered relabelling

`exists_relabel`: for every good colouring `b` of `K_22` there is a census case
`(n8, n9, n10, v8, v9, v10)` (its histogram, the root degree `k = rootOf n8 n10` and the composition
of a root of that degree) such that, for every `cells` meeting `CellsSem` for that case, some
relabelling `π` puts the root at vertex `0`, its blue neighbours at `1..k`, and gives every vertex `x`
the blue degree `cells.D[x]`.

Degrees come from `Colouring.degree_in_eight_nine_ten` and the histogram from
`Colouring.histogram_membership` (Lemma 1.2 and the class bounds; `Lemma12.lean`). The relabelling
is `Equiv.ofFiberEquiv` over the class map `vertex ↦ (role, degree)` (role: root / neighbour /
non-neighbour), whose fibres have the same sizes on positions and on vertices.
-/
import RootedM4.Cells

set_option linter.unusedVariables false

namespace SB.Rooted.M4
open LRATCatcher.Rooted SB.Rooted SB Finset

/-- Row 1 of a cube: the root `0` is blue to exactly `1..k`. -/
def Row1 (a : EColouring 22 2) (k : Nat) : Prop :=
  ∀ u : Fin 22, (h : (0 : Fin 22) ≠ u) → (a (mkEdge 0 u h) = 1 ↔ u.val ≤ k)

/-- Exact degrees of a cube. -/
def DegEq (a : EColouring 22 2) (cells : Cells) : Prop :=
  ∀ v : Fin 22, deg a 1 v = cells.D[v.val]!

theorem deg_eq_card (b : EColouring 22 2) (v : Fin 22) :
    deg b 1 v = ((kOf b).blueNbr v).card := by
  have := Colouring.deg_toE_one (kOf b) v
  rwa [toE_kOf] at this

theorem kOf_C_iff (b : EColouring 22 2) {x y : Fin 22} (h : x ≠ y) :
    (kOf b).C x y = true ↔ b (mkEdge x y h) = 1 := by
  rw [kOf_C, dif_neg h]; simp

theorem card_filter_split {α : Type*} [Fintype α] [DecidableEq α] (P A B : α → Prop)
    [DecidablePred P] [DecidablePred A] [DecidablePred B] :
    (univ.filter P).card = (univ.filter (fun x => P x ∧ A x)).card +
      (univ.filter (fun x => P x ∧ ¬ A x ∧ B x)).card +
      (univ.filter (fun x => P x ∧ ¬ A x ∧ ¬ B x)).card := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : P x <;> by_cases ha : A x <;> by_cases hb : B x <;> simp [hp, ha, hb]

theorem card_filter_three {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) (f : α → Nat)
    (hs : ∀ x ∈ s, f x = 8 ∨ f x = 9 ∨ f x = 10) :
    s.card = (s.filter (fun x => f x = 8)).card + (s.filter (fun x => f x = 9)).card +
      (s.filter (fun x => f x = 10)).card := by
  have h1 : s.card = ∑ x ∈ s, 1 := by simp
  rw [h1]
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rcases hs x hx with h | h | h <;> simp [h]

theorem pick_of_mem {d : Nat} (hd : d = 8 ∨ d = 9 ∨ d = 10) : d ∈ [8, 9, 10] := by
  rcases hd with rfl | rfl | rfl <;> simp

theorem mkEdge_congr_root (π : Equiv.Perm (Fin 22)) {r : Fin 22} (h0 : π 0 = r) {u : Fin 22}
    (h : π 0 ≠ π u) : mkEdge (π 0) (π u) h = mkEdge r (π u) (h0 ▸ h) := by
  subst h0; rfl

/-- The role of a position: `0` the root, `1` a neighbour (`1..k`), `2` a non-neighbour. -/
def roleP (k : Nat) (x : Fin 22) : Nat := if x.val = 0 then 0 else if x.val ≤ k then 1 else 2

theorem roleP_lt (k : Nat) (x : Fin 22) : roleP k x < 3 := by unfold roleP; split_ifs <;> omega

theorem roleP_zero (k : Nat) (x : Fin 22) : roleP k x = 0 ↔ x.val = 0 := by
  unfold roleP; by_cases h1 : x.val = 0 <;> by_cases h2 : x.val ≤ k <;> simp [h1, h2]

theorem roleP_one (k : Nat) (x : Fin 22) : roleP k x = 1 ↔ x.val ≠ 0 ∧ x.val ≤ k := by
  unfold roleP; by_cases h1 : x.val = 0 <;> by_cases h2 : x.val ≤ k <;> simp [h1, h2]

theorem roleP_two (k : Nat) (x : Fin 22) : roleP k x = 2 ↔ x.val ≠ 0 ∧ ¬ x.val ≤ k := by
  unfold roleP; by_cases h1 : x.val = 0 <;> by_cases h2 : x.val ≤ k <;> simp [h1, h2]

/-- The role of a vertex relative to the root `r`. -/
def roleV (K : Colouring 22) (r v : Fin 22) : Nat := if v = r then 0 else if K.C r v = true then 1 else 2

theorem roleV_lt (K : Colouring 22) (r v : Fin 22) : roleV K r v < 3 := by
  unfold roleV; split_ifs <;> omega

theorem roleV_zero (K : Colouring 22) (r v : Fin 22) : roleV K r v = 0 ↔ v = r := by
  unfold roleV; by_cases h1 : v = r <;> by_cases h2 : K.C r v = true <;> simp [h1, h2]

theorem roleV_one (K : Colouring 22) (r v : Fin 22) :
    roleV K r v = 1 ↔ v ≠ r ∧ K.C r v = true := by
  unfold roleV; by_cases h1 : v = r <;> by_cases h2 : K.C r v = true <;> simp [h1, h2]

theorem roleV_two (K : Colouring 22) (r v : Fin 22) :
    roleV K r v = 2 ↔ v ≠ r ∧ ¬ K.C r v = true := by
  unfold roleV; by_cases h1 : v = r <;> by_cases h2 : K.C r v = true <;> simp [h1, h2]

/-- **Degrees, root and the cell-ordered relabelling.** -/
theorem exists_relabel (b : EColouring 22 2) (hred : NoKst b 0 2 8) (hblue : NoKst b 1 2 5) :
    ∃ n8 n9 n10 v8 v9 v10 : Nat, ValidCase n8 n9 n10 v8 v9 v10 ∧
      ∀ cells : Cells, CellsSem n8 n9 n10 v8 v9 v10 cells →
        ∃ π : Equiv.Perm (Fin 22), Row1 (actV π b) (rootOf n8 n10) ∧ DegEq (actV π b) cells := by
  classical
  have hG : (kOf b).Good 4 7 :=
    Colouring.good_of_NoKst (kOf b) (by rw [toE_kOf]; exact hblue) (by rw [toE_kOf]; exact hred)
  have hdeg : ∀ v, ((kOf b).blueNbr v).card = 8 ∨ ((kOf b).blueNbr v).card = 9 ∨
      ((kOf b).blueNbr v).card = 10 :=
    fun v => (kOf b).degree_in_eight_nine_ten hG.1 hG.2 rfl v
  obtain ⟨hsum, h8, h10, h9e⟩ := (kOf b).histogram_membership hG.1 hG.2 rfl
  generalize hK : kOf b = K at hG hdeg hsum h8 h10 h9e
  generalize hdg : (fun v => (K.blueNbr v).card) = dg
  have hdgv : ∀ v, (K.blueNbr v).card = dg v := fun v => by rw [← hdg]
  simp only [hdgv] at hdeg hsum h8 h10 h9e
  generalize hn8 : (univ.filter (fun y => dg y = 8)).card = n8 at hsum h8 h10 h9e
  generalize hn9 : (univ.filter (fun y => dg y = 9)).card = n9 at hsum h8 h10 h9e
  generalize hn10 : (univ.filter (fun y => dg y = 10)).card = n10 at hsum h8 h10 h9e
  have hkm := rootOf_mem n8 n10
  generalize hk : rootOf n8 n10 = k at hkm
  -- a root of degree k
  obtain ⟨r, hr⟩ : ∃ r, dg r = k := by
    by_cases a8 : 0 < n8
    · rw [← hn8] at a8
      obtain ⟨r, hr⟩ := Finset.card_pos.mp a8
      refine ⟨r, ?_⟩
      rw [← hk]; unfold rootOf; rw [if_pos (by rw [← hn8]; exact a8)]
      exact (Finset.mem_filter.mp hr).2
    · by_cases a10 : 0 < n10
      · rw [← hn10] at a10
        obtain ⟨r, hr⟩ := Finset.card_pos.mp a10
        refine ⟨r, ?_⟩
        rw [← hk]; unfold rootOf; rw [if_neg a8, if_pos (by rw [← hn10]; exact a10)]
        exact (Finset.mem_filter.mp hr).2
      · have a9 : 0 < n9 := by omega
        rw [← hn9] at a9
        obtain ⟨r, hr⟩ := Finset.card_pos.mp a9
        refine ⟨r, ?_⟩
        rw [← hk]; unfold rootOf; rw [if_neg a8, if_neg a10]
        exact (Finset.mem_filter.mp hr).2
  -- the composition and the W-counts
  let nu : Nat → Nat := fun d => (univ.filter (fun v => dg v = d ∧ ¬ v = r ∧ K.C r v = true)).card
  let wc : Nat → Nat := fun d => (univ.filter (fun v => dg v = d ∧ ¬ v = r ∧ ¬ K.C r v = true)).card
  have hsplit : ∀ d, (univ.filter (fun y => dg y = d)).card = ind d k + nu d + wc d := by
    intro d
    rw [card_filter_split (fun y => dg y = d) (fun v => v = r) (fun v => K.C r v = true)]
    congr 2
    have : univ.filter (fun x => dg x = d ∧ x = r) = if d = k then {r} else ∅ := by
      ext x
      by_cases h : d = k
      · rw [if_pos h]; subst h
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro rfl; exact ⟨hr, rfl⟩
      · rw [if_neg h]
        simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
        rintro hx rfl; exact h (hx ▸ hr.symm ▸ rfl)
    rw [this, ind]; split_ifs <;> simp
  have hnuS : nu 8 + nu 9 + nu 10 = k := by
    have hc : (K.blueNbr r).card = k := by rw [hdgv]; exact hr
    have h3 := card_filter_three (K.blueNbr r) dg (fun x _ => hdeg x)
    rw [hc] at h3
    have e : ∀ d, ((K.blueNbr r).filter (fun x => dg x = d)).card = nu d := by
      intro d; congr 1; ext v
      simp only [Colouring.blueNbr, mem_filter, mem_univ, true_and]
      tauto
    rw [e, e, e] at h3; omega
  have hpar : (n8 + n10) % 2 = 0 := by obtain ⟨j, hj⟩ := h9e; omega
  have hs8 : n8 = ind 8 k + nu 8 + wc 8 := by rw [← hn8]; exact hsplit 8
  have hs9 : n9 = ind 9 k + nu 9 + wc 9 := by rw [← hn9]; exact hsplit 9
  have hs10 : n10 = ind 10 k + nu 10 + wc 10 := by rw [← hn10]; exact hsplit 10
  have hvalid : ValidCase n8 n9 n10 (nu 8) (nu 9) (nu 10) :=
    ⟨by omega, by omega, hsum, hpar, by rw [hk]; exact hnuS, by rw [hk]; omega, by rw [hk]; omega,
      by rw [hk]; omega⟩
  refine ⟨n8, n9, n10, nu 8, nu 9, nu 10, hvalid, fun cells hc => ?_⟩
  rw [hk]
  have hcN : ∀ d ∈ [8, 9, 10], cntN cells.D k d = pick (nu 8) (nu 9) (nu 10) d := by
    intro d hd; have := hc.cntN d hd; rwa [hk] at this
  have hcW : ∀ d ∈ [8, 9, 10], cntW cells.D k d = pick n8 n9 n10 d - ind d k - pick (nu 8) (nu 9) (nu 10) d := by
    intro d hd; have := hc.cntW d hd; rwa [hk] at this
  -- the class maps
  let pc : Fin 22 → Nat × Nat := fun x => (roleP k x, cells.D[x.val]!)
  let vc : Fin 22 → Nat × Nat := fun v => (roleV K r v, dg v)
  have hrangeD : ∀ x : Fin 22, cells.D[x.val]! = 8 ∨ cells.D[x.val]! = 9 ∨ cells.D[x.val]! = 10 :=
    fun x => hc.range x.val x.isLt
  have hroot : cells.D[(0 : Fin 22).val]! = k := by have := hc.root; rwa [hk] at this
  -- position counts
  have hposN : ∀ d, (univ.filter (fun x : Fin 22 => x.val ≠ 0 ∧ x.val ≤ k ∧ cells.D[x.val]! = d)).card =
      cntN cells.D k d := by
    intro d; unfold cntN
    rw [count_fin (fun x : Fin 22 => x.val ≠ 0 ∧ x.val ≤ k ∧ cells.D[x.val]! = d)]
    intro x
    simp only [Nat.add_sub_cancel, Array.getElem!_toList]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    constructor <;> intro h <;> omega
  have hposW : ∀ d, (univ.filter (fun x : Fin 22 => x.val ≠ 0 ∧ ¬ x.val ≤ k ∧ cells.D[x.val]! = d)).card =
      cntW cells.D k d := by
    intro d; unfold cntW
    rw [count_fin (fun x : Fin 22 => x.val ≠ 0 ∧ ¬ x.val ≤ k ∧ cells.D[x.val]! = d)]
    intro x
    simp only [Nat.add_sub_cancel, Array.getElem!_toList]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    constructor <;> intro h <;> omega
  have hcard : ∀ c, (univ.filter (fun x => pc x = c)).card = (univ.filter (fun v => vc v = c)).card := by
    rintro ⟨t, d⟩
    rcases Nat.lt_or_ge t 3 with ht | ht
    · have ep : univ.filter (fun x => pc x = (t, d)) =
          univ.filter (fun x : Fin 22 => roleP k x = t ∧ cells.D[x.val]! = d) := by
        ext x; simp [pc, Prod.ext_iff]
      have ev : univ.filter (fun v => vc v = (t, d)) =
          univ.filter (fun v : Fin 22 => roleV K r v = t ∧ dg v = d) := by
        ext x; simp [vc, Prod.ext_iff]
      rw [ep, ev]
      interval_cases t
      · -- the root
        have e1 : univ.filter (fun x : Fin 22 => roleP k x = 0 ∧ cells.D[x.val]! = d) =
            if d = k then {(0 : Fin 22)} else ∅ := by
          ext x
          simp only [mem_filter, mem_univ, true_and, roleP_zero]
          by_cases h : d = k
          · rw [if_pos h, mem_singleton]
            constructor
            · rintro ⟨hx, -⟩; exact Fin.ext hx
            · rintro rfl; exact ⟨rfl, by rw [hroot, h]⟩
          · rw [if_neg h]
            simp only [Finset.notMem_empty, iff_false, not_and]
            intro hx hd
            have : x = 0 := Fin.ext hx
            subst this; exact h (by rw [← hd, hroot])
        have e2 : univ.filter (fun v : Fin 22 => roleV K r v = 0 ∧ dg v = d) =
            if d = k then {r} else ∅ := by
          ext v
          simp only [mem_filter, mem_univ, true_and, roleV_zero]
          by_cases h : d = k
          · rw [if_pos h, mem_singleton]
            constructor
            · rintro ⟨hv, -⟩; exact hv
            · rintro rfl; exact ⟨rfl, by rw [hr, h]⟩
          · rw [if_neg h]
            simp only [Finset.notMem_empty, iff_false, not_and]
            rintro rfl hd; exact h (by rw [← hd, hr])
        rw [e1, e2]; split_ifs <;> simp
      · -- neighbours
        have e1 : univ.filter (fun x : Fin 22 => roleP k x = 1 ∧ cells.D[x.val]! = d) =
            univ.filter (fun x : Fin 22 => x.val ≠ 0 ∧ x.val ≤ k ∧ cells.D[x.val]! = d) := by
          ext x; simp only [mem_filter, mem_univ, true_and, roleP_one, and_assoc]
        have e2 : univ.filter (fun v : Fin 22 => roleV K r v = 1 ∧ dg v = d) =
            univ.filter (fun v => dg v = d ∧ ¬ v = r ∧ K.C r v = true) := by
          ext v; simp only [mem_filter, mem_univ, true_and, roleV_one]
          constructor
          · rintro ⟨⟨h2, h3⟩, h4⟩; exact ⟨h4, h2, h3⟩
          · rintro ⟨h4, h2, h3⟩; exact ⟨⟨h2, h3⟩, h4⟩
        rw [e1, e2, hposN]
        show cntN cells.D k d = nu d
        by_cases hd : d = 8 ∨ d = 9 ∨ d = 10
        · rw [hcN d (pick_of_mem hd)]
          rcases hd with rfl | rfl | rfl <;> rfl
        · have z1 : cntN cells.D k d = 0 := by
            rw [← hposN, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro x _ hx; exact hd (hx.2.2 ▸ hrangeD x)
          have z2 : nu d = 0 := by
            show (univ.filter _).card = 0
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro x _ hx; exact hd (hx.1 ▸ hdeg x)
          rw [z1, z2]
      · -- non-neighbours
        have e1 : univ.filter (fun x : Fin 22 => roleP k x = 2 ∧ cells.D[x.val]! = d) =
            univ.filter (fun x : Fin 22 => x.val ≠ 0 ∧ ¬ x.val ≤ k ∧ cells.D[x.val]! = d) := by
          ext x; simp only [mem_filter, mem_univ, true_and, roleP_two, and_assoc]
        have e2 : univ.filter (fun v : Fin 22 => roleV K r v = 2 ∧ dg v = d) =
            univ.filter (fun v => dg v = d ∧ ¬ v = r ∧ ¬ K.C r v = true) := by
          ext v; simp only [mem_filter, mem_univ, true_and, roleV_two]
          constructor
          · rintro ⟨⟨h2, h3⟩, h4⟩; exact ⟨h4, h2, h3⟩
          · rintro ⟨h4, h2, h3⟩; exact ⟨⟨h2, h3⟩, h4⟩
        rw [e1, e2, hposW]
        show cntW cells.D k d = wc d
        by_cases hd : d = 8 ∨ d = 9 ∨ d = 10
        · rw [hcW d (pick_of_mem hd)]
          rcases hd with rfl | rfl | rfl
          · show n8 - ind 8 k - nu 8 = wc 8; omega
          · show n9 - ind 9 k - nu 9 = wc 9; omega
          · show n10 - ind 10 k - nu 10 = wc 10; omega
        · have z1 : cntW cells.D k d = 0 := by
            rw [← hposW, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro x _ hx; exact hd (hx.2.2 ▸ hrangeD x)
          have z2 : wc d = 0 := by
            show (univ.filter _).card = 0
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro x _ hx; exact hd (hx.1 ▸ hdeg x)
          rw [z1, z2]
    · have e1 : univ.filter (fun x => pc x = (t, d)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro x _ hx
        have := roleP_lt k x; simp only [pc, Prod.mk.injEq] at hx; omega
      have e2 : univ.filter (fun v => vc v = (t, d)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro x _ hx
        have := roleV_lt K r x; simp only [vc, Prod.mk.injEq] at hx; omega
      rw [e1, e2]
  -- the relabelling
  have hfib : ∀ c, Fintype.card {x // pc x = c} = Fintype.card {v // vc v = c} := by
    intro c; rw [Fintype.card_subtype, Fintype.card_subtype]; exact hcard c
  let π : Equiv.Perm (Fin 22) := Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hfib c))
  have hπ : ∀ x, vc (π x) = pc x := fun x => Equiv.ofFiberEquiv_map _ x
  have hπ0 : π 0 = r := by
    have h := congrArg Prod.fst (hπ 0)
    simp only [vc, pc] at h
    have : roleP k 0 = 0 := by unfold roleP; simp
    rw [this, roleV_zero] at h
    exact h
  refine ⟨π, ?_, ?_⟩
  · intro u hu
    have h1 := congrArg Prod.fst (hπ u)
    simp only [vc, pc] at h1
    have hu0 : u.val ≠ 0 := fun h => hu (Fin.ext h.symm)
    have hne : π u ≠ r := by
      rw [← hπ0]; exact fun h => hu (π.injective h).symm
    have hrn : r ≠ π u := fun h => hne h.symm
    rw [actV_mkEdge, mkEdge_congr_root π hπ0, ← kOf_C_iff b hrn, hK]
    have hu1 : roleP k u = 1 ∨ roleP k u = 2 := by unfold roleP; split_ifs <;> simp_all
    constructor
    · intro hC
      have : roleV K r (π u) = 1 := (roleV_one K r (π u)).mpr ⟨hne, hC⟩
      rw [this] at h1
      exact ((roleP_one k u).mp h1.symm).2
    · intro hk'
      have : roleP k u = 1 := (roleP_one k u).mpr ⟨hu0, hk'⟩
      rw [this] at h1
      exact ((roleV_one K r (π u)).mp h1).2
  · intro v
    rw [deg_actV, deg_eq_card, hK, hdgv]
    have := congrArg Prod.snd (hπ v)
    simpa [vc, pc] using this

end SB.Rooted.M4

#print axioms SB.Rooted.M4.exists_relabel
