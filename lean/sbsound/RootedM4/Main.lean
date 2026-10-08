/-
# M4, part 4: every good colouring of `K_22` is in the canonical form of a listed cube

The coverage step (Theorem 3.1 of LEMMAS_draft together with the M0 H-cover) is stated as the
hypothesis `CensusCover C` about a list `C` of cubes (`degs, k, comp, H` and the option set `o` under
which the cube's verdict was certified). It says: for every census case and every graph `h` on the
root's neighbourhood (positions `0..k-1`, i.e. encoder vertices `2..k+1`) that passes the three
census filters in the form M1 proves for good colourings (`FiltersOK`) and is lex-`≤` its image
under every degree-preserving permutation of the neighbourhood (`DPres`), the list `C` contains a
cube of that case whose `H` is `h` (the `srt`-normalised edges of `c.H` are exactly `hEdges h`),
with `shortfall = false`.
This is exactly what the M0 cover CNF of the family certifies (`RootedM4.Cover` for the CNF
semantics); it is a hypothesis here, never an axiom.

* `exists_canon`: under `CensusCover C`, every good `b` has a relabelling `a = actV π b` (good) and a
  cube `c ∈ C` with `cellsOf … = .ok cells`, `CubeWF cells`, `c.o.shortfall = false` and
  `RootedCanon a c.k cells (normH c.H) c.o`.
* `no_good_K22_of`: if moreover no good colouring is in the canonical form of any cube of `C`
  (what `no_canon_of_unsat` / `no_canon_of_children_unsat` give from cake_lpr verdicts), then
  `K_22` has no good colouring.

Order of choices: the relabelling `π0` of `exists_relabel` (root, cells), then the stage-1 leader
`q` over the degree-preserving permutations of the neighbourhood (this fixes the labelled `H`), then
the stage-2 leader over the orbit of `b` restricted to `Row1 ∧ DegEq ∧ HUnits`, for the
W-cell transpositions and the `CellAut` maps of the fixed `H`.
-/
import RootedM4.Leader

set_option linter.unusedVariables false

namespace SB.Rooted.M4
open LRATCatcher.Rooted SB.Rooted SB Finset

/-- **The coverage hypothesis** (what the M0 cover CNFs certify, family by family). -/
def CensusCover (C : List Cube) : Prop :=
  ∀ n8 n9 n10 v8 v9 v10 : Nat, ValidCase n8 n9 n10 v8 v9 v10 →
  ∀ h : EColouring (rootOf n8 n10) 2,
    FiltersOK (rootOf n8 n10) (Dnu (rootOf n8 n10) v8 v9 v10) (gOf h) →
    (∀ p, DPres (rootOf n8 n10) v8 v9 v10 p → lexView h ≤ lexView (actV p h)) →
    ∃ c ∈ C, c.degs = histDegs n8 n9 n10 ∧ c.k = rootOf n8 n10 ∧
      c.comp = compF v8 v9 v10 ∧
      (∀ q, q ∈ c.H.map (fun p => srt p.1 p.2) ↔ q ∈ hEdges h) ∧ c.o.shortfall = false

/-! ## `normH` and `hEdges` -/

theorem normH_contains (H : List (Nat × Nat)) (q : Nat × Nat) :
    (normH H).contains q = true ↔ q ∈ H.map (fun p => srt p.1 p.2) := by
  unfold normH
  rw [Array.contains_iff_mem, List.mem_toArray, List.mem_mergeSort, List.mem_eraseDups]

theorem normH_sorted (H : List (Nat × Nat)) : ∀ e ∈ normH H, e.1 ≤ e.2 := by
  intro e he
  have := (normH_contains H e).mp (Array.contains_iff_mem.mpr he)
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp this
  exact srt_le _ _

theorem mem_hEdges {k : Nat} (h : EColouring k 2) (u w : Nat) :
    (u, w) ∈ hEdges h ↔ ∃ i j : Fin k, ∃ hij : i < j, h ⟨toLex (i, j), hij⟩ = 1 ∧
      u = i.val + 2 ∧ w = j.val + 2 := by
  unfold hEdges
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap]
  constructor
  · rintro ⟨i, j, hj⟩
    split_ifs at hj with h1 h2
    · simp only [Option.some.injEq, Prod.mk.injEq] at hj
      exact ⟨i, j, h1, h2, hj.1.symm, hj.2.symm⟩
  · rintro ⟨i, j, hij, hh, rfl, rfl⟩
    exact ⟨i, j, by rw [dif_pos hij, if_pos hh]⟩

/-- The H units of the graph read off positions `1..k`, against `normH (hEdges …)`. -/
theorem hunits_of_restr {k : Nat} (hk : k < 22) (a : EColouring 22 2) (H : List (Nat × Nat))
    (hH : ∀ q, q ∈ H.map (fun p => srt p.1 p.2) ↔ q ∈ hEdges (restr hk a)) :
    HUnits a k (normH H) := by
  -- the case x < y
  have key : ∀ x y : Fin 22, (hxy : x < y) → 1 ≤ x.val → y.val ≤ k →
      (a (mkEdge x y (ne_of_lt hxy)) = 1 ↔ (normH H).contains (srt (x.val + 1) (y.val + 1)) = true) := by
    intro x y hxy hx hy
    have hlt : x.val < y.val := hxy
    have hs : srt (x.val + 1) (y.val + 1) = (x.val + 1, y.val + 1) := by unfold srt; rw [if_pos (by omega)]
    rw [normH_contains, hH, hs]
    let i : Fin k := ⟨x.val - 1, by omega⟩
    let j : Fin k := ⟨y.val - 1, by omega⟩
    have hij : i < j := by show x.val - 1 < y.val - 1; omega
    have hshi : sh hk i = x := Fin.ext (by simp [sh, i]; omega)
    have hshj : sh hk j = y := Fin.ext (by simp [sh, j]; omega)
    have hval : restr hk a ⟨toLex (i, j), hij⟩ = a (mkEdge x y (ne_of_lt hxy)) := by
      have := restr_mkEdge hk a (ne_of_lt hij)
      rw [mkEdge_pos (ne_of_lt hij) hij] at this
      rw [this]; congr 1; exact mkEdge_congr _ hshi hshj
    rw [mem_hEdges]
    constructor
    · intro hb
      exact ⟨i, j, hij, by rw [hval]; exact hb, by simp [i]; omega, by simp [j]; omega⟩
    · rintro ⟨i', j', hij', hh, hu, hw⟩
      have ei : i' = i := Fin.ext (by simp [i]; omega)
      have ej : j' = j := Fin.ext (by simp [j]; omega)
      subst ei ej
      rw [← hval]; exact hh
  intro x y hxy hx hy hxk hyk
  rcases lt_or_gt_of_ne hxy with h | h
  · exact key x y h hx hyk
  · rw [← mkEdge_comm x y hxy, srt_comm]
    exact key y x h hy hxk

/-! ## The main theorem -/

/-- **Every good colouring of `K_22` is, after relabelling, in the canonical rooted form of a
listed cube** (under the coverage hypothesis). -/
theorem exists_canon (C : List Cube) (hC : CensusCover C) (b : EColouring 22 2)
    (hred : NoKst b 0 2 8) (hblue : NoKst b 1 2 5) :
    ∃ c ∈ C, ∃ cells : Cells, ∃ π : Equiv.Perm (Fin 22),
      cellsOf 22 c.degs c.k c.comp = .ok cells ∧ CubeWF cells ∧ c.o.shortfall = false ∧
      NoKst (actV π b) 0 2 8 ∧ NoKst (actV π b) 1 2 5 ∧
      RootedCanon (actV π b) c.k cells (normH c.H) c.o := by
  classical
  obtain ⟨n8, n9, n10, v8, v9, v10, hv, hrel⟩ := exists_relabel b hred hblue
  obtain ⟨cells, hcF, hc⟩ := census_cells hv
  obtain ⟨π0, hrow0, hdeg0⟩ := hrel cells hc
  have hkm := rootOf_mem n8 n10
  have hk22 : rootOf n8 n10 < 22 := by omega
  have hk21 : rootOf n8 n10 < 21 := by omega
  -- stage 1: the leader over the degree-preserving permutations of the neighbourhood
  obtain ⟨q, hq, hlead⟩ := stage1 (restr hk22 (actV π0 b)) (DPres (rootOf n8 n10) v8 v9 v10)
    (fun i => rfl) (fun p q hp hq i => by show _ = _; simp only [Equiv.Perm.mul_apply]; rw [hp, hq])
  have hl0 : lift hk22 q 0 = 0 := lift_fix _ _ (by simp)
  have hlk : ∀ x, (lift hk22 q x).val ≤ (rootOf n8 n10) ↔ x.val ≤ (rootOf n8 n10) := by
    intro x
    by_cases h : 1 ≤ x.val ∧ x.val ≤ (rootOf n8 n10)
    · rw [lift_range hk22 q x h, sh_val]
      have := (q ⟨x.val - 1, by omega⟩).isLt
      constructor <;> intro _ <;> omega
    · rw [lift_fix hk22 q h]
  have hlD : ∀ x : Fin 22, cells.D[(lift hk22 q x).val]! = cells.D[x.val]! := by
    intro x
    by_cases h : 1 ≤ x.val ∧ x.val ≤ (rootOf n8 n10)
    · rw [lift_range hk22 q x h, sh_val]
      have e1 := hc.nword _ (q ⟨x.val - 1, by omega⟩).isLt
      have e2 := hc.nword (x.val - 1) (by omega)
      rw [Nat.sub_add_cancel h.1] at e2
      rw [e1, e2, hq]
    · rw [lift_fix hk22 q h]
  have hrow1 : Row1 (actV (lift hk22 q) (actV π0 b)) (rootOf n8 n10) := row1_closed _ hl0 hlk hrow0
  have hdeg1 : DegEq (actV (lift hk22 q) (actV π0 b)) cells := degEq_closed _ hlD hdeg0
  have hrestr : restr hk22 (actV (lift hk22 q) (actV π0 b)) = actV q (restr hk22 (actV π0 b)) := restr_actV_lift hk22 q _
  have hred1 : NoKst (actV (lift hk22 q) (actV π0 b)) 0 2 8 := noKst_closed_actV _ _ _ _ _ (noKst_closed_actV _ _ _ _ _ hred)
  have hblue1 : NoKst (actV (lift hk22 q) (actV π0 b)) 1 2 5 := noKst_closed_actV _ _ _ _ _ (noKst_closed_actV _ _ _ _ _ hblue)
  -- the root label of `(actV (lift hk22 q) (actV π0 b))` and M1's filters
  have hmem : ∀ i : Fin (rootOf n8 n10), sh hk22 i ∈ (kOf (actV (lift hk22 q) (actV π0 b))).blueNbr 0 := by
    intro i
    have hne : (0 : Fin 22) ≠ sh hk22 i := fun e => by have := congrArg Fin.val e; simp [sh] at this
    simp only [Colouring.blueNbr, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun e => hne e.symm, (kOf_C_iff (actV (lift hk22 q) (actV π0 b)) hne).mpr ((hrow1 _ hne).mpr ?_)⟩
    simp only [sh_val]; have := i.isLt; omega
  have hcard0 : ((kOf (actV (lift hk22 q) (actV π0 b))).blueNbr 0).card = (rootOf n8 n10) := by
    rw [← deg_eq_card, hdeg1 0]; exact hc.root
  let L : Colouring.RootLabel (kOf (actV (lift hk22 q) (actV π0 b))) 0 (rootOf n8 n10) :=
    { e := sh hk22, inj := fun i j h => sh_inj hk22 h, mem := hmem, card := hcard0 }
  have hD : ∀ i : Fin (rootOf n8 n10), (((kOf (actV (lift hk22 q) (actV π0 b))).blueNbr (L.e i)).card : ℤ) = Dnu (rootOf n8 n10) v8 v9 v10 i := by
    intro i
    show (((kOf (actV (lift hk22 q) (actV π0 b))).blueNbr (sh hk22 i)).card : ℤ) = _
    rw [← deg_eq_card, hdeg1, sh_val, hc.nword i.val i.isLt]; rfl
  have hg : gOf (restr hk22 (actV (lift hk22 q) (actV π0 b))) = Colouring.labH L := by
    funext i j
    unfold gOf Colouring.labH
    by_cases hij : i = j
    · rw [dif_pos hij]; simp [hij]
    · rw [dif_neg hij, restr_mkEdge]
      show decide ((actV (lift hk22 q) (actV π0 b)) _ = 1) = (decide (i ≠ j) && (kOf (actV (lift hk22 q) (actV π0 b))).C (sh hk22 i) (sh hk22 j))
      rw [decide_eq_true hij, Bool.true_and]
      cases hb : (kOf (actV (lift hk22 q) (actV π0 b))).C (sh hk22 i) (sh hk22 j)
      · have : ¬ (actV (lift hk22 q) (actV π0 b)) (mkEdge (sh hk22 i) (sh hk22 j) (sh_ne hk22 hij)) = 1 :=
          fun e => by rw [(kOf_C_iff (actV (lift hk22 q) (actV π0 b)) (sh_ne hk22 hij)).mpr e] at hb; exact Bool.noConfusion hb
        simp [this]
      · simp [(kOf_C_iff (actV (lift hk22 q) (actV π0 b)) (sh_ne hk22 hij)).mp hb]
  have hfilt : FiltersOK (rootOf n8 n10) (Dnu (rootOf n8 n10) v8 v9 v10) (gOf (restr hk22 (actV (lift hk22 q) (actV π0 b)))) := by
    obtain ⟨f1, f2, f3, -⟩ := Colouring.filters_py_NoKst rfl (by rw [toE_kOf]; exact hblue1)
      (by rw [toE_kOf]; exact hred1) L (Dnu (rootOf n8 n10) v8 v9 v10) hD hk21
    rw [hg]; exact ⟨f1, f2, f3⟩
  obtain ⟨c, hcC, hdegs, hck, hcomp, hH, hsf⟩ :=
    hC n8 n9 n10 v8 v9 v10 hv (restr hk22 (actV (lift hk22 q) (actV π0 b))) hfilt (by rw [hrestr]; exact hlead)
  have hun1 : HUnits (actV (lift hk22 q) (actV π0 b)) (rootOf n8 n10) (normH c.H) := hunits_of_restr hk22 (actV (lift hk22 q) (actV π0 b)) c.H hH
  -- stage 2: the leader over the W transpositions and the `CellAut` maps of the fixed `H`
  let P : EColouring 22 2 → Prop := fun a => Row1 a (rootOf n8 n10) ∧ DegEq a cells ∧ HUnits a (rootOf n8 n10) (normH c.H)
  let S : Set (Equiv.Perm (Fin 22)) := {τ | WSwap cells τ ∨ CellAut τ cells (normH c.H)}
  have hcl : ∀ τ ∈ S, ∀ a, P a → P (actV τ a) := by
    rintro τ (hw | haut) a ⟨h1, h2, h3⟩
    · obtain ⟨hfix, hk, hDτ⟩ := wswap_props hc hw
      have h0 : τ 0 = 0 := hfix 0 (by simp)
      exact ⟨row1_closed τ h0 hk h1, degEq_closed τ hDτ h2, hunits_closed_fix τ hfix h3⟩
    · obtain ⟨h0, hk, -, hDτ⟩ := cellAut_props hc haut
      exact ⟨row1_closed τ h0 hk h1, degEq_closed τ hDτ h2,
        hunits_closed_aut hc (normH_sorted c.H) haut h3⟩
  obtain ⟨π, ⟨hr, hdg, hu⟩, hle⟩ := exists_leader_orbit b P S hcl
    ⟨π0 * lift hk22 q, by rw [← actV_actV]; exact ⟨hrow1, hdeg1, hun1⟩⟩
  have hcells : cellsOf 22 c.degs c.k c.comp = .ok cells := by
    rw [hdegs, hck, hcomp]; exact hcF
  refine ⟨c, hcC, cells, π, hcells, hc.wf, hsf, noKst_closed_actV _ _ _ _ _ hred,
    noKst_closed_actV _ _ _ _ _ hblue, ?_⟩
  rw [hck]
  exact
    { row1 := hr
      deg := hdg
      hunits := hu
      wlex := fun cl hcl v h1 h2 => hle _ (Or.inl ⟨cl, hcl, v, v + 1, h1, by omega, h2, rfl⟩)
      wall := fun _ cl hcl p q h1 h2 h3 => hle _ (Or.inl ⟨cl, hcl, p, q, h1, h2, h3, rfl⟩)
      auth := fun _ τ hτ => hle _ (Or.inr hτ) }

/-- **No good colouring of `K_22`**, given the coverage hypothesis and that no good colouring is in
the canonical form of any listed cube (the per-cube verdicts, through `no_canon_of_unsat` or
`no_canon_of_children_unsat`). -/
theorem no_good_K22_of (C : List Cube) (hC : CensusCover C)
    (hU : ∀ c ∈ C, ∀ cells : Cells, cellsOf 22 c.degs c.k c.comp = .ok cells → CubeWF cells →
      c.o.shortfall = false →
      ¬ ∃ a : EColouring 22 2, NoKst a 0 2 8 ∧ NoKst a 1 2 5 ∧ RootedCanon a c.k cells (normH c.H) c.o) :
    ¬ ∃ b : EColouring 22 2, NoKst b 0 2 8 ∧ NoKst b 1 2 5 := by
  rintro ⟨b, hred, hblue⟩
  obtain ⟨c, hcC, cells, π, hcells, hwf, hsf, h1, h2, hcan⟩ := exists_canon C hC b hred hblue
  exact hU c hcC cells hcells hwf hsf ⟨_, h1, h2, hcan⟩

end SB.Rooted.M4

#print axioms SB.Rooted.M4.normH_contains
#print axioms SB.Rooted.M4.hunits_of_restr
#print axioms SB.Rooted.M4.exists_canon
#print axioms SB.Rooted.M4.no_good_K22_of
