/-
# M4, part 3: the two lex-leader stages and the group closures

* `exists_leader_orbit`: in the orbit of `b`, a property `P` closed under a set `S` of relabellings
  and met by some relabelling of `b` is met by a relabelling that is lex-`≤` its image under every
  element of `S` (`exists_sb_leader`).
* Stage 1 lives on `EColouring k 2` (the graph `H` on the root's neighbourhood, edges row-major,
  red < blue, which is the order of the M0 cover words): `restr` reads `H` off positions `1..k`,
  `lift` extends a permutation of `Fin k` to `Fin 22`, and `restr_actV_lift` says relabelling by
  the lift is relabelling `H`.
* Stage 2 closures: `Row1`, `DegEq` and `HUnits` are preserved by every W-cell transposition
  (`WSwap`) and by every `CellAut` permutation, given `CellsSem`.
-/
import RootedM4.Relabel

set_option linter.unusedVariables false

namespace SB.Rooted.M4
open LRATCatcher.Rooted SB.Rooted SB Finset

/-! ## Relabelling composes -/

theorem actV_actV {n r : ℕ} (σ τ : Equiv.Perm (Fin n)) (a : EColouring n r) :
    actV τ (actV σ a) = actV (σ * τ) a := by
  funext e
  show actV σ a (mkEdge (τ _) (τ _) _) = _
  rw [actV_mkEdge]; rfl

theorem mkEdge_congr {n : ℕ} {x y x' y' : Fin n} (h : x ≠ y) (hx : x = x') (hy : y = y') :
    mkEdge x y h = mkEdge x' y' (hx ▸ hy ▸ h) := by
  subst hx hy; rfl

/-! ## The generic leader in an orbit -/

theorem exists_leader_orbit {n : ℕ} (b : EColouring n 2) (P : EColouring n 2 → Prop)
    (S : Set (Equiv.Perm (Fin n))) (hcl : ∀ τ ∈ S, ∀ a, P a → P (actV τ a))
    (hne : ∃ π, P (actV π b)) :
    ∃ π, P (actV π b) ∧ ∀ τ ∈ S, lexView (actV π b) ≤ lexView (actV τ (actV π b)) := by
  classical
  let M : Set (Lex (Edge n → Fin 2)) := {x | ∃ π, ofLex x = actV π b ∧ P (ofLex x)}
  let T : Set (Lex (Edge n → Fin 2) → Lex (Edge n → Fin 2)) :=
    (fun τ => fun x => toLex (actV τ (ofLex x))) '' S
  have hclosed : ∀ g ∈ T, ∀ x ∈ M, g x ∈ M := by
    rintro g ⟨τ, hτ, rfl⟩ x ⟨π, hx, hP⟩
    refine ⟨π * τ, ?_, ?_⟩
    · show actV τ (ofLex x) = _
      rw [hx, actV_actV]
    · exact hcl τ hτ _ hP
  obtain ⟨π0, h0⟩ := hne
  obtain ⟨x, ⟨π, hx, hP⟩, hle⟩ := exists_sb_leader (M := M) ⟨toLex (actV π0 b), π0, rfl, h0⟩ hclosed
  refine ⟨π, hx ▸ hP, fun τ hτ => ?_⟩
  have := hle _ ⟨τ, hτ, rfl⟩
  rw [← hx]; exact this

/-! ## Stage 1: the graph on positions `1..k` -/

section Stage1
variable {k : ℕ}

/-- Position `i : Fin k` of the neighbourhood is vertex `i + 1` of `K_22`. -/
def sh (hk : k < 22) (i : Fin k) : Fin 22 := ⟨i.val + 1, by omega⟩

theorem sh_val (hk : k < 22) (i : Fin k) : (sh hk i).val = i.val + 1 := rfl

theorem sh_inj (hk : k < 22) {i j : Fin k} (h : sh hk i = sh hk j) : i = j := by
  apply Fin.ext; have := congrArg Fin.val h; simp [sh] at this; omega

theorem sh_ne (hk : k < 22) {i j : Fin k} (h : i ≠ j) : sh hk i ≠ sh hk j :=
  fun e => h (sh_inj hk e)

/-- `H` read off positions `1..k`. -/
def restr (hk : k < 22) (a : EColouring 22 2) : EColouring k 2 :=
  fun e => a (mkEdge (sh hk (ofLex e.val).1) (sh hk (ofLex e.val).2) (sh_ne hk (ne_of_lt e.prop)))

theorem restr_mkEdge (hk : k < 22) (a : EColouring 22 2) {i j : Fin k} (h : i ≠ j) :
    restr hk a (mkEdge i j h) = a (mkEdge (sh hk i) (sh hk j) (sh_ne hk h)) := by
  rcases lt_or_gt_of_ne h with hij | hji
  · rw [mkEdge_pos h hij]; rfl
  · rw [mkEdge_neg h hji]
    show a (mkEdge (sh hk j) (sh hk i) _) = _
    rw [mkEdge_comm]

def liftF (hk : k < 22) (p : Equiv.Perm (Fin k)) (x : Fin 22) : Fin 22 :=
  if h : 1 ≤ x.val ∧ x.val ≤ k then sh hk (p ⟨x.val - 1, by omega⟩) else x

theorem liftF_inv (hk : k < 22) (p : Equiv.Perm (Fin k)) (x : Fin 22) :
    liftF hk p.symm (liftF hk p x) = x := by
  unfold liftF
  by_cases h : 1 ≤ x.val ∧ x.val ≤ k
  · rw [dif_pos h]
    have h' : 1 ≤ (sh hk (p ⟨x.val - 1, by omega⟩)).val ∧ (sh hk (p ⟨x.val - 1, by omega⟩)).val ≤ k := by
      simp only [sh_val]; have := (p ⟨x.val - 1, by omega⟩).isLt; omega
    rw [dif_pos h']
    apply Fin.ext
    simp only [sh_val, Nat.add_sub_cancel, Fin.eta, Equiv.symm_apply_apply]
    omega
  · rw [dif_neg h, dif_neg h]

/-- A permutation of the neighbourhood positions, extended by the identity. -/
def lift (hk : k < 22) (p : Equiv.Perm (Fin k)) : Equiv.Perm (Fin 22) where
  toFun := liftF hk p
  invFun := liftF hk p.symm
  left_inv := liftF_inv hk p
  right_inv := by intro x; have := liftF_inv hk p.symm x; simpa using this

theorem lift_sh (hk : k < 22) (p : Equiv.Perm (Fin k)) (i : Fin k) :
    lift hk p (sh hk i) = sh hk (p i) := by
  show liftF hk p (sh hk i) = _
  unfold liftF
  rw [dif_pos (by simp only [sh_val]; have := i.isLt; omega)]
  simp [sh]

theorem lift_fix (hk : k < 22) (p : Equiv.Perm (Fin k)) {x : Fin 22}
    (h : ¬ (1 ≤ x.val ∧ x.val ≤ k)) : lift hk p x = x := by
  show liftF hk p x = x
  unfold liftF; rw [dif_neg h]

theorem lift_range (hk : k < 22) (p : Equiv.Perm (Fin k)) (x : Fin 22) (h : 1 ≤ x.val ∧ x.val ≤ k) :
    lift hk p x = sh hk (p ⟨x.val - 1, by omega⟩) := by
  show liftF hk p x = _
  unfold liftF; rw [dif_pos h]

theorem restr_actV_lift (hk : k < 22) (p : Equiv.Perm (Fin k)) (a : EColouring 22 2) :
    restr hk (actV (lift hk p) a) = actV p (restr hk a) := by
  funext e
  show actV (lift hk p) a (mkEdge _ _ _) = restr hk a (mkEdge _ _ _)
  rw [actV_mkEdge, restr_mkEdge]
  congr 1
  apply mkEdge_congr <;> exact lift_sh hk p _

/-- **Stage 1.** For any `H` and any set of permutations of `Fin k` containing `1` and closed under
products, some member `q` makes `actV q H` lex-`≤` its image under every member. -/
theorem stage1 (h0 : EColouring k 2) (Q : Equiv.Perm (Fin k) → Prop) (h1 : Q 1)
    (hmul : ∀ p q, Q p → Q q → Q (p * q)) :
    ∃ q, Q q ∧ ∀ p, Q p → lexView (actV q h0) ≤ lexView (actV p (actV q h0)) := by
  obtain ⟨π, ⟨q, hq, he⟩, hle⟩ := exists_leader_orbit h0 (fun a => ∃ q, Q q ∧ a = actV q h0)
    {p | Q p} (by
      rintro τ hτ a ⟨q, hq, rfl⟩
      exact ⟨q * τ, hmul _ _ hq hτ, by rw [actV_actV]⟩)
    ⟨1, 1, h1, rfl⟩
  refine ⟨q, hq, fun p hp => ?_⟩
  rw [← he]; exact hle p hp

end Stage1

/-! ## Closure of `Row1` and `DegEq` -/

/-- The H units of a cube. -/
def HUnits (a : EColouring 22 2) (k : Nat) (Hs : Array (Nat × Nat)) : Prop :=
  ∀ x y : Fin 22, (h : x ≠ y) → 1 ≤ x.val → 1 ≤ y.val → x.val ≤ k → y.val ≤ k →
    (a (mkEdge x y h) = 1 ↔ Hs.contains (srt (x.val + 1) (y.val + 1)) = true)

theorem row1_closed {a : EColouring 22 2} {k : Nat} (τ : Equiv.Perm (Fin 22)) (h0 : τ 0 = 0)
    (hk : ∀ x, (τ x).val ≤ k ↔ x.val ≤ k) (ha : Row1 a k) : Row1 (actV τ a) k := by
  intro u hu
  rw [actV_mkEdge, mkEdge_congr _ h0 rfl]
  have hne : (0 : Fin 22) ≠ τ u := by
    rw [← h0]; exact fun e => hu (τ.injective e)
  rw [ha (τ u) hne, hk]

theorem degEq_closed {a : EColouring 22 2} {cells : Cells} (τ : Equiv.Perm (Fin 22))
    (hD : ∀ x : Fin 22, cells.D[(τ x).val]! = cells.D[x.val]!) (ha : DegEq a cells) :
    DegEq (actV τ a) cells := by
  intro v; rw [deg_actV, ha, hD]

/-! ## W-cell transpositions -/

/-- A transposition of two vertices of one W-cell (encoder numbering). -/
def WSwap (cells : Cells) (τ : Equiv.Perm (Fin 22)) : Prop :=
  ∃ cl ∈ cells.wcells, ∃ p q, cl.1 ≤ p ∧ p < q ∧ q ≤ cl.2.1 ∧ τ = Equiv.swap (fv p) (fv q)

section Closures
variable {n8 n9 n10 v8 v9 v10 : Nat} {cells : Cells}

theorem wswap_props (hc : CellsSem n8 n9 n10 v8 v9 v10 cells) {τ : Equiv.Perm (Fin 22)}
    (hw : WSwap cells τ) :
    (∀ x : Fin 22, x.val ≤ rootOf n8 n10 → τ x = x) ∧
    (∀ x, (τ x).val ≤ rootOf n8 n10 ↔ x.val ≤ rootOf n8 n10) ∧
    (∀ x : Fin 22, cells.D[(τ x).val]! = cells.D[x.val]!) := by
  obtain ⟨cl, hcl, p, q, h1, h2, h3, rfl⟩ := hw
  obtain ⟨hlo, hhi, hD⟩ := hc.wcell cl hcl
  have hp := fv_val (u := p) (by omega) (by omega)
  have hq := fv_val (u := q) (by omega) (by omega)
  have fix : ∀ x : Fin 22, x.val ≤ rootOf n8 n10 → Equiv.swap (fv p) (fv q) x = x := by
    intro x hx
    apply Equiv.swap_apply_of_ne_of_ne
    · intro e; rw [e, hp] at hx; omega
    · intro e; rw [e, hq] at hx; omega
  refine ⟨fix, fun x => ?_, fun x => ?_⟩
  · by_cases hx : x.val ≤ rootOf n8 n10
    · rw [fix x hx]
    · rw [Equiv.swap_apply_def]
      split_ifs with e1 e2
      · rw [hq]; subst e1; rw [hp] at hx; omega
      · rw [hp]; subst e2; rw [hq] at hx; omega
      · rfl
  · rw [Equiv.swap_apply_def]
    split_ifs with e1 e2
    · subst e1; rw [hp, hq]
      rw [hD q (by omega) (by omega), hD p h1 (by omega)]
    · subst e2; rw [hp, hq]
      rw [hD q (by omega) (by omega), hD p h1 (by omega)]
    · rfl

theorem hunits_closed_fix {a : EColouring 22 2} {k : Nat} {Hs : Array (Nat × Nat)}
    (τ : Equiv.Perm (Fin 22)) (hfix : ∀ x : Fin 22, x.val ≤ k → τ x = x) (ha : HUnits a k Hs) :
    HUnits (actV τ a) k Hs := by
  intro x y hxy h1 h2 h3 h4
  rw [actV_mkEdge, mkEdge_congr _ (hfix x h3) (hfix y h4)]
  exact ha x y hxy h1 h2 h3 h4

/-! ## `CellAut` permutations -/

theorem srt_eq_iff (a b c d : Nat) :
    srt a b = srt c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  unfold srt; split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem srt_comm (a b : Nat) : srt a b = srt b a := by
  unfold srt; split_ifs <;> simp only [Prod.mk.injEq] <;> omega

theorem srt_le (a b : Nat) : (srt a b).1 ≤ (srt a b).2 := by
  unfold srt; split_ifs <;> simp <;> omega

theorem srt_img (f : Nat → Nat) (a b : Nat) : srt (f (srt a b).1) (f (srt a b).2) = srt (f a) (f b) := by
  by_cases h : a ≤ b
  · have : srt a b = (a, b) := by unfold srt; rw [if_pos h]
    rw [this]
  · have : srt a b = (b, a) := by unfold srt; rw [if_neg h]
    rw [this, srt_comm]

theorem τN_inj (τ : Equiv.Perm (Fin 22)) {u w : Nat} (h : τN τ u = τN τ w) : u = w := by
  unfold τN at h
  by_cases hu : 1 ≤ u ∧ u ≤ 22 <;> by_cases hw : 1 ≤ w ∧ w ≤ 22
  · rw [if_pos hu, if_pos hw] at h
    have : τ (fv u) = τ (fv w) := Fin.ext (by omega)
    exact fv_inj hu.1 hu.2 hw.1 hw.2 (τ.injective this)
  · rw [if_pos hu, if_neg hw] at h; have := (τ (fv u)).isLt; omega
  · rw [if_neg hu, if_pos hw] at h; have := (τ (fv w)).isLt; omega
  · rw [if_neg hu, if_neg hw] at h; exact h

theorem τN_succ (τ : Equiv.Perm (Fin 22)) (x : Fin 22) : τN τ (x.val + 1) = (τ x).val + 1 := by
  unfold τN; rw [if_pos ⟨by omega, by have := x.isLt; omega⟩, fv_succ]

/-- A `CellAut` map sends `Hs` onto itself, so it also reflects membership. -/
theorem cellAut_reflect (τ : Equiv.Perm (Fin 22)) (Hs : Array (Nat × Nat))
    (hsorted : ∀ e ∈ Hs, e.1 ≤ e.2)
    (h3 : ∀ e ∈ Hs, Hs.contains (srt (τN τ e.1) (τN τ e.2)) = true) (u w : Nat) (huw : u ≤ w)
    (hc : Hs.contains (srt (τN τ u) (τN τ w)) = true) : Hs.contains (u, w) = true := by
  classical
  let S : Finset (Nat × Nat) := Hs.toList.toFinset
  let F : Nat × Nat → Nat × Nat := fun e => srt (τN τ e.1) (τN τ e.2)
  have hmemS : ∀ e, e ∈ S ↔ e ∈ Hs := fun e => by simp [S]
  have hinj : ∀ e e' : Nat × Nat, e.1 ≤ e.2 → e'.1 ≤ e'.2 → F e = F e' → e = e' := by
    intro e e' he he' hF
    rcases (srt_eq_iff _ _ _ _).mp hF with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext (τN_inj τ h1) (τN_inj τ h2)
    · have a1 := τN_inj τ h1; have a2 := τN_inj τ h2
      exact Prod.ext (by omega) (by omega)
  have hsub : S.image F ⊆ S := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    exact (hmemS _).mpr (Array.contains_iff_mem.mp (h3 e ((hmemS e).mp he)))
  have hcard : S.card ≤ (S.image F).card := by
    rw [Finset.card_image_of_injOn]
    intro e he e' he' hF
    exact hinj e e' (hsorted e ((hmemS e).mp he)) (hsorted e' ((hmemS e').mp he')) hF
  have heq : S.image F = S := Finset.eq_of_subset_of_card_le hsub hcard
  have hFin : F (u, w) ∈ S := (hmemS _).mpr (Array.contains_iff_mem.mp hc)
  rw [← heq] at hFin
  obtain ⟨e, he, hFe⟩ := Finset.mem_image.mp hFin
  have := hinj e (u, w) (hsorted e ((hmemS e).mp he)) huw hFe
  rw [← this]; exact Array.contains_iff_mem.mpr ((hmemS e).mp he)

theorem cellAut_props (hc : CellsSem n8 n9 n10 v8 v9 v10 cells) {τ : Equiv.Perm (Fin 22)}
    {Hs : Array (Nat × Nat)} (ha : CellAut τ cells Hs) :
    τ 0 = 0 ∧ (∀ x, (τ x).val ≤ rootOf n8 n10 ↔ x.val ≤ rootOf n8 n10) ∧
    (∀ x : Fin 22, 1 ≤ x.val → 1 ≤ (τ x).val) ∧
    (∀ x : Fin 22, cells.D[(τ x).val]! = cells.D[x.val]!) := by
  obtain ⟨hoff, hcell, -⟩ := ha
  -- membership in an N-cell
  have hin : ∀ v, v ∈ cellVerts (nCellArrays cells) → ∃ cl ∈ cells.ncells, cl.1 ≤ v ∧ v ≤ cl.2.1 := by
    intro v hv
    obtain ⟨arr, harr, hvarr⟩ := mem_cellVerts.mp hv
    unfold nCellArrays at harr
    obtain ⟨cl, hcl, rfl⟩ := Array.mem_map.mp harr
    have hv' : v ∈ List.range' cl.1 (cl.2.1 + 1 - cl.1) := by simpa using hvarr
    rw [List.mem_range'_1] at hv'
    exact ⟨cl, hcl, by omega, by omega⟩
  have hcellD : ∀ x : Fin 22, x.val + 1 ∈ cellVerts (nCellArrays cells) →
      (2 ≤ x.val + 1 ∧ x.val + 1 ≤ rootOf n8 n10 + 1) ∧ (2 ≤ (τ x).val + 1 ∧ (τ x).val + 1 ≤ rootOf n8 n10 + 1) ∧
      cells.D[(τ x).val]! = cells.D[x.val]! := by
    intro x hx
    obtain ⟨arr, harr, h1, h2⟩ := hcell x hx
    unfold nCellArrays at harr
    obtain ⟨cl, hcl, rfl⟩ := Array.mem_map.mp harr
    have h1' : x.val + 1 ∈ List.range' cl.1 (cl.2.1 + 1 - cl.1) := by simpa using h1
    have h2' : (τ x).val + 1 ∈ List.range' cl.1 (cl.2.1 + 1 - cl.1) := by simpa using h2
    rw [List.mem_range'_1] at h1' h2'
    obtain ⟨hlo, hhi, hD⟩ := hc.ncell cl hcl
    have e1 := hD (x.val + 1) (by omega) (by omega)
    have e2 := hD ((τ x).val + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at e1 e2
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by rw [e1, e2]⟩
  have h0 : τ 0 = 0 := by
    apply hoff
    intro h
    have := (hcellD 0 h).1; simp at this
  refine ⟨h0, fun x => ?_, fun x hx => ?_, fun x => ?_⟩
  · by_cases hx : x.val + 1 ∈ cellVerts (nCellArrays cells)
    · have := hcellD x hx; constructor <;> intro _ <;> omega
    · rw [hoff x hx]
  · by_contra hne
    have : τ x = 0 := Fin.ext (by omega)
    rw [← h0] at this
    have := τ.injective this; subst this; simp at hx
  · by_cases hx : x.val + 1 ∈ cellVerts (nCellArrays cells)
    · exact (hcellD x hx).2.2
    · rw [hoff x hx]

theorem hunits_closed_aut (hc : CellsSem n8 n9 n10 v8 v9 v10 cells) {a : EColouring 22 2}
    {Hs : Array (Nat × Nat)} (hsorted : ∀ e ∈ Hs, e.1 ≤ e.2) {τ : Equiv.Perm (Fin 22)}
    (haut : CellAut τ cells Hs) (ha : HUnits a (rootOf n8 n10) Hs) :
    HUnits (actV τ a) (rootOf n8 n10) Hs := by
  obtain ⟨h0, hk, h1, -⟩ := cellAut_props hc haut
  have h3 := haut.2.2
  intro x y hxy hx1 hy1 hxk hyk
  rw [actV_mkEdge]
  rw [ha (τ x) (τ y) _ (h1 x hx1) (h1 y hy1) ((hk x).mpr hxk) ((hk y).mpr hyk)]
  rw [← τN_succ, ← τN_succ]
  constructor
  · intro hc'
    have hs := srt_le (x.val + 1) (y.val + 1)
    have key : srt (τN τ (srt (x.val + 1) (y.val + 1)).1) (τN τ (srt (x.val + 1) (y.val + 1)).2) =
        srt (τN τ (x.val + 1)) (τN τ (y.val + 1)) := srt_img _ _ _
    have := cellAut_reflect τ Hs hsorted h3 _ _ hs (by rw [key]; exact hc')
    simpa using this
  · intro hc'
    have hmem := Array.contains_iff_mem.mp hc'
    have := h3 _ hmem
    have key : srt (τN τ (srt (x.val + 1) (y.val + 1)).1) (τN τ (srt (x.val + 1) (y.val + 1)).2) =
        srt (τN τ (x.val + 1)) (τN τ (y.val + 1)) := srt_img _ _ _
    rwa [key] at this

end Closures

end SB.Rooted.M4

#print axioms SB.Rooted.M4.exists_leader_orbit
#print axioms SB.Rooted.M4.stage1
#print axioms SB.Rooted.M4.restr_actV_lift
#print axioms SB.Rooted.M4.wswap_props
#print axioms SB.Rooted.M4.cellAut_reflect
#print axioms SB.Rooted.M4.hunits_closed_aut
