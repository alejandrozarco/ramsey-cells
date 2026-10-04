import Sbsound.SBGraph

/-!
# A concrete witness: `R(K_{3,4}, K_{3,3}) > 18`

An explicit 2-colouring `w18` of the edges of `K_18` such that colour `0`
(table colour 1) contains no `K_{3,4}` and colour `1` (table colour 2)
contains no `K_{3,3}`.

Proof architecture:
* `w18` is the colouring, built from the concrete table `cb`.
* `NoKst c s t` is the mathematical predicate "colour `c` contains no
  monochromatic `K_{s,t}`": no pair of disjoint vertex sets of sizes `s`, `t`
  with every one of the `s*t` crossing edges coloured `c`.
* `NoKstR` is the same statement with quantifiers restricted to the finitely
  many subsets of the right size; `noKst_iff_R` proves the restriction loses
  nothing, so the statement being evaluated is the mathematical one.
* `witness18` closes the two goals by evaluation. See `#print axioms` at the
  foot of the file for exactly what that places in the trusted base.
-/

namespace SB.Witness18

open SB

/-! ### The colouring as concrete data -/

/-- `cb i j` = `true` iff edge `{i, j}` (1 ≤ i < j ≤ 18) has table colour 2
(`false` = table colour 1). -/
def cb : ℕ → ℕ → Bool
  | 1,2=>false | 1,3=>false | 1,4=>true | 1,5=>true | 1,6=>true | 1,7=>true | 1,8=>false
  | 1,9=>false | 1,10=>false | 1,11=>false | 1,12=>true | 1,13=>false | 1,14=>true
  | 1,15=>false | 1,16=>false | 1,17=>true | 1,18=>true
  | 2,3=>false | 2,4=>false | 2,5=>true | 2,6=>true | 2,7=>true | 2,8=>true | 2,9=>false
  | 2,10=>true | 2,11=>false | 2,12=>false | 2,13=>true | 2,14=>false | 2,15=>true
  | 2,16=>false | 2,17=>false | 2,18=>true
  | 3,4=>false | 3,5=>false | 3,6=>true | 3,7=>true | 3,8=>true | 3,9=>true | 3,10=>true
  | 3,11=>true | 3,12=>false | 3,13=>false | 3,14=>true | 3,15=>false | 3,16=>true
  | 3,17=>false | 3,18=>false
  | 4,5=>false | 4,6=>false | 4,7=>true | 4,8=>true | 4,9=>true | 4,10=>false | 4,11=>true
  | 4,12=>true | 4,13=>false | 4,14=>false | 4,15=>true | 4,16=>false | 4,17=>true
  | 4,18=>false
  | 5,6=>false | 5,7=>false | 5,8=>true | 5,9=>true | 5,10=>false | 5,11=>false
  | 5,12=>true | 5,13=>true | 5,14=>false | 5,15=>false | 5,16=>true | 5,17=>false
  | 5,18=>true
  | 6,7=>false | 6,8=>false | 6,9=>true | 6,10=>true | 6,11=>false | 6,12=>false
  | 6,13=>true | 6,14=>true | 6,15=>false | 6,16=>false | 6,17=>true | 6,18=>false
  | 7,8=>false | 7,9=>false | 7,10=>false | 7,11=>true | 7,12=>false | 7,13=>false
  | 7,14=>true | 7,15=>true | 7,16=>false | 7,17=>false | 7,18=>true
  | 8,9=>false | 8,10=>true | 8,11=>false | 8,12=>true | 8,13=>false | 8,14=>false
  | 8,15=>true | 8,16=>true | 8,17=>false | 8,18=>false
  | 9,10=>false | 9,11=>true | 9,12=>false | 9,13=>true | 9,14=>false | 9,15=>false
  | 9,16=>true | 9,17=>true | 9,18=>false
  | 10,11=>true | 10,12=>true | 10,13=>false | 10,14=>false | 10,15=>false | 10,16=>false
  | 10,17=>true | 10,18=>true
  | 11,12=>true | 11,13=>true | 11,14=>false | 11,15=>false | 11,16=>false | 11,17=>false
  | 11,18=>true
  | 12,13=>true | 12,14=>true | 12,15=>false | 12,16=>false | 12,17=>false | 12,18=>false
  | 13,14=>true | 13,15=>true | 13,16=>false | 13,17=>false | 13,18=>false
  | 14,15=>true | 14,16=>true | 14,17=>false | 14,18=>false
  | 15,16=>true | 15,17=>true | 15,18=>false
  | 16,17=>true | 16,18=>true
  | 17,18=>true
  | _,_ => false

/-- The vertices of `K_18`. -/
abbrev Vtx := Fin 18

/-- Table bit of the unordered pair `{u, v}`. -/
def bb (u v : Vtx) : Bool :=
  if u < v then cb (u.val + 1) (v.val + 1) else cb (v.val + 1) (u.val + 1)

/-- The witness colouring: table colour 1 ↦ `(0 : Fin 2)`, table colour 2 ↦ `1`. -/
def w18 : EColouring 18 2 := fun e =>
  cond (cb ((ofLex e.val).1.val + 1) ((ofLex e.val).2.val + 1)) 1 0

lemma eval_w18_mkEdge {u v : Vtx} (h : u ≠ v) :
    w18 (mkEdge u v h) = cond (bb u v) 1 0 := by
  rcases lt_or_gt_of_ne h with hl | hg
  · simp [w18, bb, mkEdge_pos h hl, hl]
  · simp only [bb, if_neg (not_lt.2 hg.le)]
    rw [mkEdge_neg h hg]
    simp [w18]

lemma eq_c_iff {c : Fin 2} (b : Bool) :
    (cond b 1 0 = c) ↔ (decide b = decide (c == 1)) := by
  revert b
  fin_cases c <;> intros b <;> cases b <;> simp [Fin.isValue]

/-- Mathematical bridge: an edge is colour-`c` iff its table bit matches `c`. -/
lemma mem_edge_iff (c : Fin 2) (u v : Vtx) :
    colourRel w18 c u v ↔ (u ≠ v ∧ bb u v = (c == 1)) := by
  constructor
  · rintro ⟨hne, hc⟩
    rw [eval_w18_mkEdge hne, eq_c_iff] at hc
    exact ⟨hne, by simpa using hc⟩
  · rintro ⟨hne, hb⟩
    refine ⟨hne, ?_⟩
    rw [eval_w18_mkEdge hne]
    exact (eq_c_iff _).mpr (by simpa using hb)

/-- Boolean test "`{u, v}` is a colour-`c` edge". -/
def isC (c : Fin 2) (u v : Vtx) : Bool :=
  decide (u ≠ v) && decide (bb u v = (c == 1))

lemma colourRel_iff_isC (c : Fin 2) (u v : Vtx) :
    colourRel w18 c u v ↔ isC c u v = true := by
  rw [mem_edge_iff]
  simp [isC]

/-! ### Decidability, and the restricted form the checker evaluates -/

/-- `colourRel` on this concrete colouring is decidable, which is what lets the
statement below be settled by evaluation. -/
instance instDecColourRel (c : Fin 2) (u v : Vtx) : Decidable (colourRel w18 c u v) :=
  decidable_of_iff _ (colourRel_iff_isC c u v).symm

/-- All `s`-element vertex subsets. -/
abbrev subsetsF (s : ℕ) : Finset (Finset Vtx) :=
  Finset.powersetCard s (Finset.univ : Finset Vtx)

/-! ### The mathematical predicate -/

/-- **The mathematical predicate**: colour `c` contains no `K_{s,t}` — no pair
of disjoint vertex sets of sizes `s`, `t` with every one of the `s*t` crossing
edges coloured `c`. Edges inside `S` or inside `T` are unconstrained. This
quantifies over *all* finite vertex sets and mentions no checker. -/
def NoKst (c : Fin 2) (s t : ℕ) : Prop :=
  ∀ S T : Finset Vtx, Finset.card S = s → Finset.card T = t → Disjoint S T →
    ¬ (∀ u ∈ S, ∀ v ∈ T, colourRel w18 c u v)

/-! ### The codegree reformulation

Quantifying over pairs of subsets costs `C(18,3) * C(18,4)` ≈ 2.5M cases, which is
not evaluable in reasonable time. The standard reformulation — *colour `c` contains
a `K_{s,t}` iff some `s`-set has at least `t` common `c`-neighbours* — costs
`C(18,3) * 18` ≈ 15k. `codegree_iff` below proves the two agree, so nothing is
assumed; this is the same s-side/t-side duality the CNF encoder relies on. -/

/-- The common colour-`c` neighbourhood of `S`: vertices outside `S` joined to
every element of `S` by a colour-`c` edge. -/
def commonNbrs (c : Fin 2) (S : Finset Vtx) : Finset Vtx :=
  Finset.univ.filter fun v => v ∉ S ∧ ∀ u ∈ S, colourRel w18 c u v

/-- The evaluable statement: every `s`-set has fewer than `t` common
`c`-neighbours. -/
abbrev SmallCodegree (c : Fin 2) (s t : ℕ) : Prop :=
  ∀ S ∈ subsetsF s, Finset.card (commonNbrs c S) < t

/-- **The bridge.** A monochromatic `K_{s,t}` in colour `c` exists exactly when
some `s`-set has `t` or more common `c`-neighbours. Forward: the `t`-side of a
copy sits inside the common neighbourhood. Backward: any `t`-subset of a large
enough common neighbourhood *is* the `t`-side of a copy. -/
lemma codegree_iff (c : Fin 2) (s t : ℕ) : NoKst c s t ↔ SmallCodegree c s t := by
  constructor
  · intro h S hS
    by_contra hcon
    push Not at hcon
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcon
    refine h S T (Finset.mem_powersetCard.mp hS).2 hTcard ?_ ?_
    · rw [Finset.disjoint_right]
      intro v hv hvS
      exact (Finset.mem_filter.mp (hTsub hv)).2.1 hvS
    · intro u hu v hv
      exact (Finset.mem_filter.mp (hTsub hv)).2.2 u hu
  · intro h S T hS hT hd hcross
    have hTsub : T ⊆ commonNbrs c S := by
      intro v hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact fun hvS => (Finset.disjoint_left.mp hd hvS) hv
      · intro u hu; exact hcross u hu v hv
    have : t ≤ Finset.card (commonNbrs c S) := hT ▸ Finset.card_le_card hTsub
    exact absurd this (Nat.not_le.mpr (h S (Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hS⟩)))

/-- **The witness theorem.** The explicit colouring `w18` of `K_18` has no
monochromatic `K_{3,4}` in colour `0` and no monochromatic `K_{3,3}` in colour
`1`, witnessing `R(K_{3,4}, K_{3,3}) > 18`. -/
theorem witness18 : NoKst 0 3 4 ∧ NoKst 1 3 3 :=
  ⟨(codegree_iff 0 3 4).mpr (by native_decide),
   (codegree_iff 1 3 3).mpr (by native_decide)⟩

#print axioms witness18

end SB.Witness18
