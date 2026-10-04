import Sbsound.Codegree

/-!
# A concrete witness: `R(K_{3,5}, K_{2,5}) > 21`, checked by the kernel

An explicit 2-colouring `w21` of the edges of `K_21` such that colour `0` contains no `K_{3,5}` and
colour `1` contains no `K_{2,5}`. The colouring is the deposited witness
`ramsey-cells/k35k25-lb22/witness/witness_k35k25_n21.txt`: its colour 1 is colour `0` here, its colour 2
is colour `1`.

The statement is `SB.NoKst`, the predicate used by the refutation side, so the two halves of
`R(K_{3,5}, K_{2,5}) = 22` are stated in one vocabulary. Every evaluation is `decide +kernel`; the axioms
are the three standard ones (see `#print axioms` at the foot).

As in `Witness18Kernel`:
* the table is one natural number, `MASK`: bit `u * 21 + v` is set iff `{u, v}` has colour `1`;
  `bb_symm` checks that the table is symmetric, which is all `w21` needs to be well defined on edges;
* common neighbours are counted over `List.finRange 21` for sorted triples and pairs, and
  `card_commonNbrs3` / `card_commonNbrs2` prove these counts are the cardinalities in `SB.SmallCodegree`.
-/

namespace SB.Witness21

open SB

/-- The vertices of `K_21`. -/
abbrev Vtx := Fin 21

/-- The table as one number: bit `u * 21 + v` is set iff `{u, v}` has colour `1`. -/
def MASK : Nat := 710320805683094273187958777625483226594442674756763210651783736010802021202270364990019218943111822749266136065365676735047611179008

/-- Table bit of the ordered pair `(u, v)`. -/
def bb (u v : Vtx) : Bool := Nat.testBit MASK (u.val * 21 + v.val)

set_option maxRecDepth 100000 in
theorem bb_symm : ∀ u v : Vtx, bb u v = bb v u := by decide +kernel

/-- The witness colouring: table bit `false` ↦ colour `0`, `true` ↦ colour `1`. -/
def w21 : EColouring 21 2 := fun e => cond (bb (ofLex e.val).1 (ofLex e.val).2) 1 0

lemma eval_w21_mkEdge {u v : Vtx} (h : u ≠ v) : w21 (mkEdge u v h) = cond (bb u v) 1 0 := by
  rcases lt_or_gt_of_ne h with hl | hg
  · rw [mkEdge_pos h hl]; rfl
  · rw [mkEdge_neg h hg, bb_symm u v]; rfl

lemma eq_c_iff {c : Fin 2} (b : Bool) :
    (cond b 1 0 = c) ↔ (decide b = decide (c == 1)) := by
  revert b
  fin_cases c <;> intros b <;> cases b <;> simp [Fin.isValue]

/-- Boolean test "`{u, v}` is a colour-`c` edge". -/
def isC (c : Fin 2) (u v : Vtx) : Bool :=
  decide (u ≠ v) && decide (bb u v = (c == 1))

lemma colourRel_iff_isC (c : Fin 2) (u v : Vtx) :
    colourRel w21 c u v ↔ isC c u v = true := by
  constructor
  · rintro ⟨hne, hc⟩
    rw [eval_w21_mkEdge hne, eq_c_iff] at hc
    simp only [isC, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hne, by simpa using hc⟩
  · intro h
    simp only [isC, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨h.1, ?_⟩
    rw [eval_w21_mkEdge h.1]
    exact (eq_c_iff _).mpr (by simpa using h.2)

/-! ### Triples (colour `0`, `K_{3,5}`) -/

/-- Common colour-`c` neighbours of `{a, b, d}`, counted over the explicit vertex list. -/
def cnt3 (c : Fin 2) (a b d : Vtx) : Nat :=
  (List.finRange 21).countP fun v => decide (v ≠ a) && decide (v ≠ b) && decide (v ≠ d)
    && isC c a v && isC c b v && isC c d v

theorem card_commonNbrs3 (c : Fin 2) (a b d : Vtx) :
    (commonNbrs w21 c {a, b, d}).card = cnt3 c a b d := by
  rw [commonNbrs, Finset.card_def, Finset.filter_val, ← Multiset.countP_eq_card_filter,
    Finset.val_univ_fin, Multiset.coe_countP, cnt3]
  apply List.countP_congr
  intro v _
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, forall_eq_or_imp, forall_eq,
    colourRel_iff_isC, Bool.and_eq_true, decide_eq_true_eq, ne_eq]
  tauto

/-- Three distinct vertices, listed in increasing order. -/
theorem triple_sorted {x y z : Vtx} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ a b d : Vtx, a < b ∧ b < d ∧ ({x, y, z} : Finset Vtx) = {a, b, d} := by
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;>
  rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
  rcases lt_or_gt_of_ne hyz with h3 | h3
  all_goals first
    | exact ⟨x, y, z, by assumption, by assumption, rfl⟩
    | exact ⟨x, z, y, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨y, x, z, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨y, z, x, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨z, x, y, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨z, y, x, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩

theorem smallCodegree3_of_cnt (c : Fin 2) (t : ℕ)
    (h : ∀ a b d : Vtx, a < b → b < d → cnt3 c a b d < t) : SmallCodegree w21 c 3 t := by
  intro S hS
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ :=
    Finset.card_eq_three.mp (Finset.mem_powersetCard.mp hS).2
  obtain ⟨a, b, d, hab, hbd, he⟩ := triple_sorted hxy hxz hyz
  rw [he, card_commonNbrs3]
  exact h a b d hab hbd

set_option maxRecDepth 100000 in
theorem cnt3_035 : ∀ a b d : Vtx, a < b → b < d → cnt3 0 a b d < 5 := by decide +kernel

/-! ### Pairs (colour `1`, `K_{2,5}`) -/

/-- Common colour-`c` neighbours of `{a, b}`, counted over the explicit vertex list. -/
def cnt2 (c : Fin 2) (a b : Vtx) : Nat :=
  (List.finRange 21).countP fun v => decide (v ≠ a) && decide (v ≠ b) && isC c a v && isC c b v

theorem card_commonNbrs2 (c : Fin 2) (a b : Vtx) :
    (commonNbrs w21 c {a, b}).card = cnt2 c a b := by
  rw [commonNbrs, Finset.card_def, Finset.filter_val, ← Multiset.countP_eq_card_filter,
    Finset.val_univ_fin, Multiset.coe_countP, cnt2]
  apply List.countP_congr
  intro v _
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, forall_eq_or_imp, forall_eq,
    colourRel_iff_isC, Bool.and_eq_true, decide_eq_true_eq, ne_eq]
  tauto

theorem smallCodegree2_of_cnt (c : Fin 2) (t : ℕ)
    (h : ∀ a b : Vtx, a < b → cnt2 c a b < t) : SmallCodegree w21 c 2 t := by
  intro S hS
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hS).2
  rcases lt_or_gt_of_ne hxy with hl | hg
  · rw [card_commonNbrs2]; exact h x y hl
  · rw [Finset.pair_comm, card_commonNbrs2]; exact h y x hg

set_option maxRecDepth 100000 in
theorem cnt2_125 : ∀ a b : Vtx, a < b → cnt2 1 a b < 5 := by decide +kernel

/-- **The witness theorem, kernel-checked.** `w21` has no `K_{3,5}` in colour `0` and no `K_{2,5}` in
colour `1`, so `R(K_{3,5}, K_{2,5}) > 21`. -/
theorem witness21_kernel : NoKst w21 0 3 5 ∧ NoKst w21 1 2 5 :=
  ⟨(codegree_iff w21 0 3 5).mpr (smallCodegree3_of_cnt 0 5 cnt3_035),
   (codegree_iff w21 1 2 5).mpr (smallCodegree2_of_cnt 1 5 cnt2_125)⟩

end SB.Witness21

#print axioms SB.Witness21.witness21_kernel
