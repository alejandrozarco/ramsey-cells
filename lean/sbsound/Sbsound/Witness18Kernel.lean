import Sbsound.Witness18

/-!
# The K_18 witness, checked by the kernel instead of by `native_decide`

`SB.Witness18.witness18` settles the two codegree checks with `native_decide`, which puts the Lean
compiler in the trusted base. `witness18_kernel` below proves the same statement with
`decide +kernel` only, so its axioms are the three standard ones.

Two things make the kernel's job small enough:
* the colour table is read from one natural number, `MASK` (bit `u*18+v` is `bb u v`), with
  `Nat.testBit`, instead of through the 153-case match `cb`; `bb_eq_bbM` proves the two agree on
  all 324 vertex pairs;
* the 3-vertex sets are enumerated as ordered triples `a < b < d` and common neighbours are counted
  over `List.finRange 18` (`cntM`), instead of through `Finset.powersetCard` and `Finset.filter`,
  whose kernel evaluation needed more than 10 GB (measured 2026-09-17).
`card_commonNbrs` and `smallCodegree_of_cnt` show that this is the same statement as `SmallCodegree`.
-/

namespace SB.Witness18

/-- The table as one number: bit `u * 18 + v` is `bb u v` (so the matrix is symmetric, diagonal 0). -/
def MASK : Nat := 13027081767587175303715579514337240323349636949447911970751316935205334509757413675743138526996600

/-- Table bit of `{u, v}`, read from `MASK`. -/
def bbM (u v : Vtx) : Bool := Nat.testBit MASK (u.val * 18 + v.val)

set_option maxRecDepth 100000 in
theorem bb_eq_bbM : ∀ u v : Vtx, bb u v = bbM u v := by decide +kernel

/-- `isC` with the table read from `MASK`. -/
def isCM (c : Fin 2) (u v : Vtx) : Bool := decide (u ≠ v) && (bbM u v == (c == 1))

theorem colourRel_iff_isCM (c : Fin 2) (u v : Vtx) :
    colourRel w18 c u v ↔ isCM c u v = true := by
  rw [colourRel_iff_isC]
  simp [isC, isCM, bb_eq_bbM]

/-- Common colour-`c` neighbours of `{a, b, d}`, counted over the explicit vertex list. -/
def cntM (c : Fin 2) (a b d : Vtx) : Nat :=
  (List.finRange 18).countP fun v => decide (v ≠ a) && decide (v ≠ b) && decide (v ≠ d)
    && isCM c a v && isCM c b v && isCM c d v

theorem card_commonNbrs (c : Fin 2) (a b d : Vtx) :
    (commonNbrs c {a, b, d}).card = cntM c a b d := by
  rw [commonNbrs, Finset.card_def, Finset.filter_val, ← Multiset.countP_eq_card_filter,
    Finset.val_univ_fin, Multiset.coe_countP, cntM]
  apply List.countP_congr
  intro v _
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, forall_eq_or_imp, forall_eq,
    colourRel_iff_isCM, Bool.and_eq_true, decide_eq_true_eq, ne_eq]
  tauto

/-- Three distinct vertices, listed in increasing order. (In the two contradictory sign patterns one of
the six listings still type-checks, so no separate contradiction branch is needed.) -/
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

theorem smallCodegree_of_cnt (c : Fin 2) (t : ℕ)
    (h : ∀ a b d : Vtx, a < b → b < d → cntM c a b d < t) : SmallCodegree c 3 t := by
  intro S hS
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ :=
    Finset.card_eq_three.mp (Finset.mem_powersetCard.mp hS).2
  obtain ⟨a, b, d, hab, hbd, he⟩ := triple_sorted hxy hxz hyz
  rw [he, card_commonNbrs]
  exact h a b d hab hbd

set_option maxRecDepth 100000 in
theorem cnt_034 : ∀ a b d : Vtx, a < b → b < d → cntM 0 a b d < 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cnt_133 : ∀ a b d : Vtx, a < b → b < d → cntM 1 a b d < 3 := by decide +kernel

/-- **The witness theorem, kernel-checked.** Same statement as `witness18`, no `native_decide`. -/
theorem witness18_kernel : NoKst 0 3 4 ∧ NoKst 1 3 3 :=
  ⟨(codegree_iff 0 3 4).mpr (smallCodegree_of_cnt 0 4 cnt_034),
   (codegree_iff 1 3 3).mpr (smallCodegree_of_cnt 1 3 cnt_133)⟩

#print axioms witness18_kernel

end SB.Witness18
