/-
# M5: the cube table discharges M4's two hypotheses

* `C = rows.map Row.toCube` is the cube list of `no_good_K22_of_cubes` (M4).
* `hcubes_of`: M4's listed-word ↔ cube correspondence, from the kernel checks of the table
  (`caseOKB` on every case, `keyB` on every census index tuple) and `famH_spec`.
* `hU_of`: the per-cube refutations. A `direct` row: `direct_cakelpr` and `no_canon_of_unsat` (M3). A
  `split` row: `leaves_cakelpr`, the kernel-checked `coversB` and `no_canon_of_children_unsat` (M3). If
  the encoder had returned an error, the axiom would assert that the empty CNF is unsatisfiable, which is
  refuted (`not_unsat_empty`); so no kernel evaluation of `rootedFormula` is needed.
  A `pending` row is a hypothesis `hP` (rows whose verdict is not attached yet).
* `no_good_K22_of_pending`: no good colouring of `K_22`, given the checks and `hP`.

The closed form (checks instantiated, no pending rows) is `RootedM5/Close.lean`.
-/
import RootedM5.Axioms
import RootedM5.Keys
import RootedM5.CheckDefs
import RootedM4.Census

namespace SB.Rooted.M5
open SB SB.Rooted SB.Rooted.M4 SB.Rooted.M4.Cover SB.Rooted.M4.CoverData SB.BipBridge LRATCatcher.Rooted

/-- A row as an M4 cube. -/
def Row.toCube (r : Row) : Cube :=
  { degs := histDegs r.n8 r.n9 r.n10, k := rootOf r.n8 r.n10, comp := compF r.v8 r.v9 r.v10,
    H := r.e.H, o := r.e.os.opts }

/-- The cube list. -/
def C : List Cube := rows.map Row.toCube

theorem formula_eq (r : Row) : r.formula =
    rootedFormula 22 ["K2x8", "K2x5"] r.toCube.degs r.toCube.k r.toCube.comp r.toCube.H r.toCube.o := rfl

theorem not_unsat_toCNFV_nil : ¬ (toCNFV ([] : List (List Int))).Unsat :=
  Std.Sat.CNF.not_unsat_empty

theorem mem_rows {r : Row} (hr : r ∈ rows) : ∃ c ∈ table, r.e ∈ c.entries ∧
    r = Row.mk c.n8 c.n9 c.n10 c.v8 c.v9 c.v10 r.e := by
  obtain ⟨c, hc, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
  exact ⟨c, hc, he, rfl⟩

theorem zip_get {α β : Type} (l₁ : List α) (l₂ : List β) (p : α → β → Bool)
    (hl : l₁.length = l₂.length) (h : (l₁.zip l₂).all (fun q => p q.1 q.2) = true) {b : β} (hb : b ∈ l₂) :
    ∃ a ∈ l₁, p a b = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have hi' : i < l₁.length := hl ▸ hi
  refine ⟨l₁[i], List.getElem_mem hi', ?_⟩
  have hz : (l₁[i], l₂[i]) ∈ l₁.zip l₂ := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [List.length_zip]; omega, by simp⟩
  exact List.all_eq_true.mp h _ hz

section
variable (htab : table.all caseOKB = true)
include htab

theorem verdict_ok {r : Row} (hr : r ∈ rows) : verdictOKB r.e.v = true := by
  obtain ⟨c, hc, he, -⟩ := mem_rows hr
  have h := List.all_eq_true.mp htab c hc
  unfold caseOKB at h
  simp only [Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.2 _ he

variable (hkeys : ∀ n8 < 8, ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, keyB n8 n10 v8 v9 = true)
include hkeys

/-- **M4's `hcubes` for `C`.** -/
theorem hcubes_of : ∀ n8 n9 n10 v8 v9 v10, ValidCase n8 n9 n10 v8 v9 v10 →
    ∀ wb ∈ listedWords (certOf (rootOf n8 n10) v8 v9 v10), ∃ c ∈ C,
      c.degs = histDegs n8 n9 n10 ∧ c.k = rootOf n8 n10 ∧ c.comp = compF v8 v9 v10 ∧
      c.H = wordEdges (rootOf n8 n10) wb ∧ c.o.shortfall = false := by
  intro n8 n9 n10 v8 v9 v10 hv wb hwb
  have hval := validB_of hv
  have hk := rootOf_mem n8 n10
  obtain ⟨h8, h10, hsum, -, hcomp, -, -, -⟩ := hv
  have hkey := hkeys n8 h8 n10 h10 v8 (by omega) v9 (by omega)
  have e9 : n9 = 22 - n8 - n10 := by omega
  have e10 : v10 = rootOf n8 n10 - v8 - v9 := by omega
  subst e9 e10
  unfold keyB at hkey
  simp only [hval, Bool.not_true, Bool.false_or] at hkey
  obtain ⟨c, hc, hck⟩ := List.any_eq_true.mp hkey
  simp only [Bool.and_eq_true, beq_iff_eq] at hck
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hck
  have hok := List.all_eq_true.mp htab c hc
  unfold caseOKB at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hok
  obtain ⟨⟨⟨-, hfam⟩, hmap⟩, -⟩ := hok
  rw [h1, h3, h4, h5, h6] at hfam hmap
  have hspec := famH_spec _ hfam
  simp only at hspec
  have hw : wordEdges (rootOf n8 n10) wb ∈ c.entries.map Entry.H := by
    rw [hmap, ← hspec]; exact List.mem_map_of_mem hwb
  obtain ⟨e, he, hH⟩ := List.mem_map.mp hw
  refine ⟨(Row.mk c.n8 c.n9 c.n10 c.v8 c.v9 c.v10 e).toCube,
    List.mem_map.mpr ⟨_, List.mem_flatMap.mpr ⟨c, hc, List.mem_map.mpr ⟨e, he, rfl⟩⟩, rfl⟩, ?_⟩
  simp only [Row.toCube, h1, h2, h3, h4, h5, h6, OptSet.shortfall_false, and_true, true_and]
  exact hH

end

/-- **M4's `hU` for `C`**, from the verdict axioms, the `coversB` checks and `hP` for pending rows. -/
theorem hU_of (htab : table.all caseOKB = true)
    (hP : ∀ r ∈ rows, r.e.v = .pending → ∀ cells : Cells,
      cellsOf 22 r.toCube.degs r.toCube.k r.toCube.comp = .ok cells → CubeWF cells →
      ¬ ∃ a : EColouring 22 2, NoKst a 0 2 8 ∧ NoKst a 1 2 5 ∧
        RootedCanon a r.toCube.k cells (normH r.toCube.H) r.toCube.o) :
    ∀ c ∈ C, ∀ cells : Cells, cellsOf 22 c.degs c.k c.comp = .ok cells → CubeWF cells →
      c.o.shortfall = false →
      ¬ ∃ a : EColouring 22 2, NoKst a 0 2 8 ∧ NoKst a 1 2 5 ∧ RootedCanon a c.k cells (normH c.H) c.o := by
  intro c hc cells hcells hwf hsf
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
  match hv : r.e.v with
  | .direct =>
    have hax := direct_cakelpr r hr hv
    match hF : r.formula with
    | .error _ =>
      exfalso
      simp only [Row.clauses, hF] at hax
      exact not_unsat_toCNFV_nil hax
    | .ok F =>
      refine no_canon_of_unsat _ _ _ _ _ F ((formula_eq r).symm.trans hF) cells hcells hwf hsf ?_
      simpa only [Row.clauses, hF, fCNF] using hax
  | .split t n us =>
    have hcov : coversB n us = true := by
      have := verdict_ok htab hr
      rw [hv] at this
      exact this
    have hax := leaves_cakelpr r hr t n us hv
    match hF : r.formula with
    | .error _ =>
      exfalso
      cases us with
      | nil => cases n <;> simp [coversB] at hcov
      | cons u _ =>
        have h1 := hax u (List.mem_cons_self ..)
        simp only [Row.leafClauses, hF] at h1
        exact not_unsat_toCNFV_nil h1
    | .ok F =>
      refine no_canon_of_children_unsat _ _ _ _ _ F ((formula_eq r).symm.trans hF) cells hcells hwf hsf
        t us n hcov ?_
      intro u hu
      have h1 := hax u hu
      simpa only [Row.leafClauses, hF, fCNF] using h1
  | .pending => exact hP r hr hv cells hcells hwf

/-- **No good colouring of `K_22`**, from the kernel checks of the table, the verdict axioms
(`direct_cakelpr`, `leaves_cakelpr`, `cover_cakelpr`) and `hP` for the rows still pending. -/
theorem no_good_K22_of_pending (htab : table.all caseOKB = true)
    (hkeys : ∀ n8 < 8, ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, keyB n8 n10 v8 v9 = true)
    (hP : ∀ r ∈ rows, r.e.v = .pending → ∀ cells : Cells,
      cellsOf 22 r.toCube.degs r.toCube.k r.toCube.comp = .ok cells → CubeWF cells →
      ¬ ∃ a : EColouring 22 2, NoKst a 0 2 8 ∧ NoKst a 1 2 5 ∧
        RootedCanon a r.toCube.k cells (normH r.toCube.H) r.toCube.o) :
    ¬ ∃ b : EColouring 22 2, NoKst b 0 2 8 ∧ NoKst b 1 2 5 :=
  no_good_K22_of_cubes C (hcubes_of htab hkeys) (hU_of htab hP)

end SB.Rooted.M5

#print axioms SB.Rooted.M5.hcubes_of
#print axioms SB.Rooted.M5.hU_of
#print axioms SB.Rooted.M5.no_good_K22_of_pending
