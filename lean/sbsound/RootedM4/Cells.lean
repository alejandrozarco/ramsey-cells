/-
# M4, part 1: the semantics of `cellsOf` on the census cases

`cellsOf` sorts the distinct degrees with `List.mergeSort`, which is defined by well-founded
recursion and does not reduce in the kernel. `cellsOfK` is the same program with
`List.insertionSort`; `cellsOf_eq_K` identifies the two (Mathlib's `mergeSort_eq_insertionSort`).

A census case is an admissible histogram `(n8, n9, n10)` (Lemma 1.2 / `histogram_membership`), the
root degree `k = rootOf n8 n10` (8 if `n8 > 0`, else 10 if `n10 > 0`, else 9) and a composition
`(v8, v9, v10)` of `k` with `v_d + [d = k] ≤ n_d`. `degs = histDegs n8 n9 n10` (the census's sorted
degree list) and the composition is passed zero-filtered (`compF`), the convention under which
every eligible ledger row reproduces its `cnf_sha256` (M2 RESULTS: no row matches only unfiltered).

`census_cells`: for every census case, `cellsOf` returns `.ok cells` for the zero-filtered composition
(the convention every ledger row matches, M2 RESULTS), and `cells` satisfies `CellsSem` (root degree, per-degree counts on `N` and on `W`, the
N-degree vector in cell order, every N-cell inside `2..k+1` with constant degree, every W-cell
inside `k+2..22` with constant degree, `CubeWF`). It is proved by one kernel evaluation over all
`8 · 11 · 11 · 11` index tuples (`caseB_all`, `decide +kernel`) and a general soundness lemma for the
Boolean check (`cellsSem_of_B`).
-/
import RootedM4.Defs
import RootedBridge.Canon
import Mathlib.Data.List.Sort

set_option linter.unusedVariables false

namespace SB.Rooted.M4
open LRATCatcher.Rooted SB.Rooted

/-- `cellsOf` with `insertionSort` in place of `mergeSort` (kernel-reducible). -/
def cellsOfK (N : Nat) (degs : List Nat) (k : Nat) (comp : List (Nat × Nat)) :
    Except String Cells := do
  let vals := (degs.eraseDups).insertionSort (· ≤ ·)
  let count := fun d => degs.count d
  if count k < 1 then throw "root degree not present"
  let rest := fun d => if d == k then count d - 1 else count d
  for (d, c) in comp do
    if !(rest d ≥ c) then
      throw s!"composition needs {c} neighbours of degree {d}, only {rest d} available"
  if (comp.map (·.2)).sum != k then throw "composition must sum to the root degree"
  let mut D : Array Nat := #[k]
  let mut ncells := #[]
  let mut wcells := #[]
  let mut pos := 2
  for d in vals do
    let c := lookup comp d
    if c != 0 then
      ncells := ncells.push (pos, pos + c - 1, d)
      for _ in [0:c] do D := D.push d
      pos := pos + c
  for d in vals do
    let c := rest d - lookup comp d
    if c != 0 then
      wcells := wcells.push (pos, pos + c - 1, d)
      for _ in [0:c] do D := D.push d
      pos := pos + c
  if D.size != N then throw "len(D) != N"
  return ⟨D, ncells, wcells⟩

theorem cellsOf_eq_K : cellsOf = cellsOfK := by
  funext N degs k comp
  unfold cellsOf cellsOfK
  rw [List.mergeSort_eq_insertionSort]

/-! ## The census index -/

/-- The root rule of the census (`rooted_gen_lists.py`, M0 RESULTS): 8, else 10, else 9. -/
def rootOf (n8 n10 : Nat) : Nat := if 0 < n8 then 8 else if 0 < n10 then 10 else 9

/-- The entry for degree `d` of a triple indexed by the degrees `8, 9, 10` (0 elsewhere). -/
def pick (x8 x9 x10 d : Nat) : Nat :=
  if d = 8 then x8 else if d = 9 then x9 else if d = 10 then x10 else 0

/-- The composition dict, unfiltered: `{8: v8, 9: v9, 10: v10}`. -/
def compU (v8 v9 v10 : Nat) : List (Nat × Nat) := [(8, v8), (9, v9), (10, v10)]

/-- The composition dict with zero classes dropped (`rooted_run.py`). -/
def compF (v8 v9 v10 : Nat) : List (Nat × Nat) := (compU v8 v9 v10).filter (fun p => p.2 != 0)

/-- `[d = k]` as a number. -/
def ind (d k : Nat) : Nat := if d = k then 1 else 0

/-- A census case. -/
structure ValidCase (n8 n9 n10 v8 v9 v10 : Nat) : Prop where
  h8 : n8 < 8
  h10 : n10 < 11
  hsum : n8 + n9 + n10 = 22
  hpar : (n8 + n10) % 2 = 0
  hcomp : v8 + v9 + v10 = rootOf n8 n10
  hv8 : v8 + ind 8 (rootOf n8 n10) ≤ n8
  hv9 : v9 + ind 9 (rootOf n8 n10) ≤ n9
  hv10 : v10 + ind 10 (rootOf n8 n10) ≤ n10

def validB (n8 n9 n10 v8 v9 v10 : Nat) : Bool :=
  decide (n8 < 8) && decide (n10 < 11) && decide (n8 + n9 + n10 = 22) && decide ((n8 + n10) % 2 = 0) &&
  decide (v8 + v9 + v10 = rootOf n8 n10) && decide (v8 + ind 8 (rootOf n8 n10) ≤ n8) &&
  decide (v9 + ind 9 (rootOf n8 n10) ≤ n9) && decide (v10 + ind 10 (rootOf n8 n10) ≤ n10)

theorem validB_of {n8 n9 n10 v8 v9 v10 : Nat} (h : ValidCase n8 n9 n10 v8 v9 v10) :
    validB n8 n9 n10 v8 v9 v10 = true := by
  obtain ⟨a, b, c, d, e, f, g, i⟩ := h
  simp [validB, a, b, c, d, e, f, g, i]

theorem rootOf_mem (n8 n10 : Nat) : rootOf n8 n10 = 8 ∨ rootOf n8 n10 = 9 ∨ rootOf n8 n10 = 10 := by
  unfold rootOf; split_ifs <;> simp

/-! ## The Boolean check and its meaning -/

/-- Positions `2..k+1` (encoder numbering) of degree `d`. -/
def cntN (D : Array Nat) (k d : Nat) : Nat :=
  ((List.range' 1 22).filter (fun u => decide (2 ≤ u) && decide (u ≤ k + 1) && D.toList[u - 1]! == d)).length

/-- Positions `k+2..22` of degree `d`. -/
def cntW (D : Array Nat) (k d : Nat) : Nat :=
  ((List.range' 1 22).filter (fun u => decide (k + 2 ≤ u) && D.toList[u - 1]! == d)).length

def cellsOKB (n8 n9 n10 v8 v9 v10 : Nat) (c : Cells) : Bool :=
  let k := rootOf n8 n10
  let D := c.D.toList
  (D.length == 22) && (D[0]! == k) &&
  (List.range 22).all (fun x => D[x]! == 8 || D[x]! == 9 || D[x]! == 10) &&
  [8, 9, 10].all (fun d => cntN c.D k d == pick v8 v9 v10 d &&
    cntW c.D k d == pick n8 n9 n10 d - ind d k - pick v8 v9 v10 d) &&
  (List.range k).all (fun i => D[i + 1]! == (histDegs v8 v9 v10)[i]!) &&
  c.ncells.toList.all (fun cl => decide (2 ≤ cl.1) && decide (cl.2.1 ≤ k + 1) &&
    (List.range' cl.1 (cl.2.1 + 1 - cl.1)).all (fun u => D[u - 1]! == cl.2.2)) &&
  c.wcells.toList.all (fun cl => decide (k + 2 ≤ cl.1) && decide (cl.2.1 ≤ 22) &&
    (List.range' cl.1 (cl.2.1 + 1 - cl.1)).all (fun u => D[u - 1]! == cl.2.2)) &&
  decide (cellVerts (nCellArrays c)).Nodup

/-- What M4 uses of a cube's cells. -/
structure CellsSem (n8 n9 n10 v8 v9 v10 : Nat) (c : Cells) : Prop where
  size : c.D.size = 22
  root : c.D[0]! = rootOf n8 n10
  range : ∀ x, x < 22 → c.D[x]! = 8 ∨ c.D[x]! = 9 ∨ c.D[x]! = 10
  cntN : ∀ d ∈ [8, 9, 10], cntN c.D (rootOf n8 n10) d = pick v8 v9 v10 d
  cntW : ∀ d ∈ [8, 9, 10],
    cntW c.D (rootOf n8 n10) d = pick n8 n9 n10 d - ind d (rootOf n8 n10) - pick v8 v9 v10 d
  nword : ∀ i, i < rootOf n8 n10 → c.D[i + 1]! = (histDegs v8 v9 v10)[i]!
  ncell : ∀ cl ∈ c.ncells, 2 ≤ cl.1 ∧ cl.2.1 ≤ rootOf n8 n10 + 1 ∧
    ∀ u, cl.1 ≤ u → u ≤ cl.2.1 → c.D[u - 1]! = cl.2.2
  wcell : ∀ cl ∈ c.wcells, rootOf n8 n10 + 2 ≤ cl.1 ∧ cl.2.1 ≤ 22 ∧
    ∀ u, cl.1 ≤ u → u ≤ cl.2.1 → c.D[u - 1]! = cl.2.2
  wf : CubeWF c

theorem cellsSem_of_B {n8 n9 n10 v8 v9 v10 : Nat} {c : Cells}
    (h : cellsOKB n8 n9 n10 v8 v9 v10 c = true) : CellsSem n8 n9 n10 v8 v9 v10 c := by
  unfold cellsOKB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    List.mem_range, List.mem_range'_1, Array.getElem!_toList, Array.length_toList] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have hk := rootOf_mem n8 n10
  have hn : ∀ cl ∈ c.ncells, 2 ≤ cl.1 ∧ cl.2.1 ≤ rootOf n8 n10 + 1 ∧
      ∀ u, cl.1 ≤ u → u ≤ cl.2.1 → c.D[u - 1]! = cl.2.2 := by
    intro cl hcl
    obtain ⟨⟨a, b⟩, d⟩ := h6 cl (Array.mem_toList_iff.mpr hcl)
    exact ⟨a, b, fun u h1 h2 => d u ⟨h1, by omega⟩⟩
  have hw : ∀ cl ∈ c.wcells, rootOf n8 n10 + 2 ≤ cl.1 ∧ cl.2.1 ≤ 22 ∧
      ∀ u, cl.1 ≤ u → u ≤ cl.2.1 → c.D[u - 1]! = cl.2.2 := by
    intro cl hcl
    obtain ⟨⟨a, b⟩, d⟩ := h7 cl (Array.mem_toList_iff.mpr hcl)
    exact ⟨a, b, fun u h1 h2 => d u ⟨h1, by omega⟩⟩
  refine ⟨h1, h2, fun x hx => ?_, fun d hd => (h4 d hd).1, fun d hd => ?_, h5, hn, hw, ?_⟩
  · rcases h3 x hx with (a | a) | a
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
    · exact Or.inr (Or.inr a)
  · have := (h4 d hd).2
    simpa [ind] using this
  · refine ⟨fun cl hcl => ?_, fun v hv => ?_, h8⟩
    · have := hw cl hcl; omega
    · obtain ⟨arr, harr, hvarr⟩ := mem_cellVerts.mp hv
      unfold nCellArrays at harr
      obtain ⟨cl, hcl, rfl⟩ := Array.mem_map.mp harr
      have hv' : v ∈ List.range' cl.1 (cl.2.1 + 1 - cl.1) := by simpa using hvarr
      rw [List.mem_range'_1] at hv'
      have := hn cl hcl
      rcases hk with hk | hk | hk <;> omega

/-! ## The kernel evaluation over all census cases -/

def caseB (n8 n10 v8 v9 : Nat) : Bool :=
  let n9 := 22 - n8 - n10
  let k := rootOf n8 n10
  let v10 := k - v8 - v9
  if validB n8 n9 n10 v8 v9 v10 then
    match cellsOfK 22 (histDegs n8 n9 n10) k (compF v8 v9 v10) with
    | .ok c => cellsOKB n8 n9 n10 v8 v9 v10 c
    | .error _ => false
  else true

/-! The kernel evaluation is cut into 88 slices `(n8, n10)` (2026-10-07, M5): one `decide +kernel` over
all 10,648 tuples needed more than 9 GB; each slice is a separate declaration, so the kernel's cache is
released between slices. -/
theorem caseB_0_0 : ∀ v8 < 11, ∀ v9 < 11, caseB 0 0 v8 v9 = true := by decide +kernel
theorem caseB_0_1 : ∀ v8 < 11, ∀ v9 < 11, caseB 0 1 v8 v9 = true := by decide +kernel
theorem caseB_0_2 : ∀ v8 < 11, ∀ v9 < 11, caseB 0 2 v8 v9 = true := by decide +kernel
theorem caseB_0_3 : ∀ v8 < 11, ∀ v9 < 11, caseB 0 3 v8 v9 = true := by decide +kernel
theorem caseB_0_4 : ∀ v8 < 11, ∀ v9 < 11, caseB 0 4 v8 v9 = true := by decide +kernel
theorem caseB_0_5 : ∀ v8 < 11, ∀ v9 < 11, caseB 0 5 v8 v9 = true := by decide +kernel
theorem caseB_0_6 : ∀ v8 < 11, ∀ v9 < 11, caseB 0 6 v8 v9 = true := by decide +kernel
theorem caseB_0_7 : ∀ v8 < 11, ∀ v9 < 11, caseB 0 7 v8 v9 = true := by decide +kernel
theorem caseB_0_8 : ∀ v8 < 11, ∀ v9 < 11, caseB 0 8 v8 v9 = true := by decide +kernel
theorem caseB_0_9 : ∀ v8 < 11, ∀ v9 < 11, caseB 0 9 v8 v9 = true := by decide +kernel
theorem caseB_0_10 : ∀ v8 < 11, ∀ v9 < 11, caseB 0 10 v8 v9 = true := by decide +kernel
theorem caseB_1_0 : ∀ v8 < 11, ∀ v9 < 11, caseB 1 0 v8 v9 = true := by decide +kernel
theorem caseB_1_1 : ∀ v8 < 11, ∀ v9 < 11, caseB 1 1 v8 v9 = true := by decide +kernel
theorem caseB_1_2 : ∀ v8 < 11, ∀ v9 < 11, caseB 1 2 v8 v9 = true := by decide +kernel
theorem caseB_1_3 : ∀ v8 < 11, ∀ v9 < 11, caseB 1 3 v8 v9 = true := by decide +kernel
theorem caseB_1_4 : ∀ v8 < 11, ∀ v9 < 11, caseB 1 4 v8 v9 = true := by decide +kernel
theorem caseB_1_5 : ∀ v8 < 11, ∀ v9 < 11, caseB 1 5 v8 v9 = true := by decide +kernel
theorem caseB_1_6 : ∀ v8 < 11, ∀ v9 < 11, caseB 1 6 v8 v9 = true := by decide +kernel
theorem caseB_1_7 : ∀ v8 < 11, ∀ v9 < 11, caseB 1 7 v8 v9 = true := by decide +kernel
theorem caseB_1_8 : ∀ v8 < 11, ∀ v9 < 11, caseB 1 8 v8 v9 = true := by decide +kernel
theorem caseB_1_9 : ∀ v8 < 11, ∀ v9 < 11, caseB 1 9 v8 v9 = true := by decide +kernel
theorem caseB_1_10 : ∀ v8 < 11, ∀ v9 < 11, caseB 1 10 v8 v9 = true := by decide +kernel
theorem caseB_2_0 : ∀ v8 < 11, ∀ v9 < 11, caseB 2 0 v8 v9 = true := by decide +kernel
theorem caseB_2_1 : ∀ v8 < 11, ∀ v9 < 11, caseB 2 1 v8 v9 = true := by decide +kernel
theorem caseB_2_2 : ∀ v8 < 11, ∀ v9 < 11, caseB 2 2 v8 v9 = true := by decide +kernel
theorem caseB_2_3 : ∀ v8 < 11, ∀ v9 < 11, caseB 2 3 v8 v9 = true := by decide +kernel
theorem caseB_2_4 : ∀ v8 < 11, ∀ v9 < 11, caseB 2 4 v8 v9 = true := by decide +kernel
theorem caseB_2_5 : ∀ v8 < 11, ∀ v9 < 11, caseB 2 5 v8 v9 = true := by decide +kernel
theorem caseB_2_6 : ∀ v8 < 11, ∀ v9 < 11, caseB 2 6 v8 v9 = true := by decide +kernel
theorem caseB_2_7 : ∀ v8 < 11, ∀ v9 < 11, caseB 2 7 v8 v9 = true := by decide +kernel
theorem caseB_2_8 : ∀ v8 < 11, ∀ v9 < 11, caseB 2 8 v8 v9 = true := by decide +kernel
theorem caseB_2_9 : ∀ v8 < 11, ∀ v9 < 11, caseB 2 9 v8 v9 = true := by decide +kernel
theorem caseB_2_10 : ∀ v8 < 11, ∀ v9 < 11, caseB 2 10 v8 v9 = true := by decide +kernel
theorem caseB_3_0 : ∀ v8 < 11, ∀ v9 < 11, caseB 3 0 v8 v9 = true := by decide +kernel
theorem caseB_3_1 : ∀ v8 < 11, ∀ v9 < 11, caseB 3 1 v8 v9 = true := by decide +kernel
theorem caseB_3_2 : ∀ v8 < 11, ∀ v9 < 11, caseB 3 2 v8 v9 = true := by decide +kernel
theorem caseB_3_3 : ∀ v8 < 11, ∀ v9 < 11, caseB 3 3 v8 v9 = true := by decide +kernel
theorem caseB_3_4 : ∀ v8 < 11, ∀ v9 < 11, caseB 3 4 v8 v9 = true := by decide +kernel
theorem caseB_3_5 : ∀ v8 < 11, ∀ v9 < 11, caseB 3 5 v8 v9 = true := by decide +kernel
theorem caseB_3_6 : ∀ v8 < 11, ∀ v9 < 11, caseB 3 6 v8 v9 = true := by decide +kernel
theorem caseB_3_7 : ∀ v8 < 11, ∀ v9 < 11, caseB 3 7 v8 v9 = true := by decide +kernel
theorem caseB_3_8 : ∀ v8 < 11, ∀ v9 < 11, caseB 3 8 v8 v9 = true := by decide +kernel
theorem caseB_3_9 : ∀ v8 < 11, ∀ v9 < 11, caseB 3 9 v8 v9 = true := by decide +kernel
theorem caseB_3_10 : ∀ v8 < 11, ∀ v9 < 11, caseB 3 10 v8 v9 = true := by decide +kernel
theorem caseB_4_0 : ∀ v8 < 11, ∀ v9 < 11, caseB 4 0 v8 v9 = true := by decide +kernel
theorem caseB_4_1 : ∀ v8 < 11, ∀ v9 < 11, caseB 4 1 v8 v9 = true := by decide +kernel
theorem caseB_4_2 : ∀ v8 < 11, ∀ v9 < 11, caseB 4 2 v8 v9 = true := by decide +kernel
theorem caseB_4_3 : ∀ v8 < 11, ∀ v9 < 11, caseB 4 3 v8 v9 = true := by decide +kernel
theorem caseB_4_4 : ∀ v8 < 11, ∀ v9 < 11, caseB 4 4 v8 v9 = true := by decide +kernel
theorem caseB_4_5 : ∀ v8 < 11, ∀ v9 < 11, caseB 4 5 v8 v9 = true := by decide +kernel
theorem caseB_4_6 : ∀ v8 < 11, ∀ v9 < 11, caseB 4 6 v8 v9 = true := by decide +kernel
theorem caseB_4_7 : ∀ v8 < 11, ∀ v9 < 11, caseB 4 7 v8 v9 = true := by decide +kernel
theorem caseB_4_8 : ∀ v8 < 11, ∀ v9 < 11, caseB 4 8 v8 v9 = true := by decide +kernel
theorem caseB_4_9 : ∀ v8 < 11, ∀ v9 < 11, caseB 4 9 v8 v9 = true := by decide +kernel
theorem caseB_4_10 : ∀ v8 < 11, ∀ v9 < 11, caseB 4 10 v8 v9 = true := by decide +kernel
theorem caseB_5_0 : ∀ v8 < 11, ∀ v9 < 11, caseB 5 0 v8 v9 = true := by decide +kernel
theorem caseB_5_1 : ∀ v8 < 11, ∀ v9 < 11, caseB 5 1 v8 v9 = true := by decide +kernel
theorem caseB_5_2 : ∀ v8 < 11, ∀ v9 < 11, caseB 5 2 v8 v9 = true := by decide +kernel
theorem caseB_5_3 : ∀ v8 < 11, ∀ v9 < 11, caseB 5 3 v8 v9 = true := by decide +kernel
theorem caseB_5_4 : ∀ v8 < 11, ∀ v9 < 11, caseB 5 4 v8 v9 = true := by decide +kernel
theorem caseB_5_5 : ∀ v8 < 11, ∀ v9 < 11, caseB 5 5 v8 v9 = true := by decide +kernel
theorem caseB_5_6 : ∀ v8 < 11, ∀ v9 < 11, caseB 5 6 v8 v9 = true := by decide +kernel
theorem caseB_5_7 : ∀ v8 < 11, ∀ v9 < 11, caseB 5 7 v8 v9 = true := by decide +kernel
theorem caseB_5_8 : ∀ v8 < 11, ∀ v9 < 11, caseB 5 8 v8 v9 = true := by decide +kernel
theorem caseB_5_9 : ∀ v8 < 11, ∀ v9 < 11, caseB 5 9 v8 v9 = true := by decide +kernel
theorem caseB_5_10 : ∀ v8 < 11, ∀ v9 < 11, caseB 5 10 v8 v9 = true := by decide +kernel
theorem caseB_6_0 : ∀ v8 < 11, ∀ v9 < 11, caseB 6 0 v8 v9 = true := by decide +kernel
theorem caseB_6_1 : ∀ v8 < 11, ∀ v9 < 11, caseB 6 1 v8 v9 = true := by decide +kernel
theorem caseB_6_2 : ∀ v8 < 11, ∀ v9 < 11, caseB 6 2 v8 v9 = true := by decide +kernel
theorem caseB_6_3 : ∀ v8 < 11, ∀ v9 < 11, caseB 6 3 v8 v9 = true := by decide +kernel
theorem caseB_6_4 : ∀ v8 < 11, ∀ v9 < 11, caseB 6 4 v8 v9 = true := by decide +kernel
theorem caseB_6_5 : ∀ v8 < 11, ∀ v9 < 11, caseB 6 5 v8 v9 = true := by decide +kernel
theorem caseB_6_6 : ∀ v8 < 11, ∀ v9 < 11, caseB 6 6 v8 v9 = true := by decide +kernel
theorem caseB_6_7 : ∀ v8 < 11, ∀ v9 < 11, caseB 6 7 v8 v9 = true := by decide +kernel
theorem caseB_6_8 : ∀ v8 < 11, ∀ v9 < 11, caseB 6 8 v8 v9 = true := by decide +kernel
theorem caseB_6_9 : ∀ v8 < 11, ∀ v9 < 11, caseB 6 9 v8 v9 = true := by decide +kernel
theorem caseB_6_10 : ∀ v8 < 11, ∀ v9 < 11, caseB 6 10 v8 v9 = true := by decide +kernel
theorem caseB_7_0 : ∀ v8 < 11, ∀ v9 < 11, caseB 7 0 v8 v9 = true := by decide +kernel
theorem caseB_7_1 : ∀ v8 < 11, ∀ v9 < 11, caseB 7 1 v8 v9 = true := by decide +kernel
theorem caseB_7_2 : ∀ v8 < 11, ∀ v9 < 11, caseB 7 2 v8 v9 = true := by decide +kernel
theorem caseB_7_3 : ∀ v8 < 11, ∀ v9 < 11, caseB 7 3 v8 v9 = true := by decide +kernel
theorem caseB_7_4 : ∀ v8 < 11, ∀ v9 < 11, caseB 7 4 v8 v9 = true := by decide +kernel
theorem caseB_7_5 : ∀ v8 < 11, ∀ v9 < 11, caseB 7 5 v8 v9 = true := by decide +kernel
theorem caseB_7_6 : ∀ v8 < 11, ∀ v9 < 11, caseB 7 6 v8 v9 = true := by decide +kernel
theorem caseB_7_7 : ∀ v8 < 11, ∀ v9 < 11, caseB 7 7 v8 v9 = true := by decide +kernel
theorem caseB_7_8 : ∀ v8 < 11, ∀ v9 < 11, caseB 7 8 v8 v9 = true := by decide +kernel
theorem caseB_7_9 : ∀ v8 < 11, ∀ v9 < 11, caseB 7 9 v8 v9 = true := by decide +kernel
theorem caseB_7_10 : ∀ v8 < 11, ∀ v9 < 11, caseB 7 10 v8 v9 = true := by decide +kernel
theorem caseB_0 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, caseB 0 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [caseB_0_0, caseB_0_1, caseB_0_2, caseB_0_3, caseB_0_4, caseB_0_5, caseB_0_6, caseB_0_7, caseB_0_8, caseB_0_9, caseB_0_10]
theorem caseB_1 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, caseB 1 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [caseB_1_0, caseB_1_1, caseB_1_2, caseB_1_3, caseB_1_4, caseB_1_5, caseB_1_6, caseB_1_7, caseB_1_8, caseB_1_9, caseB_1_10]
theorem caseB_2 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, caseB 2 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [caseB_2_0, caseB_2_1, caseB_2_2, caseB_2_3, caseB_2_4, caseB_2_5, caseB_2_6, caseB_2_7, caseB_2_8, caseB_2_9, caseB_2_10]
theorem caseB_3 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, caseB 3 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [caseB_3_0, caseB_3_1, caseB_3_2, caseB_3_3, caseB_3_4, caseB_3_5, caseB_3_6, caseB_3_7, caseB_3_8, caseB_3_9, caseB_3_10]
theorem caseB_4 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, caseB 4 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [caseB_4_0, caseB_4_1, caseB_4_2, caseB_4_3, caseB_4_4, caseB_4_5, caseB_4_6, caseB_4_7, caseB_4_8, caseB_4_9, caseB_4_10]
theorem caseB_5 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, caseB 5 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [caseB_5_0, caseB_5_1, caseB_5_2, caseB_5_3, caseB_5_4, caseB_5_5, caseB_5_6, caseB_5_7, caseB_5_8, caseB_5_9, caseB_5_10]
theorem caseB_6 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, caseB 6 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [caseB_6_0, caseB_6_1, caseB_6_2, caseB_6_3, caseB_6_4, caseB_6_5, caseB_6_6, caseB_6_7, caseB_6_8, caseB_6_9, caseB_6_10]
theorem caseB_7 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, caseB 7 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [caseB_7_0, caseB_7_1, caseB_7_2, caseB_7_3, caseB_7_4, caseB_7_5, caseB_7_6, caseB_7_7, caseB_7_8, caseB_7_9, caseB_7_10]
theorem caseB_all : ∀ n8 < 8, ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, caseB n8 n10 v8 v9 = true := by
  intro n8 h
  rcases (by omega : n8 = 0 ∨ n8 = 1 ∨ n8 = 2 ∨ n8 = 3 ∨ n8 = 4 ∨ n8 = 5 ∨ n8 = 6 ∨ n8 = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [caseB_0, caseB_1, caseB_2, caseB_3, caseB_4, caseB_5, caseB_6, caseB_7]

/-- **`cellsOf` on the census cases** (composition passed zero-filtered, as in every ledger row). -/
theorem census_cells {n8 n9 n10 v8 v9 v10 : Nat} (h : ValidCase n8 n9 n10 v8 v9 v10) :
    ∃ cells, cellsOf 22 (histDegs n8 n9 n10) (rootOf n8 n10) (compF v8 v9 v10) = .ok cells ∧
      CellsSem n8 n9 n10 v8 v9 v10 cells := by
  have hk := rootOf_mem n8 n10
  have hv := validB_of h
  obtain ⟨h8, h10, hsum, -, hcomp, -, -, -⟩ := h
  have hB := caseB_all n8 h8 n10 h10 v8 (by omega) v9 (by omega)
  have e9 : n9 = 22 - n8 - n10 := by omega
  have e10 : v10 = rootOf n8 n10 - v8 - v9 := by omega
  subst e9 e10
  rw [cellsOf_eq_K]
  unfold caseB at hB
  simp only [hv, if_true] at hB
  split at hB
  · next c hc => exact ⟨c, hc, cellsSem_of_B hB⟩
  · exact absurd hB (by simp)

end SB.Rooted.M4

#print axioms SB.Rooted.M4.cellsOf_eq_K
#print axioms SB.Rooted.M4.caseB_all
#print axioms SB.Rooted.M4.census_cells
