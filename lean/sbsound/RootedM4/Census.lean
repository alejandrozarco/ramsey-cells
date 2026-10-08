/-
# M4, part 6: the coverage step from the M0 certificates, and what M5 still has to supply

* `cover_cakelpr` (AXIOM, the only one M4 adds; declared in `RootedM4/CoverAxiom.lean`): each of the 53 M0 cover CNFs, printed from the Lean
  term `famCNF fc` (`fc ∈ allCerts`) by `ramsey/runs/k28_rooted/m4_canon/PrintCover.lean`, is
  unsatisfiable. Discharged outside Lean by cake_lpr (the CakeML-verified LRAT checker) with the M0
  trimmed LRAT proofs; the printed files are body-identical to the M0 files
  (`m4_canon/cover_print_compare.jsonl`, `m4_canon/cakelpr_cover.jsonl`).
* `certOf_spec`: every census case has a certificate in `allCerts` with its own `(k, v8, v9, v10)`
  (kernel evaluation over all index tuples).
* `censusCover_of_cubes`: `CensusCover C` for any list of cubes `C` that contains, for every census
  case and every listed word of its family, a cube of that case with `H = wordEdges k w` and
  `shortfall = false`. That correspondence is a finite check on the ledgers and is left to M5.
* `no_good_K22_of_cubes`: no good colouring of `K_22`, from that correspondence and the per-cube
  refutations (the hypothesis of `no_good_K22_of`, which `no_canon_of_unsat` /
  `no_canon_of_children_unsat` give from the cube verdicts).
-/
import RootedM4.CoverChecks.All
import RootedM4.CoverAxiom
import RootedM4.Main

set_option linter.unusedVariables false

namespace SB.Rooted.M4.CoverData
open SB SB.Rooted SB.Rooted.M4 SB.Rooted.M4.Cover SB.BipBridge LRATCatcher.Rooted

-- `cover_cakelpr` is declared in `RootedM4/CoverAxiom.lean` (moved there for M5, same statement).

/-- The certificate lookup is right for one index tuple (vacuous off the census cases). -/
def certCheckB (n8 n10 v8 v9 : ℕ) : Bool :=
  let n9 := 22 - n8 - n10
  let k := rootOf n8 n10
  let v10 := k - v8 - v9
  !validB n8 n9 n10 v8 v9 v10 ||
    (decide (famKeys.idxOf (k, v8, v9, v10) < allCerts.length) &&
      ((certOf k v8 v9 v10).k == k) && ((certOf k v8 v9 v10).v8 == v8) &&
      ((certOf k v8 v9 v10).v9 == v9) && ((certOf k v8 v9 v10).v10 == v10))

theorem certCheck_all : ∀ n8 < 8, ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, certCheckB n8 n10 v8 v9 = true := by
  decide +kernel

theorem certOf_spec {n8 n9 n10 v8 v9 v10 : ℕ} (h : ValidCase n8 n9 n10 v8 v9 v10) :
    certOf (rootOf n8 n10) v8 v9 v10 ∈ allCerts ∧
      (certOf (rootOf n8 n10) v8 v9 v10).k = rootOf n8 n10 ∧
      (certOf (rootOf n8 n10) v8 v9 v10).v8 = v8 ∧ (certOf (rootOf n8 n10) v8 v9 v10).v9 = v9 ∧
      (certOf (rootOf n8 n10) v8 v9 v10).v10 = v10 := by
  have hk := rootOf_mem n8 n10
  have hv := validB_of h
  obtain ⟨h8, h10, hsum, -, hcomp, -, -, -⟩ := h
  have hB := certCheck_all n8 h8 n10 h10 v8 (by omega) v9 (by omega)
  have e9 : n9 = 22 - n8 - n10 := by omega
  have e10 : v10 = rootOf n8 n10 - v8 - v9 := by omega
  subst e9 e10
  unfold certCheckB at hB
  simp only [hv, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hB
  obtain ⟨⟨⟨⟨hidx, h1⟩, h2⟩, h3⟩, h4⟩ := hB
  refine ⟨?_, h1, h2, h3, h4⟩
  unfold certOf
  rw [List.getD_eq_getElem _ _ hidx]
  exact List.getElem_mem hidx

/-- **`CensusCover` from the M0 certificates**, given the listed-word ↔ cube correspondence. -/
theorem censusCover_of_cubes (C : List Cube)
    (hcubes : ∀ n8 n9 n10 v8 v9 v10, ValidCase n8 n9 n10 v8 v9 v10 →
      ∀ wb ∈ listedWords (certOf (rootOf n8 n10) v8 v9 v10), ∃ c ∈ C,
        c.degs = histDegs n8 n9 n10 ∧ c.k = rootOf n8 n10 ∧ c.comp = compF v8 v9 v10 ∧
        c.H = wordEdges (rootOf n8 n10) wb ∧ c.o.shortfall = false) :
    CensusCover C := by
  apply censusCover_of_certs C certOf
  intro n8 n9 n10 v8 v9 v10 hv
  obtain ⟨hmem, h1, h2, h3, h4⟩ := certOf_spec hv
  exact ⟨h1, h2, h3, h4, allCerts_ok _ hmem, cover_cakelpr _ hmem, hcubes n8 n9 n10 v8 v9 v10 hv⟩

/-- **No good 2-colouring of `K_22`**, from the listed-word ↔ cube correspondence and the per-cube
refutations (M5's obligations). -/
theorem no_good_K22_of_cubes (C : List Cube)
    (hcubes : ∀ n8 n9 n10 v8 v9 v10, ValidCase n8 n9 n10 v8 v9 v10 →
      ∀ wb ∈ listedWords (certOf (rootOf n8 n10) v8 v9 v10), ∃ c ∈ C,
        c.degs = histDegs n8 n9 n10 ∧ c.k = rootOf n8 n10 ∧ c.comp = compF v8 v9 v10 ∧
        c.H = wordEdges (rootOf n8 n10) wb ∧ c.o.shortfall = false)
    (hU : ∀ c ∈ C, ∀ cells : Cells, cellsOf 22 c.degs c.k c.comp = .ok cells → CubeWF cells →
      c.o.shortfall = false →
      ¬ ∃ a : EColouring 22 2, NoKst a 0 2 8 ∧ NoKst a 1 2 5 ∧ RootedCanon a c.k cells (normH c.H) c.o) :
    ¬ ∃ b : EColouring 22 2, NoKst b 0 2 8 ∧ NoKst b 1 2 5 :=
  no_good_K22_of C (censusCover_of_cubes C hcubes) hU

end SB.Rooted.M4.CoverData

#print axioms SB.Rooted.M4.CoverData.certOf_spec
#print axioms SB.Rooted.M4.CoverData.censusCover_of_cubes
#print axioms SB.Rooted.M4.CoverData.no_good_K22_of_cubes
