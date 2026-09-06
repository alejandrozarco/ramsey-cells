/- Mixed cover: leaves refuted under a weaker formula `base` or under the stronger `base ++ extra`,
cover over the union; conclusion: `base ++ extra` is unsatisfiable. (Any model of the stronger formula
models the weaker one, lies in some cube, and that cube's leaf is refuted under a formula it satisfies.)
Instantiated for the K2x8,K2x5 hybrid tree: base = the DO formula, extra = the conditional-lex block. -/
import LRATCatcher.Cover
import LRATCatcher.Encoder
open Std.Sat
namespace LRATCatcher

theorem Encoder.toCNF_append (a b : List (List Int)) :
    Encoder.toCNF (a ++ b) = Encoder.toCNF a ++ Encoder.toCNF b := by
  show Encoder.toCNF (a ++ b) = CNF.append _ _
  unfold Encoder.toCNF CNF.append
  simp only [List.map_append]
  first
    | rfl
    | simp
    | (congr 1; exact List.append_toArray _ _)

/-- The DOL formula is the DO formula followed by the conditional-lex block (definitional). -/
theorem Encoder.k28k25_dol_eq :
    Encoder.k28k25_n22_DOL =
      Encoder.k28k25_n22_DO ++ Encoder.toCNF (Encoder.dolParts 22 2 8 2 5).2 := by
  unfold Encoder.k28k25_n22_DOL Encoder.k28k25_n22_DO Encoder.encodeBipDOL Encoder.encodeBipDO
  exact Encoder.toCNF_append _ _

theorem cover_unsat_mixed {base extra : CNF Nat} {c1 c2 : List Cube}
    (h1 : ∀ c ∈ c1, (Cube.leafCNF c base).Unsat)
    (h2 : ∀ c ∈ c2, (Cube.leafCNF c (base ++ extra)).Unsat)
    (hcover : (negCubesCNF (c1 ++ c2)).Unsat) :
    (base ++ extra).Unsat := by
  intro a
  obtain ⟨c, hc, hsat⟩ := cover_complete hcover a
  rcases List.mem_append.mp hc with hc1 | hc2
  · have hl := h1 c hc1 a
    simp [Cube.leafCNF, Cube.eval_toCNF, hsat] at hl
    simp [hl]
  · have hl := h2 c hc2 a
    simpa [Cube.leafCNF, Cube.eval_toCNF, hsat] using hl

end LRATCatcher

#print axioms LRATCatcher.cover_unsat_mixed
#print axioms LRATCatcher.Encoder.k28k25_dol_eq
