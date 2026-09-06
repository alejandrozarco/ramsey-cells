/- External verdicts for the K3x5,K2x4 n=19 certificate, declared where the Challenge sees them.
Discharged by cake_lpr on DIMACS printed from the Lean terms by lratcatch-export-encoder;
ledger runs/k35k24_cakelpr_encoder_ledger.jsonl. -/
import LRATCatcher.Cover
import LRATCatcher.Encoder
import LRATCatcher.ComparatorCubesK35K24
open Std.Sat
/-- cake_lpr: every leaf `cube ++ Encoder.k35k24_n19` is unsatisfiable (773 files). -/
axiom LRATCatcher.Comparator.K35K24.leaves_cakelpr :
    ∀ c ∈ LRATCatcher.Comparator.K35K24.cubes,
      (LRATCatcher.Cube.leafCNF c LRATCatcher.Encoder.k35k24_n19).Unsat
/-- cake_lpr: the negated cubes are jointly unsatisfiable (the 773 leaves cover every assignment). -/
axiom LRATCatcher.Comparator.K35K24.cover_cakelpr :
    (LRATCatcher.negCubesCNF LRATCatcher.Comparator.K35K24.cubes).Unsat
