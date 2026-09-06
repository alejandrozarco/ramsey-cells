/- External verdicts for the K2x11,K2x3 n=22 certificate (declared in the Challenge's import closure).
Discharged by cake_lpr on DIMACS printed from the Lean terms (lratcatch-export-encoder k211k23_n22
--prefixes: header + unit lines per leaf, base printed once; base sha256 57518b8c... == the closed
formula). Ledger: cert_k211k23/cert_ledger.jsonl. -/
import LRATCatcher.Cover
import LRATCatcher.Encoder
import LRATCatcher.ComparatorCubesK211K23
open Std.Sat
/-- cake_lpr: every leaf `cube ++ Encoder.k211k23_n22` is unsatisfiable (1,313 files). -/
axiom LRATCatcher.Comparator.K211K23.leaves_cakelpr :
    ∀ c ∈ LRATCatcher.Comparator.K211K23.cubes,
      (LRATCatcher.Cube.leafCNF c LRATCatcher.Encoder.k211k23_n22).Unsat
/-- cake_lpr: the negated cubes are jointly unsatisfiable (the leaves cover every assignment). -/
axiom LRATCatcher.Comparator.K211K23.cover_cakelpr :
    (LRATCatcher.negCubesCNF LRATCatcher.Comparator.K211K23.cubes).Unsat
