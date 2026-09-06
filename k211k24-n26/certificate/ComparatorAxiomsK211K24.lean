/- External verdicts for the K2x11,K2x4 n=26 certificate (declared in the Challenge's import closure).
Discharged by cake_lpr on DIMACS printed from the Lean terms (lratcatch-export-encoder k211k24_n26
--prefixes: header + unit lines per leaf, base printed once; base sha256 72b4e9cc... == the closed
formula). Ledger: cert_k211k24/cert_ledger.jsonl. -/
import LRATCatcher.Cover
import LRATCatcher.Encoder
import LRATCatcher.ComparatorCubesK211K24
open Std.Sat
/-- cake_lpr: every leaf `cube ++ Encoder.k211k24_n26` is unsatisfiable (10,017 files). -/
axiom LRATCatcher.Comparator.K211K24.leaves_cakelpr :
    ∀ c ∈ LRATCatcher.Comparator.K211K24.cubes,
      (LRATCatcher.Cube.leafCNF c LRATCatcher.Encoder.k211k24_n26).Unsat
/-- cake_lpr: the negated cubes are jointly unsatisfiable (the leaves cover every assignment). -/
axiom LRATCatcher.Comparator.K211K24.cover_cakelpr :
    (LRATCatcher.negCubesCNF LRATCatcher.Comparator.K211K24.cubes).Unsat
