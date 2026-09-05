/- External verdicts for the K3x5,K2x5 n=22 certificate (declared in the Challenge's import
closure). Discharged by cake_lpr on DIMACS printed from the Lean terms (lratcatch-export-encoder
k35k25_n22 --prefixes: header + unit lines per leaf, base printed once; rule validated against
full Lean-printed leaves). Ledger: cert/k35k25_n22/cert_ledger.jsonl. -/
import LRATCatcher.Cover
import LRATCatcher.Encoder
import LRATCatcher.ComparatorCubesK35K25
open Std.Sat
/-- cake_lpr: every leaf `cube ++ Encoder.k35k25_n22` is unsatisfiable (137,350 files). -/
axiom LRATCatcher.Comparator.K35K25.leaves_cakelpr :
    ∀ c ∈ LRATCatcher.Comparator.K35K25.cubes,
      (LRATCatcher.Cube.leafCNF c LRATCatcher.Encoder.k35k25_n22).Unsat
/-- cake_lpr: the negated cubes are jointly unsatisfiable (the leaves cover every assignment). -/
axiom LRATCatcher.Comparator.K35K25.cover_cakelpr :
    (LRATCatcher.negCubesCNF LRATCatcher.Comparator.K35K25.cubes).Unsat
