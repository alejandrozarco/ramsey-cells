/-
# The external verdicts, stated where the Challenge can see them

Comparator exports permitted axioms from the CHALLENGE environment, so the assumptions a
certificate rests on must be declared in the trusted file's import closure — the reader of
the challenge sees exactly what was assumed. Both are discharged outside Lean by cake_lpr,
the CakeML-verified LRAT checker, on DIMACS files printed from the Lean terms below by
`lratcatch-export-encoder` (printer: `Std.Sat.CNF.dimacs`). Verdict ledger with per-file
sha256: `runs/k34k33_cakelpr_encoder_ledger.jsonl`.
-/
import LRATCatcher.Cover
import LRATCatcher.Encoder
import LRATCatcher.ComparatorCubes
open Std.Sat

/-- cake_lpr: every leaf `cube ++ Encoder.k34k33_n19` is unsatisfiable (571 files). -/
axiom LRATCatcher.Comparator.leaves_cakelpr :
    ∀ c ∈ LRATCatcher.Comparator.cubes,
      (LRATCatcher.Cube.leafCNF c LRATCatcher.Encoder.k34k33_n19).Unsat

/-- cake_lpr: the negated cubes are jointly unsatisfiable, i.e. the 571 cubes cover every
assignment (`negcubes.cnf`). -/
axiom LRATCatcher.Comparator.cover_cakelpr :
    (LRATCatcher.negCubesCNF LRATCatcher.Comparator.cubes).Unsat
