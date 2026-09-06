/- External verdicts for the K2x8,K2x5 n=22 DOL certificate (declared in the Challenge's import
closure). Discharged by cake_lpr on DIMACS printed from the Lean terms (lratcatch-export-encoder
k28k25_n22_DOL --prefixes: header + unit lines per leaf, base printed once). The base is
`Encoder.k28k25_n22_DOL` = gen_variant.py --variant DOL (byte-identical, sha256 3515d202...); the
soundness of its symmetry breaking is `SB.Portfolio.dol_sound_K2x8_K2x5` in sbsound. -/
import LRATCatcher.Cover
import LRATCatcher.Encoder
import LRATCatcher.ComparatorCubesK28K25DOL
open Std.Sat
/-- cake_lpr: every leaf `cube ++ Encoder.k28k25_n22_DOL` is unsatisfiable. -/
axiom LRATCatcher.Comparator.K28K25DOL.leaves_cakelpr :
    ∀ c ∈ LRATCatcher.Comparator.K28K25DOL.cubes,
      (LRATCatcher.Cube.leafCNF c LRATCatcher.Encoder.k28k25_n22_DOL).Unsat
/-- cake_lpr: the negated cubes are jointly unsatisfiable (the leaves cover every assignment). -/
axiom LRATCatcher.Comparator.K28K25DOL.cover_cakelpr :
    (LRATCatcher.negCubesCNF LRATCatcher.Comparator.K28K25DOL.cubes).Unsat
