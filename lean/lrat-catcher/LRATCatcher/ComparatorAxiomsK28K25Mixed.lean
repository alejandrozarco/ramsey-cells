/- External verdicts for the K2x8,K2x5 n=22 HYBRID certificate: the 534 verified leaves of the
degree-ordered (DO) tree, refuted under `Encoder.k28k25_n22_DO`, plus the leaves of the DOL completion
of that tree's unsolved cubes, refuted under `Encoder.k28k25_n22_DOL`; the union of cubes covers every
assignment. Discharged by cake_lpr on DIMACS printed from the Lean terms (lratcatch-export-encoder
k28k25_n22_DO / k28k25_n22_DOL --prefixes). Assembly: `LRATCatcher.cover_unsat_mixed` with
`Encoder.k28k25_dol_eq` (DOL = DO ++ conditional-lex block). Soundness of the DOL symmetry breaking:
`SB.Portfolio.dol_sound_K2x8_K2x5` (sbsound). -/
import LRATCatcher.MixedCover
import LRATCatcher.ComparatorCubesK28K25DO
import LRATCatcher.ComparatorCubesK28K25DOL
open Std.Sat
/-- cake_lpr: every DO-tree leaf `cube ++ Encoder.k28k25_n22_DO` is unsatisfiable. -/
axiom LRATCatcher.Comparator.K28K25Mixed.leavesDO_cakelpr :
    ∀ c ∈ LRATCatcher.Comparator.K28K25DO.cubes,
      (LRATCatcher.Cube.leafCNF c LRATCatcher.Encoder.k28k25_n22_DO).Unsat
/-- cake_lpr: every completion leaf `cube ++ Encoder.k28k25_n22_DOL` is unsatisfiable. -/
axiom LRATCatcher.Comparator.K28K25Mixed.leavesDOL_cakelpr :
    ∀ c ∈ LRATCatcher.Comparator.K28K25DOL.cubes,
      (LRATCatcher.Cube.leafCNF c LRATCatcher.Encoder.k28k25_n22_DOL).Unsat
/-- cake_lpr: the negated cubes of the union are jointly unsatisfiable (unconditional cover). -/
axiom LRATCatcher.Comparator.K28K25Mixed.cover_cakelpr :
    (LRATCatcher.negCubesCNF
      (LRATCatcher.Comparator.K28K25DO.cubes ++ LRATCatcher.Comparator.K28K25DOL.cubes)).Unsat
