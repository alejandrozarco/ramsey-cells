/-
# Comparator-grade refutation of R(K_{3,4},K_{3,3}) at n = 19 — SOLUTION module

Trust base, stated in the open (the PrimeGaps186 shape):
  * Lean kernel + nanoda replay under propext / Quot.sound / Classical.choice, and
  * ONE named external verdict, `leaves_cakelpr`, discharged outside Lean by cake_lpr — the
    CakeML-verified LRAT checker — on the 571 leaf DIMACS files that `lratcatch-export-encoder`
    prints FROM THE LEAN ENCODER TERM `LRATCatcher.Encoder.k34k33_n19` via `Std.Sat.CNF.dimacs`.
    The verdict ledger (per-leaf sha256, proof bytes, `s VERIFIED UNSAT`) is
    `runs/k34k33_cakelpr_encoder_ledger.jsonl`.
No file is parsed anywhere in this chain; no `native_decide` is used. The cover certificate
(79 KB) is checked inside the Lean kernel on a cube-list literal.
-/
import LRATCatcher.Reflect
import LRATCatcher.Encoder
import LRATCatcher.ComparatorCubes

open Std.Sat

/-- **External verdict (whitelisted axiom).** Every leaf `cube ++ encoder output` is
unsatisfiable: verified by cake_lpr on the encoder-printed DIMACS of exactly these terms. -/
axiom LRATCatcher.Comparator.leaves_cakelpr :
    ∀ c ∈ LRATCatcher.Comparator.cubes,
      (LRATCatcher.Cube.leafCNF c LRATCatcher.Encoder.k34k33_n19).Unsat

-- Cover completeness, checked in the kernel: the negated cubes are jointly UNSAT.
-- (A doc comment is not accepted in front of this elaborator command.)
lrat_reflect_cnf +kernel LRATCatcher.Comparator.cover_ok
  (LRATCatcher.negCubesCNF LRATCatcher.Comparator.cubes) "../runs/k34k33_export/cover.lrat"

/-- **The encoder's output is unsatisfiable**, hence no lex-leader 2-colouring of K_19 avoids
K_{3,4} in colour 0 and K_{3,3} in colour 1 (with `SB.Portfolio.no_colouring_of_no_leader`
and `sound_K3x4_K3x3`: no colouring at all). -/
theorem LRATCatcher.Comparator.encoded_unsat : LRATCatcher.Encoder.k34k33_n19.Unsat :=
  LRATCatcher.cover_unsat LRATCatcher.Comparator.leaves_cakelpr LRATCatcher.Comparator.cover_ok

#print axioms LRATCatcher.Comparator.encoded_unsat
