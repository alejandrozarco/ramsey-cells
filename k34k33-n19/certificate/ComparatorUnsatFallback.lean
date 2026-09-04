/- Comparator SOLUTION: composition of the two external verdicts through the
cube-and-conquer theorem `LRATCatcher.cover_unsat`. Trust base = propext / Quot.sound /
Classical.choice + the two named cake_lpr verdicts declared in ComparatorAxioms. -/
import LRATCatcher.ComparatorAxioms
open Std.Sat
theorem LRATCatcher.Comparator.encoded_unsat : LRATCatcher.Encoder.k34k33_n19.Unsat :=
  LRATCatcher.cover_unsat LRATCatcher.Comparator.leaves_cakelpr LRATCatcher.Comparator.cover_cakelpr
#print axioms LRATCatcher.Comparator.encoded_unsat
