import LRATCatcher.ComparatorAxiomsK211K23
open Std.Sat
theorem LRATCatcher.Comparator.K211K23.encoded_unsat : LRATCatcher.Encoder.k211k23_n22.Unsat :=
  LRATCatcher.cover_unsat LRATCatcher.Comparator.K211K23.leaves_cakelpr LRATCatcher.Comparator.K211K23.cover_cakelpr
#print axioms LRATCatcher.Comparator.K211K23.encoded_unsat
