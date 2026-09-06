import LRATCatcher.ComparatorAxiomsK211K24
open Std.Sat
theorem LRATCatcher.Comparator.K211K24.encoded_unsat : LRATCatcher.Encoder.k211k24_n26.Unsat :=
  LRATCatcher.cover_unsat LRATCatcher.Comparator.K211K24.leaves_cakelpr LRATCatcher.Comparator.K211K24.cover_cakelpr
#print axioms LRATCatcher.Comparator.K211K24.encoded_unsat
