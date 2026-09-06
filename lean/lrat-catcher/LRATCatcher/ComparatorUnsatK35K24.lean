import LRATCatcher.ComparatorAxiomsK35K24
open Std.Sat
theorem LRATCatcher.Comparator.K35K24.encoded_unsat : LRATCatcher.Encoder.k35k24_n19.Unsat :=
  LRATCatcher.cover_unsat LRATCatcher.Comparator.K35K24.leaves_cakelpr LRATCatcher.Comparator.K35K24.cover_cakelpr
#print axioms LRATCatcher.Comparator.K35K24.encoded_unsat
