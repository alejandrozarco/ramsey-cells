import LRATCatcher.ComparatorAxiomsK35K25
open Std.Sat
theorem LRATCatcher.Comparator.K35K25.encoded_unsat : LRATCatcher.Encoder.k35k25_n22.Unsat :=
  LRATCatcher.cover_unsat LRATCatcher.Comparator.K35K25.leaves_cakelpr LRATCatcher.Comparator.K35K25.cover_cakelpr
#print axioms LRATCatcher.Comparator.K35K25.encoded_unsat
