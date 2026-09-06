import LRATCatcher.ComparatorAxiomsK28K25DOL
open Std.Sat
theorem LRATCatcher.Comparator.K28K25DOL.encoded_unsat : LRATCatcher.Encoder.k28k25_n22_DOL.Unsat :=
  LRATCatcher.cover_unsat LRATCatcher.Comparator.K28K25DOL.leaves_cakelpr LRATCatcher.Comparator.K28K25DOL.cover_cakelpr
#print axioms LRATCatcher.Comparator.K28K25DOL.encoded_unsat
