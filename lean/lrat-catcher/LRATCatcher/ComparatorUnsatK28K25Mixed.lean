import LRATCatcher.ComparatorAxiomsK28K25Mixed
open Std.Sat
theorem LRATCatcher.Comparator.K28K25Mixed.encoded_unsat : LRATCatcher.Encoder.k28k25_n22_DOL.Unsat := by
  have h2 := LRATCatcher.Comparator.K28K25Mixed.leavesDOL_cakelpr
  rw [LRATCatcher.Encoder.k28k25_dol_eq] at h2 ⊢
  exact LRATCatcher.cover_unsat_mixed LRATCatcher.Comparator.K28K25Mixed.leavesDO_cakelpr h2
    LRATCatcher.Comparator.K28K25Mixed.cover_cakelpr
#print axioms LRATCatcher.Comparator.K28K25Mixed.encoded_unsat
