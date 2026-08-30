/-
# O7 — the encoder bridge

`base` is the CNF the 571 cubes actually refuted: the DIMACS text of
`runs/k34k33_n19.cnf`, embedded verbatim in `Base.lean` and parsed inside the
statement of `base_unsat`. That made `base_unsat` a theorem about *a specific
string*, and left one link resting on human care: that the string is the
encoding of the Ramsey question it is described as being.

`LRATCatcher.Encoder.encodeBip` is a Lean transcription of `gen_ramsey.py`,
written against the same conventions and emitting clauses in the same order.
The theorem below checks the transcription against the file — 202,770 clauses,
105,213 variables — so the description is no longer a claim but a verified
identity.

What this does and does not settle. It settles that the file solved is the file
the encoder produces. It does not, by itself, say the encoder is the right
encoding of the Ramsey property: that is the semantic half, proved separately in
`lean-sb` (`SB.encode_sound_k34k33`, and `SB.Portfolio` for the other twelve
cells). The two halves meet at this definition.
-/
import LRATCatcher.Encoder
import LRATCatcher.Generated.k34k33_n19_unsat.Base

open Std.Sat

namespace LRATCatcher.Generated.k34k33_n19_unsat

/-- **O7.** The Lean encoder reproduces, clause for clause and literal for
literal, the DIMACS file that the cube-and-conquer search refuted.

Checked by evaluation: both sides are closed terms, one a transcription of the
Python encoder and the other the parse of the shipped file. -/
theorem encode_eq_clauses :
    (LRATCatcher.Encoder.k34k33_n19).clauses = base.clauses := by
  native_decide

/-- The same identity at the level of the CNF itself. `CNF` is a one-field
structure, so this is the field equality under structure eta. -/
theorem encode_eq_base :
    LRATCatcher.Encoder.k34k33_n19 = base :=
  congrArg CNF.mk encode_eq_clauses

end LRATCatcher.Generated.k34k33_n19_unsat

#print axioms LRATCatcher.Generated.k34k33_n19_unsat.encode_eq_clauses
#print axioms LRATCatcher.Generated.k34k33_n19_unsat.encode_eq_base
