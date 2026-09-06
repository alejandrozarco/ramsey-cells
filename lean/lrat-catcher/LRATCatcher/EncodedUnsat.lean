/-
# The encoder's own output is unsatisfiable

`base_unsat` refutes a string. `encode_eq_base` (O7) identifies that string with
the Lean encoder's output. Composing them moves the refutation off the shipped
file and onto the encoder definition, which is the object `lean-sb`'s soundness
theorems talk about.

Importing this module pulls in all 571 chunk modules — roughly 16 GB of
`.olean` — because `base_unsat` depends on every one of them.
-/
import LRATCatcher.EncoderBridge
import LRATCatcher.Generated.k34k33_n19_unsat.Main

namespace LRATCatcher.Generated.k34k33_n19_unsat

/-- **The encoder's output is unsatisfiable.** No longer a statement about a
shipped file: `LRATCatcher.Encoder.k34k33_n19` is the clause list the Lean
encoder builds from `n = 19`, `K_{3,4}`, `K_{3,3}`. -/
theorem encoded_unsat : (LRATCatcher.Encoder.k34k33_n19).Unsat :=
  encode_eq_base ▸ base_unsat

end LRATCatcher.Generated.k34k33_n19_unsat

#print axioms LRATCatcher.Generated.k34k33_n19_unsat.encoded_unsat
