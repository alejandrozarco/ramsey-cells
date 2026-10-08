/-
# M5: the cake_lpr verdicts on the census cubes (named axioms)

Two axioms, both about DIMACS files printed from Lean terms of the table `SB.Rooted.M5.rows`
(`RootedM5/Table.lean`, data generated from the census ledgers by
`ramsey/runs/k28_rooted/m5_final/m5_gen_lean.py`):

* `direct_cakelpr`: for every row with verdict `direct`, the CNF `toCNFV (Row.clauses r)` is
  unsatisfiable. `Row.clauses r` is the clause list of `rootedFormula 22 ["K2x8","K2x5"] …` for the
  row's case, `H` and option set (`[]` if the encoder fails).
* `leaves_cakelpr`: for every row with verdict `split childOf fuel us` and every `u ∈ us`, the CNF
  `toCNFV (Row.leafClauses r childOf u)` (the parent's clauses followed by the unit clauses `u`) is
  unsatisfiable.

Discharged outside Lean: the compiled printer `m5-print` (`RootedM5Print.lean`) parses the rows that
`ramsey/runs/k28_rooted/m5_final/SerRows.lean` serialises from the Lean constant (`Row.ser`, echoed and
compared), prints each file with `LRATCatcher.Rooted.writeDimacs`, and the sha256 of every printed file
equals the `cnf_sha256` of a ledger row (direct) or leaf node (split) that records a cake_lpr
`s VERIFIED UNSAT` for that file (`m5_final/verify_*.jsonl`). The clause body of the printed file is
`Row.clauses r` (resp. `Row.leafClauses r childOf u`) one clause per line; the comment lines and the
`p cnf` header are not part of the CNF.

If the encoder returned an error for a row, its clause list would be `[]`, the empty CNF, which is
satisfiable; the axiom would then be refutable, so the axioms carry no hidden assumption that the
encoder succeeds (and the printer prints nothing for such a row, so no hash could match).
-/
import RootedM5.Table
import Sbsound.BipBridge

namespace SB.Rooted.M5
open SB.BipBridge

/-- **cake_lpr verdicts, direct cubes.** -/
axiom direct_cakelpr : ∀ r ∈ rows, r.e.v = .direct → (toCNFV r.clauses).Unsat

/-- **cake_lpr verdicts, the leaves of split cubes.** -/
axiom leaves_cakelpr : ∀ r ∈ rows, ∀ (t : String) (n : Nat) (us : List (List Int)),
  r.e.v = .split t n us → ∀ u ∈ us, (toCNFV (r.leafClauses t u)).Unsat

end SB.Rooted.M5
