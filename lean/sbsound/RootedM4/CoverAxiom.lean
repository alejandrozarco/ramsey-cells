/-
# M4: the cake_lpr verdicts on the 53 H-cover CNFs (the axiom only)

Moved here from `RootedM4/Census.lean` on 2026-10-07 (M5) so that a Comparator challenge can declare the
permitted axiom by importing the certificate data and the cover CNF definition only, without the M4
proofs. Same name, same statement.

`famCNF fc` (`RootedM4/CoverBase.lean`) is the Lean port of `cnfgen.build_full`; each of the 53 files was
printed from this term by `ramsey/runs/k28_rooted/m4_canon/PrintCover.lean`, is body-identical to the M0
file, and was verified by cake_lpr with the M0 trimmed LRAT proof (`m4_canon/cakelpr_cover.jsonl`).
-/
import RootedM4.CoverData.All
import Sbsound.BipBridge

namespace SB.Rooted.M4.CoverData
open SB.Rooted.M4.Cover

/-- **cake_lpr verdicts on the 53 H-cover CNFs** (M0 certificates, printed from `famCNF`). -/
axiom cover_cakelpr : ∀ fc ∈ allCerts, (SB.BipBridge.toCNFV (famCNF fc).1).Unsat

end SB.Rooted.M4.CoverData
