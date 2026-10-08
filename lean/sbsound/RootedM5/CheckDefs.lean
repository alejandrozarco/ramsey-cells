/-
# M5: the Boolean check of one case of the cube table

`caseOKB c` says:
* `(n8, …, v10)` is a census case (`validB`);
* the family `(k, v8, v9, v10)` is one of the 53 keys of `famKeys`, and the entries' `H` lists are exactly
  `famH k v8 v9 v10`, which `famH_spec` (`RootedM5/FamAll.lean`) identifies with
  `(listedWords (certOf k v8 v9 v10)).map (wordEdges k)` (the listed words in certificate order);
* every split verdict is a complete case split (`coversB`, M3).

The data chunks are checked by `decide +kernel` (`RootedM5/Checks/K*.lean`).
-/
import RootedM5.Basic
import RootedM5.FamAll

namespace SB.Rooted.M5
open SB.Rooted SB.Rooted.M4 SB.Rooted.M4.Cover SB.Rooted.M4.CoverData

def verdictOKB : Verdict → Bool
  | .split _ n us => coversB n us
  | _ => true

def caseOKB (c : CaseRows) : Bool :=
  validB c.n8 c.n9 c.n10 c.v8 c.v9 c.v10 &&
  famKeys.contains (rootOf c.n8 c.n10, c.v8, c.v9, c.v10) &&
  decide (c.entries.map Entry.H = famH (rootOf c.n8 c.n10) c.v8 c.v9 c.v10) &&
  c.entries.all (fun e => verdictOKB e.v)

end SB.Rooted.M5
