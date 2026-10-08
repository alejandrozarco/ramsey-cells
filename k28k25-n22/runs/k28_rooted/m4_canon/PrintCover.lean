/- M4: print the 53 cover CNFs from the Lean terms `famCNF fc` (`fc ∈ allCerts`) as DIMACS.
   Run from lean-sb:  lake env lean --run ../ramsey/runs/k28_rooted/m4_canon/PrintCover.lean OUTDIR
   One file OUTDIR/<k>_<v8><v9><v10>.cnf per family: the `p cnf` line and the clauses, no comments. -/
import RootedM4.CoverData.All
open SB.Rooted.M4.Cover SB.Rooted.M4.CoverData

def main (args : List String) : IO Unit := do
  let out := args.headD "."
  for fc in allCerts do
    let name := s!"{out}/k{fc.k}_c{fc.v8}{fc.v9}{fc.v10}.cnf"
    IO.FS.writeFile name (dimacsBody (famCNF fc))
    IO.println s!"{name} written"
