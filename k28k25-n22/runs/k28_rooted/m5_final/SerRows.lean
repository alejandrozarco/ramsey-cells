/- M5: write `i<TAB>Row.ser r` for every row `r` (index `i`) of the Lean constant `SB.Rooted.M5.rows`.
   Run from lean-sb:  lake env lean --run ../ramsey/runs/k28_rooted/m5_final/SerRows.lean OUTFILE
   The printer `m5-print` takes these lines as its jobs and echoes `Row.ser` of the row it parsed. -/
import RootedM5.Table
open SB.Rooted.M5

def main (args : List String) : IO Unit := do
  let out := args.headD "rows_ser.txt"
  IO.FS.withFile out .write fun h => do
    let mut i := 0
    for r in rows do
      h.putStrLn s!"{i}\t{r.ser}"
      i := i + 1
  IO.println s!"{out} written"
