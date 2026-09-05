import LRATCatcher.Cover
import LRATCatcher.Encoder
/-!  `lratcatch-export-encoder <cell> cubes.icnf outDir [--prefixes | --sample N]`
  Base CNF = the LEAN ENCODER'S OUTPUT for the cell (never a parsed file); printer `Std.Sat.CNF.dimacs`.
  default    : one full leaf file per cube (`leafCNF c base`), plus negcubes.cnf and base_encoder.cnf
  --prefixes : base_encoder.cnf, negcubes.cnf and prefixes.tsv — per cube the leaf's header line and
               unit-clause lines exactly as the full printer emits them; leaf = prefix ++ base body
  --sample N : N full leaf files at evenly spaced cube indices, to validate the prefix rule by sha256 -/
open Std.Sat
def baseOf : String → Option (CNF Nat)
  | "k34k33_n19" => some LRATCatcher.Encoder.k34k33_n19
  | "k35k24_n19" => some LRATCatcher.Encoder.k35k24_n19
  | "k35k25_n22" => some LRATCatcher.Encoder.k35k25_n22
  | _ => none
def main (args : List String) : IO UInt32 := do
  match args with
  | cell :: icnfFile :: outDir :: rest =>
    let some base := baseOf cell | do IO.eprintln s!"unknown cell {cell}"; return 1
    let cubes := LRATCatcher.parseICnf (← IO.FS.readFile icnfFile)
    IO.FS.createDirAll outDir
    let baseText := base.dimacs
    IO.FS.writeFile s!"{outDir}/base_encoder.cnf" baseText
    IO.FS.writeFile s!"{outDir}/negcubes.cnf" (LRATCatcher.negCubesCNF cubes).dimacs
    -- header of the base: "p cnf NV NC"; a leaf's header is "p cnf NV (NC + |cube|)"
    let hdr := (baseText.splitOn "\n").head!
    let ws := hdr.splitOn " "
    let nv := ws[2]!; let nc := (ws[3]!).toNat!
    match rest with
    | ["--prefixes"] =>
      let h ← IO.FS.Handle.mk s!"{outDir}/prefixes.tsv" .write
      let mut i := 0
      for c in cubes do
        let units := c.map fun (v, b) => s!"{if b then "" else "-"}{v+1} 0"
        h.putStrLn s!"{i}\tp cnf {nv} {nc + c.length}|{"|".intercalate units}|"
        i := i + 1
      IO.println s!"prefixes for {i} leaves + base_encoder.cnf + negcubes.cnf -> {outDir}"
    | ["--sample", n] =>
      let n := n.toNat!; let step := max 1 (cubes.length / n)
      let mut i := 0; let mut k := 0
      for c in cubes do
        if i % step == 0 && k < n then
          IO.FS.writeFile s!"{outDir}/leaf{i}.cnf" (LRATCatcher.Cube.leafCNF c base).dimacs; k := k + 1
        i := i + 1
      IO.println s!"{k} sample leaves -> {outDir}"
    | _ =>
      let mut i := 0
      for c in cubes do
        IO.FS.writeFile s!"{outDir}/leaf{i}.cnf" (LRATCatcher.Cube.leafCNF c base).dimacs; i := i + 1
      IO.println s!"wrote {i} leaves + negcubes.cnf + base_encoder.cnf to {outDir}"
    return 0
  | _ => IO.eprintln "usage: lratcatch-export-encoder <cell> cubes.icnf outDir [--prefixes | --sample N]"; return 1
