import RootedM5.Basic
/-!  `m5-print OUTDIR JOBS`  (JOBS = a file, or `-` for stdin)

Prints the DIMACS files of cubes of the M5 cube table with the encoder's own printer
(`LRATCatcher.Rooted.writeDimacs`):
* a `direct` row: the file of `Row.formula r` (whose clause list is `Row.clauses r`);
* a `split childOf fuel leaves` row: for every leaf `u` (index `j`), the file of
  `splitChild F childOf u` (whose clause list is `Row.leafClauses r childOf u`);
* a `pending` row: nothing.

One job per line: `i<TAB>s`, where `s` is `Row.ser r` of row `i` of `SB.Rooted.M5.rows`, as written by
`ramsey/runs/k28_rooted/m5_final/SerRows.lean` (`lean --run` on the Lean constant). The job is parsed
back into a `Row`, and the program prints `SER<TAB>i<TAB>Row.ser` of the parsed row; the driver checks
that this equals the input text, so the printed row is the row of the Lean constant (`Row.ser` is
injective on rows with non-empty leaves). Then, per file, `OK<TAB>i<TAB>j<TAB>path<TAB>nv<TAB>nclauses`
(`j = -` for a direct row), or `ERROR<TAB>i<TAB>message`. -/
open LRATCatcher.Rooted SB.Rooted.M5

def parseNat? (s : String) : Option Nat := s.toNat?

def parseInt? (s : String) : Option Int := s.toInt?

def parseList? {α} (sep : String) (f : String → Option α) (s : String) : Option (List α) :=
  if s.isEmpty then some [] else (s.splitOn sep).mapM f

def parsePair? (s : String) : Option (Nat × Nat) :=
  match s.splitOn "-" with
  | [a, b] => do pure ((← a.toNat?), (← b.toNat?))
  | _ => none

def parseOpt? : String → Option OptSet
  | "1" => some .o1
  | "2" => some .o2
  | "3" => some .o3
  | _ => none

def parseVerdict? (s : String) : Option Verdict :=
  if s == "D" then some .direct
  else if s == "P" then some .pending
  else match s.splitOn ";" with
    | ["S", t, n, ls] => do
      let n ← n.toNat?
      let us ← (ls.splitOn "/").mapM (parseList? "," parseInt?)
      pure (.split t n us)
    | _ => none

def parseRow? (s : String) : Option Row :=
  match s.splitOn "|" with
  | [key, h, o, v] => do
    let ks ← parseList? "," parseNat? key
    match ks with
    | [n8, n9, n10, v8, v9, v10] =>
      pure ⟨n8, n9, n10, v8, v9, v10, ⟨← parseList? "," parsePair? h, ← parseOpt? o, ← parseVerdict? v⟩⟩
    | _ => none
  | _ => none

def printTo (path : String) (F : Formula) : IO Unit :=
  IO.FS.withFile path .write fun h => writeDimacs h F

def runJob (out : String) (line : String) : IO Bool := do
  match line.splitOn "\t" with
  | [i, s] =>
    match parseRow? s with
    | none => IO.println s!"ERROR\t{i}\tparse"; return false
    | some r =>
      IO.println s!"SER\t{i}\t{r.ser}"
      match r.e.v with
      | .pending => return true
      | v =>
        match r.formula with
        | .error e => IO.println s!"ERROR\t{i}\t{e}"; return false
        | .ok F =>
          match v with
          | .split t _ us =>
            let mut j := 0
            for u in us do
              let G := splitChild F t u
              let p := s!"{out}/{i}_{j}.cnf"
              printTo p G
              IO.println s!"OK\t{i}\t{j}\t{p}\t{G.nv}\t{G.clauses.size}"
              (← IO.getStdout).flush
              j := j + 1
            return true
          | _ =>
            let p := s!"{out}/{i}.cnf"
            printTo p F
            IO.println s!"OK\t{i}\t-\t{p}\t{F.nv}\t{F.clauses.size}"
            (← IO.getStdout).flush
            return true
  | _ => IO.println s!"ERROR\t-\tbad job line"; return false

def main (args : List String) : IO UInt32 := do
  match args with
  | [out, jobs] =>
    let text ← if jobs == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile jobs
    let mut ok := true
    for line in text.splitOn "\n" do
      if line.trimAscii.isEmpty then continue
      if !(← runJob out line) then ok := false
    return if ok then 0 else 1
  | _ => IO.eprintln "usage: m5-print OUTDIR JOBS|-"; return 1
