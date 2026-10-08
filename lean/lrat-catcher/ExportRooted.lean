import LRATCatcher.RootedEncoder
/-!  `lratcatch-export-rooted JOBS`  (JOBS = a file, or `-` for stdin)

Prints the rooted census CNF of each job from the LEAN port (`LRATCatcher.Rooted.rootedFormula`),
byte-for-byte in `rooted_encode.write`'s layout (comments, `p cnf nv nclauses`, clauses).

One job per line, TAB-separated `key=value` fields:
  out=PATH            output file (required)
  N=22  colors=K2x8,K2x5
  degs=8,8,9,...      the histogram as a sorted degree list
  root=K              root degree
  comp=9:5,10:3       the composition dict in Python insertion order (zero entries kept if given)
  H=2-8,2-9,...       blue edges inside N(1) (may be empty)
  tight= budget= channel= wallpairs= auth= base_codegree= shortfall=   0/1
                      (defaults: tight=1 base_codegree=1, the rest 0 — rooted_formula's defaults)
  units=256,-282,...  optional: print the split child = parent clauses ++ these unit clauses
  childof=TAG #HIDX   optional: the split child's comment `c split child of TAG #HIDX; units [...]`
Per job one stdout line: `OK<TAB>out<TAB>nv<TAB>nclauses<TAB>encode_ms<TAB>write_ms`, or
`ERROR<TAB>out<TAB>message`. Exit code 1 if any job failed. Consecutive jobs that differ only in
`out`/`units`/`childof` reuse the encoded parent (cheap printing of all children of one split). -/
open LRATCatcher.Rooted

def parseNats (s : String) : List Nat :=
  if s.isEmpty then [] else (s.splitOn ",").map String.toNat!

def parseInts (s : String) : List Int :=
  if s.isEmpty then [] else (s.splitOn ",").map String.toInt!

def parsePairs (sep : String) (s : String) : List (Nat × Nat) :=
  if s.isEmpty then [] else (s.splitOn ",").map fun e =>
    match e.splitOn sep with
    | [a, b] => (a.toNat!, b.toNat!)
    | _ => (0, 0)

def runJob (cache : IO.Ref (Option (String × Formula))) (line : String) : IO Bool := do
  let kv : List (String × String) := (line.splitOn "\t").filterMap fun f =>
    match f.splitOn "=" with
    | k :: rest => some (k, "=".intercalate rest)
    | [] => none
  let get := fun (k : String) (d : String) => (kv.find? (·.1 == k)).map (·.2) |>.getD d
  let flag := fun (k : String) (d : Bool) => match kv.find? (·.1 == k) with
    | some (_, v) => v == "1" || v == "True" || v == "true"
    | none => d
  let out := get "out" ""
  if out.isEmpty then IO.println s!"ERROR\t-\tno out= field"; return false
  let o : Opts := { tight := flag "tight" true, budget := flag "budget" false,
                    channel := flag "channel" false, wallpairs := flag "wallpairs" false,
                    auth := flag "auth" false, baseCodegree := flag "base_codegree" true,
                    shortfall := flag "shortfall" false }
  let t0 ← IO.monoMsNow
  -- consecutive jobs that differ only in out/units/childof (split children of one parent) reuse
  -- the parent formula instead of re-encoding it
  let key := "\t".intercalate ((line.splitOn "\t").filter fun f =>
    !(f.startsWith "out=" || f.startsWith "units=" || f.startsWith "childof="))
  let enc := fun (_ : Unit) => rootedFormula (get "N" "22").toNat! ((get "colors" "K2x8,K2x5").splitOn ",")
      (parseNats (get "degs" "")) (get "root" "0").toNat! (parsePairs ":" (get "comp" ""))
      (parsePairs "-" (get "H" "")) o
  let cached ← cache.get
  let res : Except String Formula := match cached with
    | some (k, F) => if k == key then .ok F else enc ()
    | none => enc ()
  if let .ok F := res then cache.set (some (key, F))
  match res with
  | .error e => IO.println s!"ERROR\t{out}\t{e}"; return false
  | .ok F =>
    let F := match kv.find? (·.1 == "units") with
      | some (_, u) => splitChild F (get "childof" "") (parseInts u)
      | none => F
    -- force the clause array before timing the write
    let ncl := F.clauses.size
    let t1 ← IO.monoMsNow
    IO.FS.withFile out .write fun h => writeDimacs h F
    let t2 ← IO.monoMsNow
    IO.println s!"OK\t{out}\t{F.nv}\t{ncl}\t{t1 - t0}\t{t2 - t1}"
    (← IO.getStdout).flush
    return true

def main (args : List String) : IO UInt32 := do
  match args with
  | [jobs] =>
    let text ← if jobs == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile jobs
    let mut ok := true
    let cache ← IO.mkRef none
    for line in text.splitOn "\n" do
      if line.trimAscii.isEmpty then continue
      if !(← runJob cache line) then ok := false
    return if ok then 0 else 1
  | _ => IO.eprintln "usage: lratcatch-export-rooted JOBS|-"; return 1
