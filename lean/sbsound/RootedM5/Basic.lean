/-
# M5: the cube table (core-only definitions)

One entry per listed cube of the rooted census at `n = 22` (23,886 cubes in 781 cases), with the
option set under which its cake_lpr verdict was recorded and the shape of that verdict:

* `direct`: cake_lpr verified the DIMACS file of the cube's own formula;
* `split childOf fuel leaves`: the cube was split (`split_certify.py`), cake_lpr verified the file of
  every leaf `splitChild F childOf u` (`u ∈ leaves`), and `coversB fuel leaves` is checked by the
  kernel (`RootedM5/Checks`);
* `pending`: no verdict attached yet (M6 still running).

This module and the data modules `RootedM5/Data/*` import only the encoder
(`LRATCatcher.RootedEncoder`, core Lean), so that the printer `RootedM5Print.lean` can be compiled
without Mathlib. `Row.clauses` / `Row.leafClauses` are the clause lists of the encoder's formula;
if the encoder returned an error they are `[]` (the empty, satisfiable CNF), so a verdict axiom
about an erroring cube would be refutable, and the proof (`RootedM5/Final.lean`) never needs a
kernel evaluation of `rootedFormula` (it cases on the result).
-/
import LRATCatcher.RootedEncoder

namespace SB.Rooted.M5
open LRATCatcher.Rooted

/-- The three option sets of the census ledgers (M2 RESULTS); `tight` on, `shortfall` off. -/
inductive OptSet
  | o1  -- budget only, base codegree on
  | o2  -- budget, channel, wallpairs, auth, base codegree on
  | o3  -- budget, channel, wallpairs, auth, base codegree off
  deriving DecidableEq, Repr

def OptSet.opts : OptSet → Opts
  | .o1 => { budget := true }
  | .o2 => { budget := true, channel := true, wallpairs := true, auth := true }
  | .o3 => { budget := true, channel := true, wallpairs := true, auth := true, baseCodegree := false }

theorem OptSet.shortfall_false (o : OptSet) : o.opts.shortfall = false := by cases o <;> rfl

/-- The recorded verdict of a cube. -/
inductive Verdict
  | direct
  | split (childOf : String) (fuel : Nat) (leaves : List (List Int))
  | pending

def Verdict.isPending : Verdict → Bool
  | .pending => true
  | _ => false

/-- Literal decoding for the data modules (a list of `Nat` literals elaborates much faster than a list
of negative `Int` literals): `2v ↦ v`, `2v+1 ↦ -v`. -/
def decLit (n : Nat) : Int := if n % 2 = 0 then ((n / 2 : Nat) : Int) else -((n / 2 : Nat) : Int)

/-- Decoded leaves of a split. -/
def decLeaves (raw : List (List Nat)) : List (List Int) := raw.map (·.map decLit)

/-- A listed cube of a case: its `H` (the list-file line, `(i, j)` pairs in row-major order), the
option set and the verdict. -/
structure Entry where
  H : List (Nat × Nat)
  os : OptSet
  v : Verdict

/-- One census case `(n8, n9, n10; v8, v9, v10)` with its cubes, in the order of the listed words of
the family's M0 certificate. -/
structure CaseRows where
  n8 : Nat
  n9 : Nat
  n10 : Nat
  v8 : Nat
  v9 : Nat
  v10 : Nat
  entries : List Entry

/-- A cube with its case. -/
structure Row where
  n8 : Nat
  n9 : Nat
  n10 : Nat
  v8 : Nat
  v9 : Nat
  v10 : Nat
  e : Entry

def CaseRows.rows (c : CaseRows) : List Row := c.entries.map (Row.mk c.n8 c.n9 c.n10 c.v8 c.v9 c.v10)

/-- Copies of `histDegs`, `rootOf`, `compF` (`RootedM4`), kept here so that this module is core-only;
`RootedM5/Final.lean` identifies them by `rfl`. -/
def degsOf (n8 n9 n10 : Nat) : List Nat :=
  List.replicate n8 8 ++ List.replicate n9 9 ++ List.replicate n10 10

def rootK (n8 n10 : Nat) : Nat := if 0 < n8 then 8 else if 0 < n10 then 10 else 9

def compOf (v8 v9 v10 : Nat) : List (Nat × Nat) :=
  ([(8, v8), (9, v9), (10, v10)] : List (Nat × Nat)).filter (fun p => p.2 != 0)

/-- The encoder's formula for the cube (the `rooted_encode.py` CNF that cake_lpr checked). -/
def Row.formula (r : Row) : Except String Formula :=
  rootedFormula 22 ["K2x8", "K2x5"] (degsOf r.n8 r.n9 r.n10) (rootK r.n8 r.n10) (compOf r.v8 r.v9 r.v10)
    r.e.H r.e.os.opts

/-- Its clauses (the DIMACS body `writeDimacs` prints), or `[]` if the encoder failed. -/
def Row.clauses (r : Row) : List (List Int) :=
  match r.formula with
  | .ok F => F.clauses.toList.map Array.toList
  | .error _ => []

/-- The clauses of the split leaf with unit literals `u`, or `[]` if the encoder failed. -/
def Row.leafClauses (r : Row) (childOf : String) (u : List Int) : List (List Int) :=
  match r.formula with
  | .ok F => (splitChild F childOf u).clauses.toList.map Array.toList
  | .error _ => []

/-! ## Serialisation (for the printer's binding check, see `RootedM5Print.lean`)

An injective text form of a row: `n8,n9,n10,v8,v9,v10|H|opt|verdict`, with `H` as `a-b` pairs joined by
`,`, opt `1`/`2`/`3`, verdict `D`, `P`, or `S;childOf;fuel;leaf/leaf/...` with a leaf's literals joined
by `,` (`childOf` contains no `;` or `|`). -/

def serPairs (H : List (Nat × Nat)) : String := ",".intercalate (H.map fun p => s!"{p.1}-{p.2}")

def serInts (u : List Int) : String := ",".intercalate (u.map toString)

def OptSet.ser : OptSet → String
  | .o1 => "1"
  | .o2 => "2"
  | .o3 => "3"

def Verdict.ser : Verdict → String
  | .direct => "D"
  | .pending => "P"
  | .split t n us => s!"S;{t};{n};" ++ "/".intercalate (us.map serInts)

def Row.ser (r : Row) : String :=
  s!"{r.n8},{r.n9},{r.n10},{r.v8},{r.v9},{r.v10}|{serPairs r.e.H}|{r.e.os.ser}|{r.e.v.ser}"

end SB.Rooted.M5
