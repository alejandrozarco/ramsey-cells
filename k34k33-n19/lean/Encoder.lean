/-
# A Lean port of `gen_ramsey.py`, for the bipartite cells

This closes obligation O7: that the DIMACS the search refuted is the file the
encoder is *described* as producing. Until now that was a human claim about a
Python script; here the clause list is defined in Lean and compared with the
parsed file.

Faithfulness is by construction, not by comment: every clause family below is a
transcription of the corresponding loop in `gen_ramsey.py`, in the same order,
with the same variable allocation order. The comparison theorem then checks the
transcription against the actual file.

Conventions, matching the Python exactly:
* vertices `1..n`; edges `(i,j)` with `i<j` in row-major order, index from 0;
* `var e c = edgeIdx e * r + c`, colours `1..r`, so edge variables occupy
  `1 .. E*r` and auxiliary variables follow in allocation order;
* auxiliary variables are allocated colour by colour: for each `s`-set, first
  the codegree indicators `y`, then the counter registers `R`, and only after
  every colour are the vertex-lex auxiliaries allocated.

Literals are produced as DIMACS `Int`s and converted with `LRATCatcher.dimacsLit`
(`l ↦ (|l| - 1, l > 0)`), the same function `parseDimacs` uses, so the two sides
of the comparison cannot drift on the ±1 convention.
-/
import LRATCatcher.Basic

open Std.Sat

namespace LRATCatcher.Encoder

/-! ## Combinatorial helpers -/

/-- `1, 2, …, n`. -/
def verts (n : Nat) : List Nat := List.range' 1 n

/-- Subsets of size `k`, in the lexicographic order `itertools.combinations`
yields on an ascending list. -/
def combos : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (combos k xs).map (x :: ·) ++ combos (k + 1) xs

/-- Edges of `K_n` in row-major order: `(1,2), (1,3), …, (1,n), (2,3), …`. -/
def edges (n : Nat) : List (Nat × Nat) :=
  (verts n).flatMap fun i => (List.range' (i + 1) (n - i)).map fun j => (i, j)

/-- Position of `(i,j)` in `edges n`, i.e. the Python `edge_index`. -/
def edgeIdx (n i j : Nat) : Nat :=
  -- edges before row i: sum_{a=1}^{i-1} (n-a); then offset within row i
  ((i - 1) * n - (i - 1) * i / 2) + (j - i - 1)

/-- `var (i,j) c`, one-based as in the Python. -/
def var (n r i j c : Nat) : Nat := (edgeIdx n i j) * r + c

/-- The variable for the unordered pair `{u,v}`. -/
def varU (n r u v c : Nat) : Nat :=
  if u < v then var n r u v c else var n r v u c

/-! ## The clause families

Each definition below mirrors one loop of `gen_ramsey.py`'s `build`. Clauses are
accumulated in the Python's emission order. -/

/-- ALO + pairwise AMO, per edge. For `r = 2` this is one positive and one
negative clause per edge. -/
def edgeClauses (n r : Nat) : List (List Int) :=
  (edges n).flatMap fun e =>
    let alo : List Int := (List.range' 1 r).map fun c => (var n r e.1 e.2 c : Int)
    let amo : List (List Int) :=
      (List.range' 1 r).flatMap fun c1 =>
        (List.range' (c1 + 1) (r - c1)).map fun c2 =>
          [-(var n r e.1 e.2 c1 : Int), -(var n r e.1 e.2 c2 : Int)]
    alo :: amo

/-- The codegree block for one colour: for each `s`-set `S`, indicator
variables `y_{S,w}` and a one-directional Sinz counter bounding their sum by
`k = t - 1`. Returns the clauses and the updated variable counter. -/
def codegreeColour (n r c s t : Nat) (nv0 : Nat) : List (List Int) × Nat :=
  let k := t - 1
  (combos s (verts n)).foldl
    (fun (acc : List (List Int) × Nat) S =>
      let (cls, nv) := acc
      let ws := (verts n).filter (fun w => !S.contains w)
      -- indicator variables, one per candidate common neighbour, in ascending w
      let (yCls, ys, nv1) :=
        ws.foldl (fun (st : List (List Int) × List Nat × Nat) w =>
          let (cs, ys, nv) := st
          let y := nv + 1
          let body : List Int := S.map fun v => -(varU n r v w c : Int)
          (cs ++ [body ++ [(y : Int)]], ys ++ [y], y))
          ([], [], nv)
      let m := ys.length
      -- registers R(i,j), i = 1..m-1 outer, j = 1..k inner
      let regBase := nv1
      let reg : Nat → Nat → Int := fun i j => ((regBase + (i - 1) * k + j : Nat) : Int)
      let nv2 := regBase + (m - 1) * k
      let y : Nat → Int := fun i => ((ys.getD (i - 1) 0 : Nat) : Int)
      let base : List (List Int) := [[-(y 1), reg 1 1]]
      let mid : List (List Int) :=
        (List.range' 2 (if m ≥ 3 then m - 2 else 0)).flatMap fun i =>
          ([[-(y i), reg i 1]] : List (List Int))
          ++ (List.range' 1 k).map (fun j => [-(reg (i - 1) j), reg i j])
          ++ (List.range' 2 (k - 1)).map (fun j => [-(y i), -(reg (i - 1) (j - 1)), reg i j])
      let block : List (List Int) :=
        (List.range' 2 (m - 1)).map fun i => [-(y i), -(reg (i - 1) k)]
      (cls ++ yCls ++ base ++ mid ++ block, nv2))
    ([], nv0)

/-- The image of edge `e` under the adjacent transposition `(v, v+1)`. -/
def swapEdge (v : Nat) (e : Nat × Nat) : Nat × Nat :=
  let sg : Nat → Nat := fun x => if x = v then v + 1 else if x = v + 1 then v else x
  let a := sg e.1; let b := sg e.2
  if a < b then (a, b) else (b, a)

/-- Vertex-lex clauses for one adjacent transposition, threading the
equality-chain variable. -/
def lexTransposition (n r v : Nat) (nv0 : Nat) : List (List Int) × Nat :=
  let moved := (edges n).filterMap fun e =>
    let f := swapEdge v e
    if f = e then none else some (e, f)
  let last := moved.length - 1
  let step := fun (st : List (List Int) × Option Nat × Nat) (ie : Nat × (Nat × Nat) × (Nat × Nat)) =>
    let (cls, eqch, nv) := st
    let (t, e, f) := ie
    let prem : List Int := match eqch with | none => [] | some q => [-(q : Int)]
    let cmp : List (List Int) :=
      (List.range' 1 r).flatMap fun cf =>
        (List.range' (cf + 1) (r - cf)).map fun ce =>
          prem ++ [-(var n r e.1 e.2 ce : Int), -(var n r f.1 f.2 cf : Int)]
    if t = last then (cls ++ cmp, eqch, nv)
    else
      let q := nv + 1
      let qCls : List (List Int) :=
        (List.range' 1 r).flatMap fun c =>
          [[-(q : Int), -(var n r e.1 e.2 c : Int), (var n r f.1 f.2 c : Int)],
           [(q : Int), -(var n r e.1 e.2 c : Int), -(var n r f.1 f.2 c : Int)]]
      let nch := q + 1
      let chCls : List (List Int) :=
        match eqch with
        | none => [[-(nch : Int), (q : Int)], [(nch : Int), -(q : Int)]]
        | some p => [[-(nch : Int), (p : Int)], [-(nch : Int), (q : Int)],
                     [(nch : Int), -(p : Int), -(q : Int)]]
      (cls ++ cmp ++ qCls ++ chCls, some nch, nch)
  let (cls, _, nv) := (moved.zipIdx.map (fun p => (p.2, p.1.1, p.1.2))).foldl step ([], none, nv0)
  (cls, nv)

/-- All vertex-lex clauses, transpositions `1..n-1` (no cube). -/
def lexClauses (n r : Nat) (nv0 : Nat) : List (List Int) × Nat :=
  (List.range' 1 (n - 1)).foldl
    (fun (acc : List (List Int) × Nat) v =>
      let (cls, nv) := acc
      let (c2, nv2) := lexTransposition n r v nv
      (cls ++ c2, nv2))
    ([], nv0)

/-! ## The whole encoder -/

/-- `gen_ramsey.py n K{s₀}x{t₀},K{s₁}x{t₁} --vertex-lex`, as DIMACS clauses. -/
def encodeBip (n s₀ t₀ s₁ t₁ : Nat) : List (List Int) :=
  let r := 2
  let E := n * (n - 1) / 2
  let (cg0, nv1) := codegreeColour n r 1 s₀ t₀ (E * r)
  let (cg1, nv2) := codegreeColour n r 2 s₁ t₁ nv1
  let (lex, _) := lexClauses n r nv2
  edgeClauses n r ++ cg0 ++ cg1 ++ lex

/-- Convert to `Std.Sat.CNF Nat` with the very function `parseDimacs` uses, so
the two sides of the comparison cannot disagree on the ±1 convention. -/
def toCNF (cs : List (List Int)) : CNF Nat :=
  { clauses := (cs.map fun c => c.map LRATCatcher.dimacsLit).toArray }

/-- The campaign's cell: `R(K_{3,4}, K_{3,3})` at `n = 19`. -/
def k34k33_n19 : CNF Nat := toCNF (encodeBip 19 3 4 3 3)

end LRATCatcher.Encoder
