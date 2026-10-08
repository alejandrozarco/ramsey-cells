/-
# A Lean port of the rooted census encoder (`scripts/lemma/rooted_encode.py`)

Milestone M2 of the K2x8/K2x5 (N = 22) census certificate: compute, in Lean, the exact CNF that
`rooted_formula(N, colors, degs, k, comp, H, tight, budget, channel, wallpairs, auth,
base_codegree, shortfall)` writes, so that a `cake_lpr` verdict on a Python-printed file can be
attached to a Lean term. Definitions only; no soundness claims (that is M3).

Transcribed, in clause ORDER and variable-ALLOCATION order, from
* `gen_ramsey.py`            `build` (base layer, no lex, no cube), `edge_index`
* `scripts/lemma/lemma_encode.py`  `Enc`, `Enc.bidir_counter`
* `scripts/lemma/typed_encode.py`  `bounds`, `budget_of`, `add_counting` (classcounts off)
* `scripts/lemma/rooted_encode.py` `cells_of`, `lex_leq`, `moved_pairs`, `pair_shortfall`,
                                   `rooted_formula` (cube mode), `write`
* `scripts/lemma/split_certify.py` the child layout: parent clauses ++ one unit per literal.

The comment lines are reproduced too (Python `str` of the dicts/lists involved), so a printed file
is byte-identical to the Python one, not only its clause body.

Implementation note: the encoder is an imperative state monad over an `Array` of clauses, not the
`List`-append style of `Encoder.lean`, because one cube is ~400k clauses and ~23.9k cubes exist.
Python's `KeyError`/`AssertionError` paths are mirrored by recording an error string; a run with a
non-empty error list must be treated as "no formula".
-/

namespace LRATCatcher.Rooted

/-! ## Python-compatible formatting -/

def pyBool (b : Bool) : String := if b then "True" else "False"
def pyList (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"
def pyIntList (xs : List Int) : String := pyList (xs.map toString)
def pyNatList (xs : List Nat) : String := pyList (xs.map toString)
def pyPair (p : Nat × Nat) : String := s!"({p.1}, {p.2})"
def pyTriple (p : Nat × Nat × Nat) : String := s!"({p.1}, {p.2.1}, {p.2.2})"

/-! ## Combinatorics (gen_ramsey conventions) -/

/-- `itertools.combinations(xs, k)` order. -/
def combos : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (combos k xs).map (x :: ·) ++ combos (k + 1) xs

/-- Row-major edge index, from 0 (`edge_index`). Requires `i < j`. -/
def edgeIdx (n i j : Nat) : Nat := ((i - 1) * n - (i - 1) * i / 2) + (j - i - 1)

/-- Edges of `K_n` in row-major order. -/
def edgesOf (n : Nat) : Array (Nat × Nat) := Id.run do
  let mut out := #[]
  for i in [1:n+1] do
    for j in [i+1:n+1] do
      out := out.push (i, j)
  return out

def srt (a b : Nat) : Nat × Nat := if a ≤ b then (a, b) else (b, a)

/-- `var(e, c) = eidx[e] * r + c` for the unordered pair `{a,b}`. -/
def varE (n r : Nat) (a b c : Nat) : Int :=
  let p := srt a b
  ((edgeIdx n p.1 p.2 * r + c : Nat) : Int)

/-! ## The encoder state (`Enc`) -/

structure St where
  nv : Nat
  cls : Array (Array Int)
  errs : Array String

abbrev EncM := StateM St

def fresh : EncM Nat := modifyGet fun s => (s.nv + 1, { s with nv := s.nv + 1 })
def add (c : Array Int) : EncM Unit := modify fun s => { s with cls := s.cls.push c }
def fail (msg : String) : EncM Unit := modify fun s => { s with errs := s.errs.push msg }
def nclauses : EncM Nat := do return (← get).cls.size

/-- A `bidir_counter` result: `rows[i-1][j-1] = R[(i,j)]`, `1 ≤ j ≤ min(i, kmax)`. -/
structure Counter where
  rows : Array (Array Nat)
  deriving Inhabited

def Counter.get? (R : Counter) (i j : Nat) : Option Nat :=
  if i = 0 ∨ j = 0 then none else
  match R.rows[i-1]? with
  | some row => row[j-1]?
  | none => none

/-- `R[(i,j)]` with Python's KeyError mirrored as a recorded error. -/
def Counter.at (R : Counter) (i j : Nat) (ctx : String) : EncM Int := do
  match R.get? i j with
  | some v => return (v : Int)
  | none => fail s!"KeyError ({i}, {j}) in {ctx}"; return 0

def Counter.size (R : Counter) : Nat := R.rows.size

/-- `Enc.bidir_counter(xs, kmax)`, same allocation and clause order. -/
def bidirCounter (xs : Array Int) (kmax : Nat) : EncM Counter := do
  let m := xs.size
  let mut rows : Array (Array Nat) := Array.mkEmpty m
  for i in [1:m+1] do
    let mut row : Array Nat := #[]
    for _ in [1:(min i kmax)+1] do
      row := row.push (← fresh)
    rows := rows.push row
  let R : Counter := ⟨rows⟩
  for i in [1:m+1] do
    let x := xs[i-1]!
    for j in [1:(min i kmax)+1] do
      let rij : Int := ((R.get? i j).getD 0 : Nat)
      let prevJ : Option Int := (R.get? (i-1) j).map (fun v => (v : Int))
      let isT := j == 1
      let prevJm1 : Option Int := if isT then none else (R.get? (i-1) (j-1)).map (fun v => (v : Int))
      if let some p := prevJ then add #[-p, rij]
      if isT then add #[-x, rij]
      else if let some p := prevJm1 then add #[-x, -p, rij]
      let mut c1 : Array Int := #[-rij, x]
      let mut c2 : Array Int := #[-rij]
      if let some p := prevJ then
        c1 := c1.push p; c2 := c2.push p
      if let some p := prevJm1 then c2 := c2.push p
      add c1
      if !isT then add c2
  return R

/-! ## typed_encode helpers -/

/-- `bounds(N, b, r, di, dj, A)` = (blue_lo, blue_hi, red_lo, red_hi). -/
def bounds (N b r di dj A : Int) : Int × Int × Int × Int :=
  let base := (N - 2) - di - dj + 2 * A
  (max 0 (-base), min b (r - base), max 0 base, min r (base + b))

/-- `budget_of(N, b, r, d)`. -/
def budgetOf (N b r d : Int) : Int :=
  let t := N - 1 - d
  d * (r - t) + b * t

/-! ## gen_ramsey.build, base layer -/

/-- Parse `K{s}x{t}` (the only colour kind used by the census). -/
def parseKst (g : String) : Option (Nat × Nat) :=
  let num := fun (cs : List Char) =>
    if cs.isEmpty || !cs.all Char.isDigit then none
    else some (cs.foldl (fun a ch => 10 * a + (ch.toNat - '0'.toNat)) 0)
  match g.toList with
  | 'K' :: rest =>
    match num (rest.takeWhile (· != 'x')), num ((rest.dropWhile (· != 'x')).drop 1) with
    | some s, some t => some (s, t)
    | _, _ => none
  | _ => none

/-- `build(n, colors)` (no swap-break, no lex, no cube) for `K{s}x{t}` colours, r = |colors|.
Returns the comment lines; clauses and variables go into the state. -/
def buildBase (n : Nat) (colors : List String) : EncM (List String) := do
  let r := colors.length
  let E := n * (n - 1) / 2
  let es := edgesOf n
  let mut comments : List String :=
    [s!"c R({",".intercalate colors}) at n={n}: SAT iff R > n",
     s!"c {E} edges x {r} colors = {E*r} edge vars"]
  for e in es do
    add ((List.range' 1 r).map (fun c => varE n r e.1 e.2 c)).toArray
    for c1 in [1:r+1] do
      for c2 in [c1+1:r+1] do
        add #[-(varE n r e.1 e.2 c1), -(varE n r e.1 e.2 c2)]
  let mut cIdx := 1
  for g in colors do
    let c := cIdx
    cIdx := cIdx + 1
    match parseKst g with
    | none => fail s!"base layer: unsupported colour {g}"
    | some (s, t) =>
      let k := t - 1
      let mut nsets := 0
      for S in combos s (List.range' 1 n) do
        nsets := nsets + 1
        let mut ys : Array Int := #[]
        for w in [1:n+1] do
          if S.contains w then continue
          let y ← fresh
          add ((S.map fun v => -(varE n r v w c)).toArray.push (y : Int))
          ys := ys.push (y : Int)
        let m := ys.size
        if !(m > k) then fail "n too small for the bound to bind"
        -- registers R(i,j), i = 1..m-1, j = 1..k
        let mut R : Array (Array Int) := #[]
        for _ in [1:m] do
          let mut row : Array Int := #[]
          for _ in [1:k+1] do
            row := row.push ((← fresh) : Int)
          R := R.push row
        let reg := fun (i j : Nat) => (R[i-1]!)[j-1]!
        add #[-(ys[0]!), reg 1 1]
        for i in [2:m] do
          add #[-(ys[i-1]!), reg i 1]
          for j in [1:k+1] do
            add #[-(reg (i-1) j), reg i j]
          for j in [2:k+1] do
            add #[-(ys[i-1]!), -(reg (i-1) (j-1)), reg i j]
        for i in [2:m+1] do
          add #[-(ys[i-1]!), -(reg (i-1) k)]
      comments := comments ++
        [s!"c color {c} forbids {g} (codegree): {nsets} {s}-sets, <= {k} common nbrs each"]
  return comments

/-! ## rooted_encode.cells_of -/

structure Cells where
  D : Array Nat                       -- D[v-1]
  ncells : Array (Nat × Nat × Nat)    -- (lo, hi, degree)
  wcells : Array (Nat × Nat × Nat)

def lookup (comp : List (Nat × Nat)) (d : Nat) : Nat :=
  match comp.find? (·.1 == d) with | some p => p.2 | none => 0

def cellsOf (N : Nat) (degs : List Nat) (k : Nat) (comp : List (Nat × Nat)) :
    Except String Cells := do
  let vals := (degs.eraseDups).mergeSort (· ≤ ·)
  let count := fun d => degs.count d
  if count k < 1 then throw "root degree not present"
  let rest := fun d => if d == k then count d - 1 else count d
  for (d, c) in comp do
    if !(rest d ≥ c) then
      throw s!"composition needs {c} neighbours of degree {d}, only {rest d} available"
  if (comp.map (·.2)).sum != k then throw "composition must sum to the root degree"
  let mut D : Array Nat := #[k]
  let mut ncells := #[]
  let mut wcells := #[]
  let mut pos := 2
  for d in vals do
    let c := lookup comp d
    if c != 0 then
      ncells := ncells.push (pos, pos + c - 1, d)
      for _ in [0:c] do D := D.push d
      pos := pos + c
  for d in vals do
    let c := rest d - lookup comp d
    if c != 0 then
      wcells := wcells.push (pos, pos + c - 1, d)
      for _ in [0:c] do D := D.push d
      pos := pos + c
  if D.size != N then throw "len(D) != N"
  return ⟨D, ncells, wcells⟩

/-! ## typed_encode.add_counting (classcounts off) -/

structure CountOut where
  counts : List (String × Nat)
  Ry : Array Counter      -- by row-major pair index
  Rz : Array Counter

/-- `add_counting(enc, N, b, r, D, var, tight, budget, channel=channel)`; colour 2 = blue. -/
def addCounting (N b r : Nat) (D : Array Nat) (tight budget channel : Bool) : EncM CountOut := do
  let var := fun (i j c : Nat) => varE N 2 i j c
  let n0 ← nclauses
  let Dz := fun (v : Nat) => ((D[v-1]! : Nat) : Int)
  let Lam := fun (v : Nat) => budgetOf N b r (Dz v)
  -- exact blue degree
  for v in [1:N+1] do
    let mut xs : Array Int := #[]
    for u in [1:N+1] do
      if u != v then xs := xs.push (var v u 2)
    let m := xs.size
    let d := D[v-1]!
    let R ← bidirCounter xs (min m (d + 1))
    if d ≥ 1 then add #[← R.at m d "degree"]
    if d + 1 ≤ m then add #[-(← R.at m (d+1) "degree")]
  let nDeg := (← nclauses) - n0
  let M := N - 2
  let mut Ry : Array Counter := #[]
  let mut Rz : Array Counter := #[]
  for (i, j) in edgesOf N do
    let di := Dz i; let dj := Dz j
    let A := var i j 2
    let mut ys : Array Int := #[]
    let mut zs : Array Int := #[]
    for w in [1:N+1] do
      if w == i || w == j then continue
      let y ← fresh
      ys := ys.push (y : Int)
      add #[-(var i w 2), -(var j w 2), y]; add #[-(y : Int), var i w 2]; add #[-(y : Int), var j w 2]
      let z ← fresh
      zs := zs.push (z : Int)
      add #[-(var i w 1), -(var j w 1), z]; add #[-(z : Int), var i w 1]; add #[-(z : Int), var j w 1]
    let ry ← bidirCounter ys (min M (b + 1))
    let rz ← bidirCounter zs (min M (r + 1))
    Ry := Ry.push ry; Rz := Rz.push rz
    for a in [0, 1] do
      let L : Int := ((N : Int) - 2) - di - dj + 2 * (a : Int)
      let (bl0, bh0, rl0, rh0) := bounds N b r di dj a
      let mut bl := bl0; let mut bh := bh0; let mut rl := rl0; let mut rh := rh0
      if tight then
        let lam := min (Lam i) (Lam j)
        if a == 1 then rl := max rl ((r : Int) - lam) else bl := max bl ((b : Int) - lam)
        bl := max bl (rl - L); rl := max rl (bl + L); bh := min bh (rh - L); rh := min rh (bh + L)
      let cond : Int := if a == 1 then -A else A
      if bl > bh || rl > rh then
        add #[cond]; continue
      if bl ≥ 1 then add #[cond, ← ry.at M bl.toNat "intervals"]
      if bh + 1 ≤ (M : Int) then add #[cond, -(← ry.at M (bh + 1).toNat "intervals")]
      if rl ≥ 1 then add #[cond, ← rz.at M rl.toNat "intervals"]
      if rh + 1 ≤ (M : Int) then add #[cond, -(← rz.at M (rh + 1).toNat "intervals")]
  if channel then
    for (i, j) in edgesOf N do
      let p := edgeIdx N i j
      let A := var i j 2
      let di := Dz i; let dj := Dz j
      for a in [0, 1] do
        let L : Int := ((N : Int) - 2) - di - dj + 2 * (a : Int)
        let cond : Int := if a == 1 then -A else A
        for q in [1:(min M (b + 1))+1] do
          match Ry[p]!.get? M q with
          | none => continue
          | some lhsN =>
            let lhs : Int := lhsN
            let qq : Int := (q : Int) + L
            if qq ≤ 0 then add #[cond, lhs]
            else if qq > (M : Int) || (Rz[p]!.get? M qq.toNat).isNone then add #[cond, -lhs]
            else
              let rzq : Int := ((Rz[p]!.get? M qq.toNat).getD 0 : Nat)
              add #[cond, -lhs, rzq]; add #[cond, lhs, -rzq]
  let nInt := (← nclauses) - n0 - nDeg
  let mut counts := [("degree", nDeg), ("intervals", nInt)]
  if budget then
    for v in [1:N+1] do
      let lam := Lam v
      if lam < 0 then add #[]; continue
      let mut Es : Array Int := #[]
      for u in [1:N+1] do
        if u == v then continue
        let key := srt u v
        let p := edgeIdx N key.1 key.2
        let A := var u v 2
        let top : Int := min lam (max (r : Int) (b : Int))
        for l in [1:top.toNat+1] do
          let P : Int := ((← fresh) : Nat)
          let Q : Int := ((← fresh) : Nat)
          let E : Int := ((← fresh) : Nat)
          if (r : Int) - l < 0 then add #[-P]
          else
            if (r : Int) - l + 1 ≤ (M : Int) then
              let lit := -(← Rz[p]!.at M (r - l + 1) "budget")
              add #[-P, A]; add #[-P, lit]; add #[P, -A, -lit]
            else
              add #[-P, A]; add #[P, -A]
          if (b : Int) - l < 0 then add #[-Q]
          else
            if (b : Int) - l + 1 ≤ (M : Int) then
              let lit := -(← Ry[p]!.at M (b - l + 1) "budget")
              add #[-Q, -A]; add #[-Q, lit]; add #[Q, A, -lit]
            else
              add #[-Q, -A]; add #[Q, A]
          add #[-E, P, Q]; add #[E, -P]; add #[E, -Q]
          Es := Es.push E
      if Es.isEmpty then
        if lam > 0 then add #[]
        continue
      let lamN := lam.toNat
      let Rb ← bidirCounter Es (min Es.size (lamN + 1))
      if lamN ≥ 1 then
        if lamN ≤ Es.size then add #[← Rb.at Es.size lamN "budget"] else add #[]
      if lamN + 1 ≤ Es.size then add #[-(← Rb.at Es.size (lamN + 1) "budget")]
    let nB := (← nclauses) - n0 - nDeg - nInt
    counts := counts ++ [("budget", nB)]
  return ⟨counts, Ry, Rz⟩

/-! ## rooted_encode helpers -/

/-- `lex_leq(enc, pairs, var)` with r = 2. -/
def lexLeq (N : Nat) (pairs : Array ((Nat × Nat) × (Nat × Nat))) : EncM Unit := do
  let var := fun (e : Nat × Nat) (c : Nat) => varE N 2 e.1 e.2 c
  let mut eqch : Option Int := none
  let last := pairs.size - 1
  for t in [0:pairs.size] do
    let (e, f) := pairs[t]!
    let prem : Array Int := match eqch with | none => #[] | some q => #[-q]
    -- cf = 1, ce = 2 is the only (cf < ce) pair for r = 2
    add (prem ++ #[-(var e 2), -(var f 1)])
    if t == last then break
    let q : Int := ((← fresh) : Nat)
    for c in [1:3] do
      add #[-q, -(var e c), var f c]; add #[q, -(var e c), -(var f c)]
    let newch : Int := ((← fresh) : Nat)
    match eqch with
    | none => add #[-newch, q]; add #[newch, -q]
    | some p => add #[-newch, p]; add #[-newch, q]; add #[newch, -p, -q]
    eqch := some newch

/-- `moved_pairs(edges, (va, vb))`. -/
def movedPairs (es : Array (Nat × Nat)) (va vb : Nat) : Array ((Nat × Nat) × (Nat × Nat)) :=
  let sg := fun x => if x == va then vb else if x == vb then va else x
  es.filterMap fun e =>
    let f := srt (sg e.1) (sg e.2)
    if f != e then some (e, f) else none

/-- Backtracking step for `autos`: the remaining positions (source vertex, candidate pool).
Structural recursion over the list of remaining positions (was a `partial def` with an index `t`
into `pos`; changed 2026-10-06 for M3 so that the kernel can reason about it; same output). -/
def autosGo (ok : Array (Nat × Nat) → Bool) :
    List (Nat × Array Nat) →
    (asg : Array (Nat × Nat)) → (used : Array Nat) → (acc : Array (Array (Nat × Nat))) →
    Array (Array (Nat × Nat))
  | [], asg, _, acc =>
    if asg.all (fun (a, b) => a == b) then acc else acc.push asg
  | (v, pool) :: rest, asg, used, acc =>
    pool.foldl (fun acc cand =>
      if used.contains cand then acc
      else
        let asg' := asg.push (v, cand)
        if ok asg' then autosGo ok rest asg' (used.push cand) acc else acc) acc

/-- The degree-preserving automorphisms of `H` (as images on the N-cell vertices), in exactly the
order `itertools.product(*[itertools.permutations(c) for c in cells])` meets them, identity
excluded. Backtracking over positions in cell order with ascending candidates enumerates the
product in lexicographic order; a partial map is pruned only when an edge with both endpoints
determined is sent outside `H`, which the Python's final test would also reject. -/
def autos (cells : Array (Array Nat)) (Hs : Array (Nat × Nat)) : Array (Array (Nat × Nat)) :=
  let pos : Array (Nat × Array Nat) :=
    cells.foldl (fun acc c => acc ++ c.map (fun v => (v, c))) #[]
  let dom : Array Nat := pos.map (·.1)
  let imgOf := fun (asg : Array (Nat × Nat)) (v : Nat) =>
    match asg.find? (·.1 == v) with
    | some p => some p.2
    | none => if dom.contains v then none else some v
  let ok := fun (asg : Array (Nat × Nat)) =>
    Hs.all fun (a, b) =>
      match imgOf asg a, imgOf asg b with
      | some x, some y => Hs.contains (srt x y)
      | _, _ => true
  autosGo ok pos.toList #[] #[] #[]

/-- Python `str` of a shortfall provenance dict. -/
def pySf (xs : List (String × Int)) : String :=
  "{" ++ ", ".intercalate (xs.map fun (k, v) => s!"'{k}': {v}") ++ "}"

/-- `pair_shortfall(enc, N, b, r, D, var, k, Hs, wcells)`; returns the provenance dict. -/
def pairShortfall (N b r : Nat) (D : Array Nat) (k : Nat) (Hs : Array (Nat × Nat))
    (wcells : Array (Nat × Nat × Nat)) (Ry : Array Counter) : EncM (List (String × Int)) := do
  let M := N - 2
  let S := List.range' 2 k
  let W := wcells.toList.flatMap fun (lo, hi, _) => List.range' lo (hi + 1 - lo)
  let inH := fun (a b : Nat) => Hs.contains (srt a b)
  let h := fun (u : Nat) => (Hs.filter fun (x, y) => x == u || y == u).size
  let Dz := fun (v : Nat) => ((D[v-1]! : Nat) : Int)
  let mut sumk : Int := 0
  let mut caps : Array ((Nat × Nat) × Int) := #[]
  for ij in combos 2 S do
    let i := ij[0]!; let j := ij[1]!
    let A : Int := if inH i j then 1 else 0
    let bh := (bounds N b r (Dz i) (Dz j) A).2.1
    let q := (S.filter fun u => u != i && u != j && inH i u && inH j u).length
    caps := caps.push ((i, j), bh)
    sumk := sumk + bh - 1 - q
  let T : Int := (S.map fun i => Dz i - 1 - (h i : Int)).sum
  let m := W.length
  if m == 0 then fail "ZeroDivisionError in pair_shortfall"; return []
  let q : Int := T / (m : Int)          -- m > 0: Int division = Python floor division
  let rho : Int := T % (m : Int)
  let sigmaRaw : Int := sumk - ((m : Int) * q * (q - 1) / 2 + rho * q)
  let sigma : Int := max sigmaRaw 0
  let mut lits : Array Int := #[]
  for ((i, j), bh) in caps do
    let lo : Int := max 1 (bh - max sigma 1 + 1)
    let p := edgeIdx N i j
    -- t = lo + i for i < bh + 1 - lo (was a `while` loop, which is `partial`; changed 2026-10-06 for M3)
    for i in [0:(bh + 1 - lo).toNat] do
      lits := lits.push (-(← Ry[p]!.at M (lo + (i : Int)).toNat "shortfall"))
  let n0 ← nclauses
  if (lits.size : Int) > sigma then
    let s := sigma.toNat
    let Rsf ← bidirCounter lits (s + 1)
    add #[-(← Rsf.at lits.size (s + 1) "shortfall")]
  let ncl := (← nclauses) - n0
  return [("sigma", sigma), ("sigma_raw", sigmaRaw), ("sumk", sumk), ("T", T), ("m", m), ("q", q),
          ("rho", rho), ("lits", lits.size), ("clauses", ncl)]

/-! ## rooted_formula (cube mode) -/

structure Opts where
  tight : Bool := true
  budget : Bool := false
  channel : Bool := false
  wallpairs : Bool := false
  auth : Bool := false
  baseCodegree : Bool := true
  shortfall : Bool := false

structure Formula where
  comments : List String
  nv : Nat
  clauses : Array (Array Int)

/-- `rooted_formula(N, colors, degs_sorted, k, comp, H=H, **opts)`. `comp` is the composition dict
in Python insertion order (zero entries kept or dropped by the caller: both conventions occur). -/
def rootedFormula (N : Nat) (colors : List String) (degs : List Nat) (k : Nat)
    (comp : List (Nat × Nat)) (H : List (Nat × Nat)) (o : Opts) : Except String Formula := do
  let (s, t) ← match colors with
    | [c0, c1] => match parseKst c0, parseKst c1 with
      | some (_, s), some (_, t) => pure (s, t)
      | _, _ => throw "colours must be K{s}x{t}"
    | _ => throw "two colours expected"
  let r := s - 1; let b := t - 1
  let cells ← cellsOf N degs k comp
  let D := cells.D
  let E := N * (N - 1) / 2
  let es := edgesOf N
  let nb := fun (u : Nat) => decide (2 ≤ u) && decide (u ≤ k + 1)
  let Hs : Array (Nat × Nat) :=
    ((H.map fun (a, b) => srt a b).eraseDups.mergeSort (fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 ≤ y.2))).toArray
  let prog : EncM (List String × Nat × List (String × Nat) × Nat × Option (List (String × Int))) := do
    let mut com : List String := []
    if o.baseCodegree then
      com ← buildBase N colors
    else
      let rr := colors.length
      for e in es do
        add ((List.range' 1 rr).map (fun c => varE N rr e.1 e.2 c)).toArray
        for c1 in [1:rr+1] do
          for c2 in [c1+1:rr+1] do
            add #[-(varE N rr e.1 e.2 c1), -(varE N rr e.1 e.2 c2)]
      com := [s!"c R({",".intercalate colors}) at n={N}: SAT iff R > n",
              s!"c {E} edges x {rr} colors = {E * rr} edge vars",
              "c BASE CODEGREE OMITTED (duplicated by add_counting); a refutation of this weaker formula refutes the full one"]
    let nv0 := (← get).nv
    for u in [2:N+1] do
      add #[varE N 2 1 u (if nb u then 2 else 1)]
    let co ← addCounting N b r D o.tight o.budget o.channel
    -- cube mode
    for e in es do
      if nb e.1 && nb e.2 then
        add #[varE N 2 e.1 e.2 (if Hs.contains e then 2 else 1)]
    for (lo, hi, _) in cells.wcells do
      for v in [lo:hi] do
        lexLeq N (movedPairs es v (v + 1))
    if o.wallpairs then
      for (lo, hi, _) in cells.wcells do
        for p in [lo:hi+1] do
          for q in [p+1:hi+1] do
            let mut pairs := #[]
            for x in [1:N+1] do
              if x != p && x != q then pairs := pairs.push (srt p x, srt q x)
            lexLeq N pairs
    let mut nauts := 0
    if o.auth then
      let cl := cells.ncells.map fun (lo, hi, _) => (List.range' lo (hi + 1 - lo)).toArray
      for asg in autos cl Hs do
        let img := fun (v : Nat) => match asg.find? (·.1 == v) with | some p => p.2 | none => v
        let pairs := es.filterMap fun e =>
          let f := srt (img e.1) (img e.2)
          if f != e then some (e, f) else none
        if !pairs.isEmpty then
          lexLeq N pairs; nauts := nauts + 1
    let sf ← if o.shortfall then
        some <$> pairShortfall N b r D k Hs cells.wcells co.Ry
      else pure none
    return (com, nv0, co.counts, nauts, sf)
  let ((com, nv0, counts, nauts, sf), st) := prog.run ⟨E * colors.length, #[], #[]⟩
  if !st.errs.isEmpty then throw (", ".intercalate st.errs.toList)
  let compS := "{" ++ ", ".intercalate (comp.map fun (d, c) => s!"{d}: {c}") ++ "}"
  let cellsS := fun (a : Array (Nat × Nat × Nat)) => pyList (a.toList.map pyTriple)
  let countsS := "{" ++ ", ".intercalate (counts.map fun (k, v) => s!"'{k}': {v}") ++ "}"
  let sfS := match sf with | some d => "; shortfall=" ++ pySf d | none => ""
  let mode := s!"cube H={pyList (Hs.toList.map pyPair)} W-lex adjacent in {cellsS cells.wcells}; " ++
    s!"wallpairs={pyBool o.wallpairs} auth={pyBool o.auth} ({nauts} automorphisms) channel={pyBool o.channel}{sfS}"
  let com := com ++
    [s!"c rooted_encode: root degree {k}, composition {compS}, cells N {cellsS cells.ncells} W {cellsS cells.wcells}; D={pyNatList D.toList}",
     s!"c {mode}; counting {countsS}; tight={pyBool o.tight} budget={pyBool o.budget}; {st.nv - nv0} new vars"]
  return ⟨com, st.nv, st.cls⟩

/-- A split child (`split_certify.py`): the parent's clauses followed by one unit per literal, the
parent comments plus `c split child of {tag} #{hidx}; units {lits}`. -/
def splitChild (F : Formula) (childOf : String) (units : List Int) : Formula :=
  { comments := F.comments ++ [s!"c split child of {childOf}; units {pyIntList units}"],
    nv := F.nv,
    clauses := F.clauses ++ (units.map fun l => #[l]).toArray }

/-! ## Printer (`rooted_encode.write`) -/

def clauseLine (c : Array Int) : String :=
  (" ".intercalate (c.toList.map toString)) ++ " 0\n"

/-- Write the DIMACS file exactly as `write(path, cls, nv, com)` does. -/
def writeDimacs (h : IO.FS.Handle) (F : Formula) : IO Unit := do
  h.putStr ("\n".intercalate F.comments ++ "\n")
  h.putStr s!"p cnf {F.nv} {F.clauses.size}\n"
  let mut buf : String := ""
  let mut n := 0
  for c in F.clauses do
    buf := buf ++ clauseLine c
    n := n + 1
    if n % 4096 == 0 then
      h.putStr buf; buf := ""
  h.putStr buf

end LRATCatcher.Rooted
