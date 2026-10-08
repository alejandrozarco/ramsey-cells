/-
# M3: `rootedFormula` with its loops as named blocks

`rootedFormulaAlt` is `rootedFormula` with the edge-only base layer, row 1, the H units, the W-lex
loops and the wallpairs loops replaced by calls to verbatim copies (`edgeOnlyBlock`, `row1Block`,
`hBlock`, `wlexBlock`, `wallBlock`); `rootedFormula_eq` identifies the two by `rfl`.
-/
import LRATCatcher.RootedEncoder

namespace SB.Rooted
open LRATCatcher.Rooted

def edgeOnlyBlock (N rr : Nat) : EncM Unit := do
  for e in edgesOf N do
    add ((List.range' 1 rr).map (fun c => varE N rr e.1 e.2 c)).toArray
    for c1 in [1:rr+1] do
      for c2 in [c1+1:rr+1] do
        add #[-(varE N rr e.1 e.2 c1), -(varE N rr e.1 e.2 c2)]

def row1Block (N k : Nat) : EncM Unit := do
  let nb := fun (u : Nat) => decide (2 ≤ u) && decide (u ≤ k + 1)
  for u in [2:N+1] do
    add #[varE N 2 1 u (if nb u then 2 else 1)]

def hBlock (N k : Nat) (Hs : Array (Nat × Nat)) : EncM Unit := do
  let nb := fun (u : Nat) => decide (2 ≤ u) && decide (u ≤ k + 1)
  for e in edgesOf N do
    if nb e.1 && nb e.2 then
      add #[varE N 2 e.1 e.2 (if Hs.contains e then 2 else 1)]

def wlexBlock (N : Nat) (wcells : Array (Nat × Nat × Nat)) : EncM Unit := do
  for (lo, hi, _) in wcells do
    for v in [lo:hi] do
      lexLeq N (movedPairs (edgesOf N) v (v + 1))

def wallBlock (N : Nat) (wcells : Array (Nat × Nat × Nat)) : EncM Unit := do
  for (lo, hi, _) in wcells do
    for p in [lo:hi+1] do
      for q in [p+1:hi+1] do
        let mut pairs := #[]
        for x in [1:N+1] do
          if x != p && x != q then pairs := pairs.push (srt p x, srt q x)
        lexLeq N pairs

/-- The `prog` of `rootedFormula` (state monad part), with its loops as named blocks. -/
def progOf (N : Nat) (colors : List String) (k : Nat) (cells : Cells) (Hs : Array (Nat × Nat))
    (o : Opts) (b r : Nat) :
    EncM (List String × Nat × List (String × Nat) × Nat × Option (List (String × Int))) := do
  let D := cells.D
  let E := N * (N - 1) / 2
  let es := edgesOf N
  let mut com : List String := []
  if o.baseCodegree then
    com ← buildBase N colors
  else
    let rr := colors.length
    edgeOnlyBlock N rr
    com := [s!"c R({",".intercalate colors}) at n={N}: SAT iff R > n",
            s!"c {E} edges x {rr} colors = {E * rr} edge vars",
            "c BASE CODEGREE OMITTED (duplicated by add_counting); a refutation of this weaker formula refutes the full one"]
  let nv0 := (← get).nv
  row1Block N k
  let co ← addCounting N b r D o.tight o.budget o.channel
  hBlock N k Hs
  wlexBlock N cells.wcells
  if o.wallpairs then
    wallBlock N cells.wcells
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

def rootedFormulaAlt (N : Nat) (colors : List String) (degs : List Nat) (k : Nat)
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
  let Hs : Array (Nat × Nat) :=
    ((H.map fun (a, b) => srt a b).eraseDups.mergeSort (fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 ≤ y.2))).toArray
  let prog := progOf N colors k cells Hs o b r
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

theorem rootedFormula_eq (N : Nat) (colors : List String) (degs : List Nat) (k : Nat)
    (comp : List (Nat × Nat)) (H : List (Nat × Nat)) (o : Opts) :
    rootedFormula N colors degs k comp H o = rootedFormulaAlt N colors degs k comp H o := by
  rfl

end SB.Rooted
