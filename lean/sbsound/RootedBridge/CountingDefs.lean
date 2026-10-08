/-
# M3: `addCounting` cut into its four blocks

`addCountingAlt` is `addCounting` (typed_encode.add_counting) written as a sequence of four named
blocks, each a verbatim copy of the corresponding loop of the source; `addCounting_eq` identifies
the two by `rfl` (definitional unfolding only). The blocks are then proved separately.
-/
import LRATCatcher.RootedEncoder

namespace SB.Rooted
open LRATCatcher.Rooted

/-- Exact blue degrees (`typed_encode.add_counting`, "degree"). -/
def degBlock (N : Nat) (D : Array Nat) : EncM Unit := do
  let var := fun (i j c : Nat) => varE N 2 i j c
  for v in [1:N+1] do
    let mut xs : Array Int := #[]
    for u in [1:N+1] do
      if u != v then xs := xs.push (var v u 2)
    let m := xs.size
    let d := D[v-1]!
    let R ← bidirCounter xs (min m (d + 1))
    if d ≥ 1 then add #[← R.at m d "degree"]
    if d + 1 ≤ m then add #[-(← R.at m (d+1) "degree")]

/-- The interval clauses of one pair and one colour `a` (after the tightening). -/
def ivEmit (M : Nat) (A : Int) (a : Nat) (ry rz : Counter) (bl bh rl rh : Int) :
    EncM (ForInStep PUnit) := do
  let cond : Int := if a == 1 then -A else A
  if bl > bh || rl > rh then
    add #[cond]
    return ForInStep.yield ()
  if bl ≥ 1 then add #[cond, ← ry.at M bl.toNat "intervals"]
  if bh + 1 ≤ (M : Int) then add #[cond, -(← ry.at M (bh + 1).toNat "intervals")]
  if rl ≥ 1 then add #[cond, ← rz.at M rl.toNat "intervals"]
  if rh + 1 ≤ (M : Int) then add #[cond, -(← rz.at M (rh + 1).toNat "intervals")]
  return ForInStep.yield ()

/-- The tightened interval of `typed_encode.add_counting` (as the encoder computes it). -/
def ivVals (N b r : Nat) (Lami Lamj di dj : Int) (tight : Bool) (a : Nat) : Int × Int × Int × Int :=
  let L : Int := ((N : Int) - 2) - di - dj + 2 * (a : Int)
  let (bl0, bh0, rl0, rh0) := bounds N b r di dj a
  if tight then
    let lam := min Lami Lamj
    let rl1 := if a == 1 then max rl0 ((r : Int) - lam) else rl0
    let bl1 := if a == 1 then bl0 else max bl0 ((b : Int) - lam)
    let bl2 := max bl1 (rl1 - L)
    let rl2 := max rl1 (bl2 + L)
    let bh2 := min bh0 (rh0 - L)
    let rh2 := min rh0 (bh2 + L)
    (bl2, bh2, rl2, rh2)
  else (bl0, bh0, rl0, rh0)

/-- One step of the intervals loop over `a ∈ {0, 1}`, as `ivEmit` of `ivVals`. -/
def ivStep (N b r : Nat) (Lami Lamj di dj : Int) (tight : Bool) (A : Int) (ry rz : Counter)
    (a : Nat) : EncM (ForInStep PUnit) :=
  let v := ivVals N b r Lami Lamj di dj tight a
  ivEmit (N - 2) A a ry rz v.1 v.2.1 v.2.2.1 v.2.2.2

/-- Codegree indicators, bidirectional codegree counters, and the conditional intervals. -/
def ivLoop (N b r : Nat) (D : Array Nat) (tight : Bool) : EncM (Array Counter × Array Counter) := do
  let var := fun (i j c : Nat) => varE N 2 i j c
  let Dz := fun (v : Nat) => ((D[v-1]! : Nat) : Int)
  let Lam := fun (v : Nat) => budgetOf N b r (Dz v)
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
  return (Ry, Rz)

/-- The channel clauses `C_ij ≥ q ↔ R_ij ≥ q + L`. -/
def chanBlock (N b : Nat) (D : Array Nat) (Ry Rz : Array Counter) : EncM Unit := do
  let var := fun (i j c : Nat) => varE N 2 i j c
  let Dz := fun (v : Nat) => ((D[v-1]! : Nat) : Int)
  let M := N - 2
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

/-- The exact deficit sums (B). -/
def budBlock (N b r : Nat) (D : Array Nat) (Ry Rz : Array Counter) : EncM Unit := do
  let var := fun (i j c : Nat) => varE N 2 i j c
  let Dz := fun (v : Nat) => ((D[v-1]! : Nat) : Int)
  let Lam := fun (v : Nat) => budgetOf N b r (Dz v)
  let M := N - 2
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

/-- `addCounting` as the sequence of its blocks. -/
def addCountingAlt (N b r : Nat) (D : Array Nat) (tight budget channel : Bool) : EncM CountOut := do
  let n0 ← nclauses
  degBlock N D
  let nDeg := (← nclauses) - n0
  let (Ry, Rz) ← ivLoop N b r D tight
  if channel then chanBlock N b D Ry Rz
  let nInt := (← nclauses) - n0 - nDeg
  let mut counts := [("degree", nDeg), ("intervals", nInt)]
  if budget then
    budBlock N b r D Ry Rz
    let nB := (← nclauses) - n0 - nDeg - nInt
    counts := counts ++ [("budget", nB)]
  return ⟨counts, Ry, Rz⟩

theorem addCounting_eq (N b r : Nat) (D : Array Nat) (tight budget channel : Bool) :
    addCounting N b r D tight budget channel = addCountingAlt N b r D tight budget channel := by
  rfl

end SB.Rooted

namespace SB.Rooted
open LRATCatcher.Rooted

/-- The body of the `a`-loop of `ivLoop`, verbatim (with `continue` as `return .yield ()`). -/
def ivBodyOrig (N b r : Nat) (D : Array Nat) (tight : Bool) (i j : Nat) (ry rz : Counter) (a : Nat) :
    EncM (ForInStep PUnit) := do
  let var := fun (i j c : Nat) => varE N 2 i j c
  let Dz := fun (v : Nat) => ((D[v-1]! : Nat) : Int)
  let Lam := fun (v : Nat) => budgetOf N b r (Dz v)
  let M := N - 2
  let di := Dz i; let dj := Dz j
  let A := var i j 2
  let L : Int := ((N : Int) - 2) - di - dj + 2 * (a : Int)
  let (bl0, bh0, rl0, rh0) := bounds N b r di dj a
  let mut bl := bl0; let mut bh := bh0; let mut rl := rl0; let mut rh := rh0
  if tight then
    let lam := min (Lam i) (Lam j)
    if a == 1 then rl := max rl ((r : Int) - lam) else bl := max bl ((b : Int) - lam)
    bl := max bl (rl - L); rl := max rl (bl + L); bh := min bh (rh - L); rh := min rh (bh + L)
  let cond : Int := if a == 1 then -A else A
  if bl > bh || rl > rh then
    add #[cond]; return ForInStep.yield ()
  if bl ≥ 1 then add #[cond, ← ry.at M bl.toNat "intervals"]
  if bh + 1 ≤ (M : Int) then add #[cond, -(← ry.at M (bh + 1).toNat "intervals")]
  if rl ≥ 1 then add #[cond, ← rz.at M rl.toNat "intervals"]
  if rh + 1 ≤ (M : Int) then add #[cond, -(← rz.at M (rh + 1).toNat "intervals")]
  return ForInStep.yield ()

theorem ivBodyOrig_eq (N b r : Nat) (D : Array Nat) (tight : Bool) (i j : Nat) (ry rz : Counter)
    (a : Nat) :
    ivBodyOrig N b r D tight i j ry rz a =
    ivStep N b r (budgetOf N b r ((D[i-1]! : Nat) : Int)) (budgetOf N b r ((D[j-1]! : Nat) : Int))
      ((D[i-1]! : Nat) : Int) ((D[j-1]! : Nat) : Int) tight (varE N 2 i j 2) ry rz a := by
  unfold ivBodyOrig ivStep ivVals ivEmit
  cases tight <;> cases h : a == 1 <;> simp <;> rfl

/-- `ivLoop` with its `a`-loop body as `ivBodyOrig`. -/
def ivLoop2 (N b r : Nat) (D : Array Nat) (tight : Bool) : EncM (Array Counter × Array Counter) := do
  let var := fun (i j c : Nat) => varE N 2 i j c
  let M := N - 2
  let mut Ry : Array Counter := #[]
  let mut Rz : Array Counter := #[]
  for (i, j) in edgesOf N do
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
    let _ ← forIn [0, 1] PUnit.unit (fun a _ => ivBodyOrig N b r D tight i j ry rz a)
  return (Ry, Rz)

theorem ivLoop_eq (N b r : Nat) (D : Array Nat) (tight : Bool) :
    ivLoop N b r D tight = ivLoop2 N b r D tight := by
  rfl

end SB.Rooted

namespace SB.Rooted
open LRATCatcher.Rooted

/-- One threshold `l` of the (B) block for the ordered pair `(v, u)`. -/
def budStep (N b r : Nat) (Ry Rz : Array Counter) (p : Nat) (A : Int) (l : Nat) (Es : Array Int) :
    EncM (ForInStep (Array Int)) := do
  let M := N - 2
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
  return ForInStep.yield (Es.push E)

/-- The (B) block's inner loop over `u` for the vertex `v`. -/
def budU (N b r : Nat) (Ry Rz : Array Counter) (lam : Int) (v u : Nat) (Es : Array Int) :
    EncM (ForInStep (Array Int)) := do
  if u == v then return ForInStep.yield Es
  let key := srt u v
  let p := edgeIdx N key.1 key.2
  let A := varE N 2 u v 2
  let top : Int := min lam (max (r : Int) (b : Int))
  let Es ← forIn [1:top.toNat+1] Es (fun l Es => budStep N b r Ry Rz p A l Es)
  return ForInStep.yield Es

/-- The (B) block for one vertex `v`. -/
def budV (N b r : Nat) (D : Array Nat) (Ry Rz : Array Counter) (v : Nat) : EncM (ForInStep PUnit) := do
  let lam := budgetOf N b r ((D[v-1]! : Nat) : Int)
  if lam < 0 then
    add #[]
    return ForInStep.yield ()
  let Es ← forIn [1:N+1] (#[] : Array Int) (fun u Es => budU N b r Ry Rz lam v u Es)
  if Es.isEmpty then
    if lam > 0 then add #[]
    return ForInStep.yield ()
  let lamN := lam.toNat
  let Rb ← bidirCounter Es (min Es.size (lamN + 1))
  if lamN ≥ 1 then
    if lamN ≤ Es.size then add #[← Rb.at Es.size lamN "budget"] else add #[]
  if lamN + 1 ≤ Es.size then add #[-(← Rb.at Es.size (lamN + 1) "budget")]
  return ForInStep.yield ()

def budBlock2 (N b r : Nat) (D : Array Nat) (Ry Rz : Array Counter) : EncM Unit := do
  let _ ← forIn [1:N+1] PUnit.unit (fun v _ => budV N b r D Ry Rz v)
  pure ()

theorem budBlock_eq (N b r : Nat) (D : Array Nat) (Ry Rz : Array Counter) :
    budBlock N b r D Ry Rz = budBlock2 N b r D Ry Rz := by
  rfl

end SB.Rooted

namespace SB.Rooted
open LRATCatcher.Rooted

/-- The `P` clauses of one threshold (`P ↔ A ∧ R ≤ r - l`). -/
def budP (r M : Nat) (Rz : Array Counter) (p : Nat) (A P : Int) (l : Nat) : EncM Unit := do
  if (r : Int) - l < 0 then add #[-P]
  else
    if (r : Int) - l + 1 ≤ (M : Int) then
      let lit := -(← Rz[p]!.at M (r - l + 1) "budget")
      add #[-P, A]; add #[-P, lit]; add #[P, -A, -lit]
    else
      add #[-P, A]; add #[P, -A]

/-- The `Q` clauses of one threshold (`Q ↔ ¬A ∧ C ≤ b - l`). -/
def budQ (b M : Nat) (Ry : Array Counter) (p : Nat) (A Q : Int) (l : Nat) : EncM Unit := do
  if (b : Int) - l < 0 then add #[-Q]
  else
    if (b : Int) - l + 1 ≤ (M : Int) then
      let lit := -(← Ry[p]!.at M (b - l + 1) "budget")
      add #[-Q, -A]; add #[-Q, lit]; add #[Q, A, -lit]
    else
      add #[-Q, -A]; add #[Q, A]

/-- `budStep` as fresh `P, Q, E`, then `budP`, `budQ`, the `E` clauses. -/
def budStep' (N b r : Nat) (Ry Rz : Array Counter) (p : Nat) (A : Int) (l : Nat) (Es : Array Int) :
    EncM (ForInStep (Array Int)) := do
  let P : Int := ((← fresh) : Nat)
  let Q : Int := ((← fresh) : Nat)
  let E : Int := ((← fresh) : Nat)
  budP r (N - 2) Rz p A P l
  budQ b (N - 2) Ry p A Q l
  add #[-E, P, Q]; add #[E, -P]; add #[E, -Q]
  return ForInStep.yield (Es.push E)

theorem budStep_eq (N b r : Nat) (Ry Rz : Array Counter) (p : Nat) (A : Int) (l : Nat) (Es : Array Int) :
    budStep N b r Ry Rz p A l Es = budStep' N b r Ry Rz p A l Es := by
  unfold budStep budStep' budP budQ
  simp only [bind_assoc]
  congr 1; funext P; congr 1; funext Q; congr 1; funext E
  by_cases h1 : (r : Int) - l < 0 <;> by_cases h2 : (b : Int) - l < 0 <;>
    by_cases h3 : (r : Int) - l + 1 ≤ ((N - 2 : Nat) : Int) <;>
    by_cases h4 : (b : Int) - l + 1 ≤ ((N - 2 : Nat) : Int) <;>
    simp [h1, h2, h3, h4, bind_assoc]

end SB.Rooted
