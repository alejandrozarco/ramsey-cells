/-
# M4, part 5a: a Lean port of the M0 H-only cover CNF (`runs/k28_rooted/m0_hcover/cnfgen.py`)

Definitions only (core Lean, no Mathlib), so that the DIMACS text can be printed from these terms
and compared with the M0 files. Transcribed in clause order and variable-allocation order from
`Builder` (`_degree_caps`, `_atmost`, `_window`, `ll_clauses`, `blocker`, `dimacs`) and
`build_full`:

* graph variables: `x_e = n + 1` for the `n`-th pair `e = (i, j)`, `i < j < k`, in
  `itertools.combinations(range(k), 2)` order (`pairsK`, closed form `pIdx`);
* (i) for each row `i`, one clause `[-v for v in sub]` per `(cap_i + 1)`-subset `sub` of the row
  (`combos`, the encoder's `itertools.combinations` transcription); an empty clause if `cap_i < 0`;
* (ii) `atMost xs hi` then `atMost (-xs) (E - lo)` (Sinz registers `s[i][j] = nv + i*K + j + 1`);
* (LL) for each recorded permutation `p`, in order, the prefix-equality chain over the moved pairs;
* (B) one clause per blocked word.

`caps`, `lo`, `hi` are computed by M1's `capPy` and `windowPy` (the transcriptions of
`family_params` that M1's filter lemmas are stated for).
-/
import LRATCatcher.RootedEncoder

namespace SB.Rooted.M4.Cover
open LRATCatcher.Rooted

/-- `itertools.combinations(range(k), 2)`. -/
def pairsK (k : Nat) : List (Nat × Nat) :=
  (List.range k).flatMap fun i => (List.range k).filterMap fun j => if i < j then some (i, j) else none

/-- The index of the pair `(i, j)`, `i < j`, in `pairsK k`. -/
def pIdx (k i j : Nat) : Nat := edgeIdx k (i + 1) (j + 1)

/-- `Builder.x(i, j)` as a natural number. -/
def xvN (k i j : Nat) : Nat := (if i < j then pIdx k i j else pIdx k j i) + 1

/-- `Builder.x(i, j)`. -/
def xv (k i j : Nat) : Int := (xvN k i j : Int)

/-- The register clauses of `Builder._atmost(lits, K)` for `1 ≤ K < len(lits)`, `K = Kn`, registers
`s[i][j] = nv + i*K + j + 1` (`i < len - 1`, `j < K`), in Python's clause order. -/
def atMostCore (lits : List Int) (Kn nv : Nat) : List (List Int) :=
  let n := lits.length
  let s : Nat → Nat → Int := fun i j => ((nv + i * Kn + j + 1 : Nat) : Int)
  let l : Nat → Int := fun i => lits.getD i 0
  let c0 : List (List Int) := [-l 0, s 0 0] :: (List.range' 1 (Kn - 1)).map (fun j => [-s 0 j])
  let mid : List (List Int) := (List.range' 1 (n - 2)).flatMap fun i =>
    [[-l i, s i 0], [-s (i - 1) 0, s i 0]] ++
    (List.range' 1 (Kn - 1)).flatMap (fun j => [[-l i, -s (i - 1) (j - 1), s i j], [-s (i - 1) j, s i j]]) ++
    [[-l i, -s (i - 1) (Kn - 1)]]
  let last : List (List Int) := [[-l (n - 1), -s (n - 2) (Kn - 1)]]
  c0 ++ mid ++ last

/-- `Builder._atmost(lits, K)` starting from `nv` allocated variables; returns the clauses and the
new variable count. -/
def atMost (lits : List Int) (K : Int) (nv : Nat) : List (List Int) × Nat :=
  if (lits.length : Int) ≤ K then ([], nv)
  else if K < 0 then ([[]], nv)
  else if K = 0 then (lits.map (fun l => [-l]), nv)
  else (atMostCore lits K.toNat nv, nv + (lits.length - 1) * K.toNat)

/-- The guard of a chain step (`g` in `ll_clauses`). -/
def guard : Option Int → List Int
  | none => []
  | some a => [-a]

/-- `ll_clauses`' chain over the moved pairs `(x_e, x_f)`, guard `g`, from `nv` variables. -/
def llChain : List (Int × Int) → Option Int → Nat → List (List Int) × Nat
  | [], _, nv => ([], nv)
  | [(x, y)], g, nv => ([guard g ++ [-x, y]], nv)
  | (x, y) :: r :: rest, g, nv =>
    let a2 : Int := ((nv + 1 : Nat) : Int)
    let res := llChain (r :: rest) (some a2) (nv + 1)
    ((guard g ++ [-x, y]) :: (guard g ++ [-x, a2]) :: (guard g ++ [y, a2]) :: res.1, res.2)

/-- `p[i]` for a permutation given as a list. -/
def pAt (p : List Nat) (i : Nat) : Nat := p.getD i 0

/-- The moved pairs of `p`: `(var e, var f)` for each pair `e = (i, j)` with `f = srt(p[i], p[j]) ≠ e`. -/
def movedVars (k : Nat) (p : List Nat) : List (Int × Int) :=
  (pairsK k).filterMap fun e =>
    let f := srt (pAt p e.1) (pAt p e.2)
    if f = e then none else some (xv k e.1 e.2, xv k f.1 f.2)

/-- `Builder.ll_clauses(p)`. -/
def llClauses (k : Nat) (p : List Nat) (nv : Nat) : List (List Int) × Nat :=
  llChain (movedVars k p) none nv

/-- `Builder.blocker(word)`: `-(n+1)` where the word has `1`, `n+1` where it has `0`. -/
def blocker (w : List Bool) : List Int :=
  (List.range w.length).map fun n => if w.getD n false then -((n + 1 : Nat) : Int) else ((n + 1 : Nat) : Int)

/-- Filter (i): for each row, the negated `(cap+1)`-subsets (`_degree_caps`). -/
def capClauses (k : Nat) (cap : Nat → Int) : List (List Int) :=
  (List.range k).flatMap fun i =>
    let row := ((List.range k).filter (fun j => j != i)).map (fun j => xvN k i j)
    if cap i < 0 then [[]]
    else (combos ((cap i).toNat + 1) row).map (fun sub => sub.map (fun (v : Nat) => -((v : Int))))

/-- Thread `llClauses` over the permutations, in order. -/
def llAll (k : Nat) : List (List Nat) → Nat → List (List Int) × Nat
  | [], nv => ([], nv)
  | p :: ps, nv =>
    let r := llClauses k p nv
    let rs := llAll k ps r.2
    (r.1 ++ rs.1, rs.2)

/-- **`build_full(k, comp, perms, blocked_words)`**: the clause list and the variable count.
`cap i` and `(lo, hi)` are the family parameters. -/
def coverCNF (k : Nat) (cap : Nat → Int) (lo hi : Int) (perms : List (List Nat))
    (blocked : List (List Bool)) : List (List Int) × Nat :=
  let E := k * (k - 1) / 2
  let xs : List Int := (List.range E).map (fun n => ((n + 1 : Nat) : Int))
  let caps := capClauses k cap
  let w1 := atMost xs hi E
  let w2 := atMost (xs.map (fun v => -v)) ((E : Int) - lo) w1.2
  let ll := llAll k perms w2.2
  (caps ++ w1.1 ++ w2.1 ++ ll.1 ++ blocked.map blocker, ll.2)

/-- The DIMACS body (`p cnf` line and clauses) as `Builder.dimacs` prints it. -/
def dimacsBody (F : List (List Int) × Nat) : String :=
  s!"p cnf {F.2} {F.1.length}\n" ++
    String.join (F.1.map fun c => " ".intercalate (c.map toString) ++ " 0\n")

end SB.Rooted.M4.Cover
