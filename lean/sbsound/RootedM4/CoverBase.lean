/-
# M4, part 5b': a family certificate as Lean data, and its cover CNF

`FamCert` holds one M0 family certificate (`m0_hcover/data/<tag>/cert_<tag>.json`): the recorded
permutations in order and the blocked words in CNF order with their kinds. `famCNF` is
`build_full(k, comp, perms, words)` for it. The data modules `RootedM4.CoverData.*` are generated
by `ramsey/runs/k28_rooted/m4_canon/gen_cover_data.py` and import only this module.
-/
import RootedM4.Defs
import RootedM4.CoverCNF

namespace SB.Rooted.M4.Cover
open SB.Rooted.M4

/-- One family's M0 certificate (`cert_<tag>.json`): the recorded permutations in order and the
blocked words in CNF order, each with its kind (`none`: a listed word; `some U`: a filter-(iii)
blocker claimed to fail on the vertex bitmask `U`). -/
structure FamCert where
  k : ℕ
  v8 : ℕ
  v9 : ℕ
  v10 : ℕ
  perms : List (List ℕ)
  blocked : List (List Bool × Option ℕ)

/-- The family's degree vector in cell order. -/
def FamCert.D (fc : FamCert) : Fin fc.k → ℤ := Dnu fc.k fc.v8 fc.v9 fc.v10

/-- The caps of filter (i) as a function of the row index. -/
def FamCert.cap (fc : FamCert) : ℕ → ℤ := fun i => if h : i < fc.k then capPy fc.k fc.D ⟨i, h⟩ else 0

/-- The cover CNF of a family (`build_full`). -/
def famCNF (fc : FamCert) : List (List ℤ) × ℕ :=
  coverCNF fc.k fc.cap (windowPy fc.k fc.D).1 (windowPy fc.k fc.D).2 fc.perms (fc.blocked.map Prod.fst)

/-- The word of a bitmask (bit `n` is character `n` of the word). -/
def wbits (E m : ℕ) : List Bool := (List.range E).map (fun n => m.testBit n)

/-- A certificate from the generated raw data: `(m, U)` is the word with bitmask `m`, listed if
`U = 0`, a filter-(iii) blocker on the vertex bitmask `U` otherwise. -/
def rawCert (k v8 v9 v10 : ℕ) (perms : List (List ℕ)) (raw : List (ℕ × ℕ)) : FamCert :=
  { k := k, v8 := v8, v9 := v9, v10 := v10, perms := perms,
    blocked := raw.map (fun b => (wbits (k * (k - 1) / 2) b.1, if b.2 = 0 then none else some b.2)) }

end SB.Rooted.M4.Cover
