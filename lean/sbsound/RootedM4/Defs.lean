/-
# M4: shared definitions (the census degree list, the neighbourhood graph, the filters, cubes)

Kept in a light module so that the generated certificate data (`RootedM4.CoverData.*`) does not
depend on the proofs.
-/
import RootedLemmas.FiltersPy
import Sbsound.SBGraph
import LRATCatcher.RootedEncoder

namespace SB.Rooted.M4
open LRATCatcher.Rooted SB

/-- The census's sorted degree list for a histogram (`rooted_run.py`: `[8]*a + [9]*b + [10]*c`). -/
def histDegs (n8 n9 n10 : Nat) : List Nat :=
  List.replicate n8 8 ++ List.replicate n9 9 ++ List.replicate n10 10

/-! ## The neighbourhood graph and the cover hypothesis -/

/-- The degree vector of the root's neighbourhood in cell order (`cnfgen.family_params`). -/
def Dnu (k v8 v9 v10 : Nat) : Fin k → ℤ := fun a => (((histDegs v8 v9 v10)[a.val]! : Nat) : ℤ)

/-- Degree-preserving permutations of the neighbourhood (the cell-preserving group `Γ_N`). -/
def DPres (k v8 v9 v10 : Nat) (p : Equiv.Perm (Fin k)) : Prop :=
  ∀ i : Fin k, (histDegs v8 v9 v10)[(p i).val]! = (histDegs v8 v9 v10)[i.val]!

/-- The graph `h` as the adjacency function M1's Python forms read (`graph_of(word)`). -/
def gOf {k : Nat} (h : EColouring k 2) : Fin k → Fin k → Bool :=
  fun a b => if hab : a = b then false else decide (h (mkEdge a b hab) = 1)

/-- Filters (i)-(iii) as M0's `cnfgen` / `validate.fail_iii` compute them (M1 `FiltersPy`). -/
def FiltersOK (k : Nat) (D : Fin k → ℤ) (g : Fin k → Fin k → Bool) : Prop :=
  (∀ a, (popRow g a : ℤ) ≤ capPy k D a) ∧
  ((windowPy k D).1 ≤ edgesPy g ∧ (edgesPy g : ℤ) ≤ (windowPy k D).2) ∧
  (∀ U, failIIIPy k g D U = false)

/-- The edges of `h` in encoder numbering (position `i` is encoder vertex `i + 2`), row-major. -/
def hEdges {k : Nat} (h : EColouring k 2) : List (Nat × Nat) :=
  (List.finRange k).flatMap fun i => (List.finRange k).filterMap fun j =>
    if hij : i < j then (if h ⟨toLex (i, j), hij⟩ = 1 then some (i.val + 2, j.val + 2) else none)
    else none

/-- A listed cube with the option set of its verdict. -/
structure Cube where
  degs : List Nat
  k : Nat
  comp : List (Nat × Nat)
  H : List (Nat × Nat)
  o : Opts

end SB.Rooted.M4
