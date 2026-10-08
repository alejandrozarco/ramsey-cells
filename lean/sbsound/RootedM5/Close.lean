/-
# M5: the composition with the kernel checks instantiated

`no_good_K22_of_pending'`: no good colouring of `K_22`, assuming only the refutation of the rows that
are still `pending` (`hP`; empty once M6 is merged, see `RootedM5/Attached.lean` and
`FaithfulK28K25Comparator.lean`).
-/
import RootedM5.Final
import RootedM5.Checks.All

namespace SB.Rooted.M5
open SB SB.Rooted SB.Rooted.M4 LRATCatcher.Rooted

theorem no_good_K22_of_pending'
    (hP : ∀ r ∈ rows, r.e.v = .pending → ∀ cells : Cells,
      cellsOf 22 r.toCube.degs r.toCube.k r.toCube.comp = .ok cells → CubeWF cells →
      ¬ ∃ a : EColouring 22 2, NoKst a 0 2 8 ∧ NoKst a 1 2 5 ∧
        RootedCanon a r.toCube.k cells (normH r.toCube.H) r.toCube.o) :
    ¬ ∃ b : EColouring 22 2, NoKst b 0 2 8 ∧ NoKst b 1 2 5 :=
  no_good_K22_of_pending table_ok keys_all hP

end SB.Rooted.M5

#print axioms SB.Rooted.M5.no_good_K22_of_pending'
