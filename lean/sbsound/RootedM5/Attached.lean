/-
# M5: every row of the table has an attached verdict (no `pending` row)

`all_attached` is a `decide +kernel` over the verdict tags of the 23,886 rows. It fails to build while
some row is `pending` (M6 still running); `m5_final/table_summary.json` lists those rows.
-/
import RootedM5.Table

namespace SB.Rooted.M5

set_option maxRecDepth 100000 in
theorem all_attached : rows.all (fun r => !r.e.v.isPending) = true := by decide +kernel

theorem no_pending : ∀ r ∈ rows, r.e.v ≠ .pending := by
  intro r hr h
  have := List.all_eq_true.mp all_attached r hr
  simp [h, Verdict.isPending] at this

end SB.Rooted.M5

#print axioms SB.Rooted.M5.no_pending
