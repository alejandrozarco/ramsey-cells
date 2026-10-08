/- Part 7 of the kernel checks of k10_c082 (split from C_k10_c082.lean on 2026-10-07 for M5:
   one module needed more than 9 GB). Same theorems, unchanged. -/
import RootedM4.Cover
import RootedM4.CoverData.F_k10_c082

namespace SB.Rooted.M4.CoverData
open SB.Rooted.M4.Cover

theorem k10_c082_b68_ok : k10_c082_b68.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b69_ok : k10_c082_b69.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b70_ok : k10_c082_b70.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b71_ok : k10_c082_b71.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b72_ok : k10_c082_b72.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b73_ok : k10_c082_b73.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b74_ok : k10_c082_b74.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b75_ok : k10_c082_b75.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b76_ok : k10_c082_b76.all (blockOKB 10 0 8 2) = true := by decide +kernel

end SB.Rooted.M4.CoverData
