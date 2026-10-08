/- Part 3 of the kernel checks of k10_c082 (split from C_k10_c082.lean on 2026-10-07 for M5:
   one module needed more than 9 GB). Same theorems, unchanged. -/
import RootedM4.Cover
import RootedM4.CoverData.F_k10_c082

namespace SB.Rooted.M4.CoverData
open SB.Rooted.M4.Cover

theorem k10_c082_b28_ok : k10_c082_b28.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b29_ok : k10_c082_b29.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b30_ok : k10_c082_b30.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b31_ok : k10_c082_b31.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b32_ok : k10_c082_b32.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b33_ok : k10_c082_b33.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b34_ok : k10_c082_b34.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b35_ok : k10_c082_b35.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b36_ok : k10_c082_b36.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b37_ok : k10_c082_b37.all (blockOKB 10 0 8 2) = true := by decide +kernel

end SB.Rooted.M4.CoverData
