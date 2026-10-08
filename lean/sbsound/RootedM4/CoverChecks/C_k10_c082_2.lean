/- Part 2 of the kernel checks of k10_c082 (split from C_k10_c082.lean on 2026-10-07 for M5:
   one module needed more than 9 GB). Same theorems, unchanged. -/
import RootedM4.Cover
import RootedM4.CoverData.F_k10_c082

namespace SB.Rooted.M4.CoverData
open SB.Rooted.M4.Cover

theorem k10_c082_b18_ok : k10_c082_b18.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b19_ok : k10_c082_b19.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b20_ok : k10_c082_b20.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b21_ok : k10_c082_b21.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b22_ok : k10_c082_b22.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b23_ok : k10_c082_b23.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b24_ok : k10_c082_b24.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b25_ok : k10_c082_b25.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b26_ok : k10_c082_b26.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b27_ok : k10_c082_b27.all (blockOKB 10 0 8 2) = true := by decide +kernel

end SB.Rooted.M4.CoverData
