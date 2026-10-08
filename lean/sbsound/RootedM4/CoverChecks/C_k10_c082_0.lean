/- Part 0 of the kernel checks of k10_c082 (split from C_k10_c082.lean on 2026-10-07 for M5:
   one module needed more than 9 GB). Same theorems, unchanged. -/
import RootedM4.Cover
import RootedM4.CoverData.F_k10_c082

namespace SB.Rooted.M4.CoverData
open SB.Rooted.M4.Cover

theorem k10_c082_p0_ok : k10_c082_p0.all (permOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_p1_ok : k10_c082_p1.all (permOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b0_ok : k10_c082_b0.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b1_ok : k10_c082_b1.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b2_ok : k10_c082_b2.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b3_ok : k10_c082_b3.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b4_ok : k10_c082_b4.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b5_ok : k10_c082_b5.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b6_ok : k10_c082_b6.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b7_ok : k10_c082_b7.all (blockOKB 10 0 8 2) = true := by decide +kernel

end SB.Rooted.M4.CoverData
