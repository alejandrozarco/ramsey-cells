/- Part 1 of the kernel checks of k10_c082 (split from C_k10_c082.lean on 2026-10-07 for M5:
   one module needed more than 9 GB). Same theorems, unchanged. -/
import RootedM4.Cover
import RootedM4.CoverData.F_k10_c082

namespace SB.Rooted.M4.CoverData
open SB.Rooted.M4.Cover

theorem k10_c082_b8_ok : k10_c082_b8.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b9_ok : k10_c082_b9.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b10_ok : k10_c082_b10.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b11_ok : k10_c082_b11.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b12_ok : k10_c082_b12.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b13_ok : k10_c082_b13.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b14_ok : k10_c082_b14.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b15_ok : k10_c082_b15.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b16_ok : k10_c082_b16.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b17_ok : k10_c082_b17.all (blockOKB 10 0 8 2) = true := by decide +kernel

end SB.Rooted.M4.CoverData
