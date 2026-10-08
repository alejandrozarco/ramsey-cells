/- Part 6 of the kernel checks of k10_c082 (split from C_k10_c082.lean on 2026-10-07 for M5:
   one module needed more than 9 GB). Same theorems, unchanged. -/
import RootedM4.Cover
import RootedM4.CoverData.F_k10_c082

namespace SB.Rooted.M4.CoverData
open SB.Rooted.M4.Cover

theorem k10_c082_b58_ok : k10_c082_b58.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b59_ok : k10_c082_b59.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b60_ok : k10_c082_b60.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b61_ok : k10_c082_b61.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b62_ok : k10_c082_b62.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b63_ok : k10_c082_b63.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b64_ok : k10_c082_b64.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b65_ok : k10_c082_b65.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b66_ok : k10_c082_b66.all (blockOKB 10 0 8 2) = true := by decide +kernel
theorem k10_c082_b67_ok : k10_c082_b67.all (blockOKB 10 0 8 2) = true := by decide +kernel

end SB.Rooted.M4.CoverData
