/-
# M5: every census case has an entry in the table

`keys_all`: for every index tuple that is a census case (`validB`), `table` has an entry with exactly
that case (`decide +kernel` over the 8·11·11·11 tuples in 88 slices; only the case fields of the entries are read).
-/
import RootedM5.Table
import RootedM4.Cells

namespace SB.Rooted.M5
open SB.Rooted.M4

def keyB (n8 n10 v8 v9 : Nat) : Bool :=
  let n9 := 22 - n8 - n10
  let k := rootOf n8 n10
  let v10 := k - v8 - v9
  !validB n8 n9 n10 v8 v9 v10 ||
    table.any (fun c => c.n8 == n8 && c.n9 == n9 && c.n10 == n10 && c.v8 == v8 && c.v9 == v9 &&
      c.v10 == v10)

/-! Cut into 88 slices `(n8, n10)`, one `decide +kernel` each, to keep the kernel's memory small. -/
theorem keys_0_0 : ∀ v8 < 11, ∀ v9 < 11, keyB 0 0 v8 v9 = true := by decide +kernel
theorem keys_0_1 : ∀ v8 < 11, ∀ v9 < 11, keyB 0 1 v8 v9 = true := by decide +kernel
theorem keys_0_2 : ∀ v8 < 11, ∀ v9 < 11, keyB 0 2 v8 v9 = true := by decide +kernel
theorem keys_0_3 : ∀ v8 < 11, ∀ v9 < 11, keyB 0 3 v8 v9 = true := by decide +kernel
theorem keys_0_4 : ∀ v8 < 11, ∀ v9 < 11, keyB 0 4 v8 v9 = true := by decide +kernel
theorem keys_0_5 : ∀ v8 < 11, ∀ v9 < 11, keyB 0 5 v8 v9 = true := by decide +kernel
theorem keys_0_6 : ∀ v8 < 11, ∀ v9 < 11, keyB 0 6 v8 v9 = true := by decide +kernel
theorem keys_0_7 : ∀ v8 < 11, ∀ v9 < 11, keyB 0 7 v8 v9 = true := by decide +kernel
theorem keys_0_8 : ∀ v8 < 11, ∀ v9 < 11, keyB 0 8 v8 v9 = true := by decide +kernel
theorem keys_0_9 : ∀ v8 < 11, ∀ v9 < 11, keyB 0 9 v8 v9 = true := by decide +kernel
theorem keys_0_10 : ∀ v8 < 11, ∀ v9 < 11, keyB 0 10 v8 v9 = true := by decide +kernel
theorem keys_1_0 : ∀ v8 < 11, ∀ v9 < 11, keyB 1 0 v8 v9 = true := by decide +kernel
theorem keys_1_1 : ∀ v8 < 11, ∀ v9 < 11, keyB 1 1 v8 v9 = true := by decide +kernel
theorem keys_1_2 : ∀ v8 < 11, ∀ v9 < 11, keyB 1 2 v8 v9 = true := by decide +kernel
theorem keys_1_3 : ∀ v8 < 11, ∀ v9 < 11, keyB 1 3 v8 v9 = true := by decide +kernel
theorem keys_1_4 : ∀ v8 < 11, ∀ v9 < 11, keyB 1 4 v8 v9 = true := by decide +kernel
theorem keys_1_5 : ∀ v8 < 11, ∀ v9 < 11, keyB 1 5 v8 v9 = true := by decide +kernel
theorem keys_1_6 : ∀ v8 < 11, ∀ v9 < 11, keyB 1 6 v8 v9 = true := by decide +kernel
theorem keys_1_7 : ∀ v8 < 11, ∀ v9 < 11, keyB 1 7 v8 v9 = true := by decide +kernel
theorem keys_1_8 : ∀ v8 < 11, ∀ v9 < 11, keyB 1 8 v8 v9 = true := by decide +kernel
theorem keys_1_9 : ∀ v8 < 11, ∀ v9 < 11, keyB 1 9 v8 v9 = true := by decide +kernel
theorem keys_1_10 : ∀ v8 < 11, ∀ v9 < 11, keyB 1 10 v8 v9 = true := by decide +kernel
theorem keys_2_0 : ∀ v8 < 11, ∀ v9 < 11, keyB 2 0 v8 v9 = true := by decide +kernel
theorem keys_2_1 : ∀ v8 < 11, ∀ v9 < 11, keyB 2 1 v8 v9 = true := by decide +kernel
theorem keys_2_2 : ∀ v8 < 11, ∀ v9 < 11, keyB 2 2 v8 v9 = true := by decide +kernel
theorem keys_2_3 : ∀ v8 < 11, ∀ v9 < 11, keyB 2 3 v8 v9 = true := by decide +kernel
theorem keys_2_4 : ∀ v8 < 11, ∀ v9 < 11, keyB 2 4 v8 v9 = true := by decide +kernel
theorem keys_2_5 : ∀ v8 < 11, ∀ v9 < 11, keyB 2 5 v8 v9 = true := by decide +kernel
theorem keys_2_6 : ∀ v8 < 11, ∀ v9 < 11, keyB 2 6 v8 v9 = true := by decide +kernel
theorem keys_2_7 : ∀ v8 < 11, ∀ v9 < 11, keyB 2 7 v8 v9 = true := by decide +kernel
theorem keys_2_8 : ∀ v8 < 11, ∀ v9 < 11, keyB 2 8 v8 v9 = true := by decide +kernel
theorem keys_2_9 : ∀ v8 < 11, ∀ v9 < 11, keyB 2 9 v8 v9 = true := by decide +kernel
theorem keys_2_10 : ∀ v8 < 11, ∀ v9 < 11, keyB 2 10 v8 v9 = true := by decide +kernel
theorem keys_3_0 : ∀ v8 < 11, ∀ v9 < 11, keyB 3 0 v8 v9 = true := by decide +kernel
theorem keys_3_1 : ∀ v8 < 11, ∀ v9 < 11, keyB 3 1 v8 v9 = true := by decide +kernel
theorem keys_3_2 : ∀ v8 < 11, ∀ v9 < 11, keyB 3 2 v8 v9 = true := by decide +kernel
theorem keys_3_3 : ∀ v8 < 11, ∀ v9 < 11, keyB 3 3 v8 v9 = true := by decide +kernel
theorem keys_3_4 : ∀ v8 < 11, ∀ v9 < 11, keyB 3 4 v8 v9 = true := by decide +kernel
theorem keys_3_5 : ∀ v8 < 11, ∀ v9 < 11, keyB 3 5 v8 v9 = true := by decide +kernel
theorem keys_3_6 : ∀ v8 < 11, ∀ v9 < 11, keyB 3 6 v8 v9 = true := by decide +kernel
theorem keys_3_7 : ∀ v8 < 11, ∀ v9 < 11, keyB 3 7 v8 v9 = true := by decide +kernel
theorem keys_3_8 : ∀ v8 < 11, ∀ v9 < 11, keyB 3 8 v8 v9 = true := by decide +kernel
theorem keys_3_9 : ∀ v8 < 11, ∀ v9 < 11, keyB 3 9 v8 v9 = true := by decide +kernel
theorem keys_3_10 : ∀ v8 < 11, ∀ v9 < 11, keyB 3 10 v8 v9 = true := by decide +kernel
theorem keys_4_0 : ∀ v8 < 11, ∀ v9 < 11, keyB 4 0 v8 v9 = true := by decide +kernel
theorem keys_4_1 : ∀ v8 < 11, ∀ v9 < 11, keyB 4 1 v8 v9 = true := by decide +kernel
theorem keys_4_2 : ∀ v8 < 11, ∀ v9 < 11, keyB 4 2 v8 v9 = true := by decide +kernel
theorem keys_4_3 : ∀ v8 < 11, ∀ v9 < 11, keyB 4 3 v8 v9 = true := by decide +kernel
theorem keys_4_4 : ∀ v8 < 11, ∀ v9 < 11, keyB 4 4 v8 v9 = true := by decide +kernel
theorem keys_4_5 : ∀ v8 < 11, ∀ v9 < 11, keyB 4 5 v8 v9 = true := by decide +kernel
theorem keys_4_6 : ∀ v8 < 11, ∀ v9 < 11, keyB 4 6 v8 v9 = true := by decide +kernel
theorem keys_4_7 : ∀ v8 < 11, ∀ v9 < 11, keyB 4 7 v8 v9 = true := by decide +kernel
theorem keys_4_8 : ∀ v8 < 11, ∀ v9 < 11, keyB 4 8 v8 v9 = true := by decide +kernel
theorem keys_4_9 : ∀ v8 < 11, ∀ v9 < 11, keyB 4 9 v8 v9 = true := by decide +kernel
theorem keys_4_10 : ∀ v8 < 11, ∀ v9 < 11, keyB 4 10 v8 v9 = true := by decide +kernel
theorem keys_5_0 : ∀ v8 < 11, ∀ v9 < 11, keyB 5 0 v8 v9 = true := by decide +kernel
theorem keys_5_1 : ∀ v8 < 11, ∀ v9 < 11, keyB 5 1 v8 v9 = true := by decide +kernel
theorem keys_5_2 : ∀ v8 < 11, ∀ v9 < 11, keyB 5 2 v8 v9 = true := by decide +kernel
theorem keys_5_3 : ∀ v8 < 11, ∀ v9 < 11, keyB 5 3 v8 v9 = true := by decide +kernel
theorem keys_5_4 : ∀ v8 < 11, ∀ v9 < 11, keyB 5 4 v8 v9 = true := by decide +kernel
theorem keys_5_5 : ∀ v8 < 11, ∀ v9 < 11, keyB 5 5 v8 v9 = true := by decide +kernel
theorem keys_5_6 : ∀ v8 < 11, ∀ v9 < 11, keyB 5 6 v8 v9 = true := by decide +kernel
theorem keys_5_7 : ∀ v8 < 11, ∀ v9 < 11, keyB 5 7 v8 v9 = true := by decide +kernel
theorem keys_5_8 : ∀ v8 < 11, ∀ v9 < 11, keyB 5 8 v8 v9 = true := by decide +kernel
theorem keys_5_9 : ∀ v8 < 11, ∀ v9 < 11, keyB 5 9 v8 v9 = true := by decide +kernel
theorem keys_5_10 : ∀ v8 < 11, ∀ v9 < 11, keyB 5 10 v8 v9 = true := by decide +kernel
theorem keys_6_0 : ∀ v8 < 11, ∀ v9 < 11, keyB 6 0 v8 v9 = true := by decide +kernel
theorem keys_6_1 : ∀ v8 < 11, ∀ v9 < 11, keyB 6 1 v8 v9 = true := by decide +kernel
theorem keys_6_2 : ∀ v8 < 11, ∀ v9 < 11, keyB 6 2 v8 v9 = true := by decide +kernel
theorem keys_6_3 : ∀ v8 < 11, ∀ v9 < 11, keyB 6 3 v8 v9 = true := by decide +kernel
theorem keys_6_4 : ∀ v8 < 11, ∀ v9 < 11, keyB 6 4 v8 v9 = true := by decide +kernel
theorem keys_6_5 : ∀ v8 < 11, ∀ v9 < 11, keyB 6 5 v8 v9 = true := by decide +kernel
theorem keys_6_6 : ∀ v8 < 11, ∀ v9 < 11, keyB 6 6 v8 v9 = true := by decide +kernel
theorem keys_6_7 : ∀ v8 < 11, ∀ v9 < 11, keyB 6 7 v8 v9 = true := by decide +kernel
theorem keys_6_8 : ∀ v8 < 11, ∀ v9 < 11, keyB 6 8 v8 v9 = true := by decide +kernel
theorem keys_6_9 : ∀ v8 < 11, ∀ v9 < 11, keyB 6 9 v8 v9 = true := by decide +kernel
theorem keys_6_10 : ∀ v8 < 11, ∀ v9 < 11, keyB 6 10 v8 v9 = true := by decide +kernel
theorem keys_7_0 : ∀ v8 < 11, ∀ v9 < 11, keyB 7 0 v8 v9 = true := by decide +kernel
theorem keys_7_1 : ∀ v8 < 11, ∀ v9 < 11, keyB 7 1 v8 v9 = true := by decide +kernel
theorem keys_7_2 : ∀ v8 < 11, ∀ v9 < 11, keyB 7 2 v8 v9 = true := by decide +kernel
theorem keys_7_3 : ∀ v8 < 11, ∀ v9 < 11, keyB 7 3 v8 v9 = true := by decide +kernel
theorem keys_7_4 : ∀ v8 < 11, ∀ v9 < 11, keyB 7 4 v8 v9 = true := by decide +kernel
theorem keys_7_5 : ∀ v8 < 11, ∀ v9 < 11, keyB 7 5 v8 v9 = true := by decide +kernel
theorem keys_7_6 : ∀ v8 < 11, ∀ v9 < 11, keyB 7 6 v8 v9 = true := by decide +kernel
theorem keys_7_7 : ∀ v8 < 11, ∀ v9 < 11, keyB 7 7 v8 v9 = true := by decide +kernel
theorem keys_7_8 : ∀ v8 < 11, ∀ v9 < 11, keyB 7 8 v8 v9 = true := by decide +kernel
theorem keys_7_9 : ∀ v8 < 11, ∀ v9 < 11, keyB 7 9 v8 v9 = true := by decide +kernel
theorem keys_7_10 : ∀ v8 < 11, ∀ v9 < 11, keyB 7 10 v8 v9 = true := by decide +kernel
theorem keys_0 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, keyB 0 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [keys_0_0, keys_0_1, keys_0_2, keys_0_3, keys_0_4, keys_0_5, keys_0_6, keys_0_7, keys_0_8, keys_0_9, keys_0_10]
theorem keys_1 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, keyB 1 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [keys_1_0, keys_1_1, keys_1_2, keys_1_3, keys_1_4, keys_1_5, keys_1_6, keys_1_7, keys_1_8, keys_1_9, keys_1_10]
theorem keys_2 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, keyB 2 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [keys_2_0, keys_2_1, keys_2_2, keys_2_3, keys_2_4, keys_2_5, keys_2_6, keys_2_7, keys_2_8, keys_2_9, keys_2_10]
theorem keys_3 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, keyB 3 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [keys_3_0, keys_3_1, keys_3_2, keys_3_3, keys_3_4, keys_3_5, keys_3_6, keys_3_7, keys_3_8, keys_3_9, keys_3_10]
theorem keys_4 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, keyB 4 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [keys_4_0, keys_4_1, keys_4_2, keys_4_3, keys_4_4, keys_4_5, keys_4_6, keys_4_7, keys_4_8, keys_4_9, keys_4_10]
theorem keys_5 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, keyB 5 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [keys_5_0, keys_5_1, keys_5_2, keys_5_3, keys_5_4, keys_5_5, keys_5_6, keys_5_7, keys_5_8, keys_5_9, keys_5_10]
theorem keys_6 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, keyB 6 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [keys_6_0, keys_6_1, keys_6_2, keys_6_3, keys_6_4, keys_6_5, keys_6_6, keys_6_7, keys_6_8, keys_6_9, keys_6_10]
theorem keys_7 : ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, keyB 7 n10 v8 v9 = true := by
  intro n10 h
  rcases (by omega : n10 = 0 ∨ n10 = 1 ∨ n10 = 2 ∨ n10 = 3 ∨ n10 = 4 ∨ n10 = 5 ∨ n10 = 6 ∨ n10 = 7 ∨ n10 = 8 ∨ n10 = 9 ∨ n10 = 10) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [keys_7_0, keys_7_1, keys_7_2, keys_7_3, keys_7_4, keys_7_5, keys_7_6, keys_7_7, keys_7_8, keys_7_9, keys_7_10]
theorem keys_all : ∀ n8 < 8, ∀ n10 < 11, ∀ v8 < 11, ∀ v9 < 11, keyB n8 n10 v8 v9 = true := by
  intro n8 h
  rcases (by omega : n8 = 0 ∨ n8 = 1 ∨ n8 = 2 ∨ n8 = 3 ∨ n8 = 4 ∨ n8 = 5 ∨ n8 = 6 ∨ n8 = 7) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [keys_0, keys_1, keys_2, keys_3, keys_4, keys_5, keys_6, keys_7]

end SB.Rooted.M5

#print axioms SB.Rooted.M5.keys_all
