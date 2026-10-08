/-
# M5: the listed words of an M0 certificate, chunk by chunk

`listedWords_rawCert`: the listed words of `rawCert k v8 v9 v10 perms raw` are the decoded bitmasks of the
raw entries with `U = 0`, in order. With it, the per-family identity
`(listedWords fc).map (wordEdges k) = LW` is proved from one small `decide +kernel` per raw data chunk
(`RootedM5/Fam/W_*.lean`), instead of evaluating `listedWords (certOf …)` as a whole in the kernel (for
the family `k10_c082`, 29,329 blockers, that ran over 15 min and 10 GB on the build machine).
-/
import RootedM4.Cover

namespace SB.Rooted.M5
open SB.Rooted.M4 SB.Rooted.M4.Cover

/-- The listed part of a raw data chunk, as `wordEdges` lists. -/
def chunkLW (k : Nat) (raw : List (Nat × Nat)) : List (List (Nat × Nat)) :=
  ((raw.filter (fun b => b.2 == 0)).map (fun b => wbits (k * (k - 1) / 2) b.1)).map (wordEdges k)

theorem chunkLW_append (k : Nat) (a b : List (Nat × Nat)) :
    chunkLW k (a ++ b) = chunkLW k a ++ chunkLW k b := by
  simp [chunkLW, List.filter_append, List.map_append]

theorem listedWords_rawCert (k v8 v9 v10 : Nat) (perms : List (List Nat)) (raw : List (Nat × Nat)) :
    (listedWords (rawCert k v8 v9 v10 perms raw)).map (wordEdges k) = chunkLW k raw := by
  unfold listedWords rawCert chunkLW
  congr 1
  induction raw with
  | nil => rfl
  | cons b t ih =>
    by_cases h : b.2 = 0
    · simp [List.filter_cons, h] at ih ⊢
      exact ih
    · simp [List.filter_cons, h] at ih ⊢
      exact ih

end SB.Rooted.M5
