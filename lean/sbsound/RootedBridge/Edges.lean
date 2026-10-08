/-
# M3: the edge variables of the rooted encoder at N = 22, and the edge part of the truthful
assignment

A colouring is presented to the core-level bridge as `col : Nat → Nat → Bool` on the 1-based
vertices `1..22`, `col a b = true` meaning BLUE (encoder colour 2, `SB` colour 1), symmetric.
`varE 22 2 a b c` is the encoder's variable of the unordered pair `{a,b}` in colour `c ∈ {1,2}`
(1 = red, 2 = blue). `σE col` gives every edge variable its truthful value; it is defined through
the encoder's own edge array `edgesOf 22`, whose indexing is checked once by kernel evaluation
(`chkEdges_true`), so no inverse of `edgeIdx` is needed.
-/
import RootedBridge.Spec

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

/-- `edgesOf 22` lists the pairs `i < j` so that pair `(i,j)` sits at index `edgeIdx 22 i j`. -/
def chkEdges : Bool :=
  (edgesOf 22).size == 231 &&
  ((List.range 23).all fun i => (List.range 23).all fun j =>
    !(1 ≤ i && i < j) || (edgesOf 22)[edgeIdx 22 i j]? == some (i, j)) &&
  ((List.range 231).all fun p => match (edgesOf 22)[p]? with
    | some (i, j) => 1 ≤ i && i < j && j ≤ 22 && edgeIdx 22 i j == p
    | none => false)

theorem chkEdges_true : chkEdges = true := by decide +kernel

theorem edgesOf_size : (edgesOf 22).size = 231 := by
  have h := chkEdges_true
  simp only [chkEdges, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem edgesOf_get {i j : Nat} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ 22) :
    (edgesOf 22)[edgeIdx 22 i j]? = some (i, j) := by
  have h := chkEdges_true
  simp only [chkEdges, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1.2 i (by omega) j (by omega)
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    beq_iff_eq] at this
  rcases this with (h1 | h1) | h1
  · omega
  · omega
  · exact h1

theorem edgesOf_mem {p : Nat} (hp : p < 231) :
    ∃ i j, (edgesOf 22)[p]? = some (i, j) ∧ 1 ≤ i ∧ i < j ∧ j ≤ 22 ∧ edgeIdx 22 i j = p := by
  have h := chkEdges_true
  simp only [chkEdges, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.2 p hp
  split at this
  · next i j heq =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨i, j, heq, this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  · simp at this

theorem edgeIdx_lt {i j : Nat} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ 22) : edgeIdx 22 i j < 231 := by
  have h := edgesOf_get hi hij hj
  rw [← edgesOf_size]
  exact (Array.getElem?_eq_some_iff.mp h).1

theorem edgeIdx_inj {i j i' j' : Nat} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ 22)
    (hi' : 1 ≤ i') (hij' : i' < j') (hj' : j' ≤ 22) (h : edgeIdx 22 i j = edgeIdx 22 i' j') :
    i = i' ∧ j = j' := by
  have h1 := edgesOf_get hi hij hj
  have h2 := edgesOf_get hi' hij' hj'
  rw [h, h2] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  exact ⟨h1.1.symm, h1.2.symm⟩

/-- Elements of `edgesOf 22` are valid pairs. -/
theorem mem_edgesOf {e : Nat × Nat} (he : e ∈ edgesOf 22) : 1 ≤ e.1 ∧ e.1 < e.2 ∧ e.2 ≤ 22 := by
  obtain ⟨p, hp, rfl⟩ := Array.getElem_of_mem he
  rw [edgesOf_size] at hp
  obtain ⟨i, j, hg, h1, h2, h3, -⟩ := edgesOf_mem hp
  rw [Array.getElem?_eq_getElem (by rw [edgesOf_size]; exact hp)] at hg
  rw [Option.some.inj hg]
  exact ⟨h1, h2, h3⟩

theorem edgesOf_getElem {p : Nat} (hp : p < (edgesOf 22).size) :
    1 ≤ (edgesOf 22)[p].1 ∧ (edgesOf 22)[p].1 < (edgesOf 22)[p].2 ∧ (edgesOf 22)[p].2 ≤ 22 ∧
      edgeIdx 22 (edgesOf 22)[p].1 (edgesOf 22)[p].2 = p := by
  rw [edgesOf_size] at hp
  obtain ⟨i, j, hg, h1, h2, h3, h4⟩ := edgesOf_mem hp
  rw [Array.getElem?_eq_getElem (by rw [edgesOf_size]; exact hp)] at hg
  rw [Option.some.inj hg]
  exact ⟨h1, h2, h3, h4⟩

/-! ## The colour of a pair and the edge assignment -/

/-- Truth value of "the pair `{a,b}` has encoder colour `c`" (2 = blue, otherwise red). -/
def colV (col : Nat → Nat → Bool) (a b c : Nat) : Bool := if c = 2 then col a b else !col a b

/-- The truthful values of the edge variables `1..462`. -/
def σE (col : Nat → Nat → Bool) (x : Nat) : Bool :=
  match (edgesOf 22)[(x - 1) / 2]? with
  | some (i, j) => if (x - 1) % 2 = 1 then col i j else !col i j
  | none => false

/-- An assignment is truthful on the edge variables. -/
def EdgeOK (col : Nat → Nat → Bool) (σ : Nat → Bool) : Prop := Agree (σE col) σ 462

/-- A valid vertex pair. -/
def VPair (a b : Nat) : Prop := 1 ≤ a ∧ a ≤ 22 ∧ 1 ≤ b ∧ b ≤ 22 ∧ a ≠ b

theorem srt_fst_snd {a b : Nat} (h : a ≠ b) :
    (srt a b).1 < (srt a b).2 ∧ (((srt a b).1 = a ∧ (srt a b).2 = b) ∨ ((srt a b).1 = b ∧ (srt a b).2 = a)) := by
  unfold srt; split <;> simp <;> omega

/-- The number of the edge variable (a natural number in `1..462`). -/
theorem varE_eq {a b c : Nat} :
    varE 22 2 a b c = ((edgeIdx 22 (srt a b).1 (srt a b).2 * 2 + c : Nat) : Int) := rfl

theorem varE_bounds {a b c : Nat} (hab : VPair a b) (hc : c = 1 ∨ c = 2) :
    0 < (varE 22 2 a b c).natAbs ∧ (varE 22 2 a b c).natAbs ≤ 462 ∧ varE 22 2 a b c ≠ 0 := by
  obtain ⟨ha1, ha2, hb1, hb2, hne⟩ := hab
  obtain ⟨h1, h2⟩ := srt_fst_snd hne
  have hlt := edgeIdx_lt (i := (srt a b).1) (j := (srt a b).2) (by omega) h1 (by omega)
  rw [varE_eq, Int.natAbs_natCast]
  omega

/-- **The edge variables are truthful.** -/
theorem lv_varE {col : Nat → Nat → Bool} (hsym : ∀ a b, col a b = col b a) {σ : Nat → Bool}
    (hσ : EdgeOK col σ) {a b c : Nat} (hab : VPair a b) (hc : c = 1 ∨ c = 2) :
    lv σ (varE 22 2 a b c) = colV col a b c := by
  have hb := varE_bounds hab hc
  obtain ⟨ha1, ha2, hb1, hb2, hne⟩ := hab
  obtain ⟨h1, h2⟩ := srt_fst_snd hne
  have hx : 0 < edgeIdx 22 (srt a b).1 (srt a b).2 * 2 + c := by omega
  rw [varE_eq, lv_natCast σ hx, hσ _ (by rw [varE_eq, Int.natAbs_natCast] at hb; exact hb.2.1)]
  unfold σE colV
  have hg := edgesOf_get (i := (srt a b).1) (j := (srt a b).2) (by omega) h1 (by omega)
  have hd : (edgeIdx 22 (srt a b).1 (srt a b).2 * 2 + c - 1) / 2 = edgeIdx 22 (srt a b).1 (srt a b).2 := by
    omega
  rw [hd, hg]
  simp only
  have hcol : col (srt a b).1 (srt a b).2 = col a b := by
    rcases h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]; exact hsym b a
  rcases hc with rfl | rfl
  · have : ¬ ((edgeIdx 22 (srt a b).1 (srt a b).2 * 2 + 1 - 1) % 2 = 1) := by omega
    rw [if_neg this, hcol]; rfl
  · have : (edgeIdx 22 (srt a b).1 (srt a b).2 * 2 + 2 - 1) % 2 = 1 := by omega
    rw [if_pos this, hcol]; rfl

theorem EdgeOK.agree {col : Nat → Nat → Bool} {σ σ' : Nat → Bool} {n : Nat} (h : EdgeOK col σ)
    (hag : Agree σ σ' n) (hn : 462 ≤ n) : EdgeOK col σ' :=
  fun v hv => by rw [hag v (Nat.le_trans hv hn), h v hv]

end SB.Rooted
