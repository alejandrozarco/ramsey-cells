/-
# M3: from "the colouring is lex-below its image under `g`" to the three comparison lists

`LexLeE col g`: walking the edges of `K_22` in the encoder's (row-major) order, at the first edge
`e` whose colour differs from the colour of its image `g e`, `e` is red and `g e` is blue
(red < blue). This is the Nat-level form of `lexView a ≤ lexView (actV τ a)` (the Mathlib side
proves that translation). Here it is turned into `LexOK` for
* `movedPairs (edgesOf 22) v (v+1)`  (W-adjacent transpositions),
* `authPairs asg`                     (enumerated H-automorphisms),
both of the shape `es.filterMap (e ↦ (e, g e) if g e ≠ e)`, and for
* `wallPairs p q`                     (the compact list of the transposition `(p q)`), where the
  first-difference equivalence with the full moved-edge word is proved.
-/
import RootedBridge.Top

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

/-- The image of an edge under a vertex map. -/
def imgE (g : Nat → Nat) (e : Nat × Nat) : Nat × Nat := srt (g e.1) (g e.2)

/-- The colouring is lex-`≤` its image under `g`, along `edgesOf 22` (red < blue). -/
def LexLeE (col : Nat → Nat → Bool) (g : Nat → Nat) : Prop :=
  ∀ p (hp : p < (edgesOf 22).size),
    (∀ p' (hp' : p' < p), colP col (edgesOf 22)[p'] = colP col (imgE g (edgesOf 22)[p'])) →
    ¬ (colP col (edgesOf 22)[p] = true ∧ colP col (imgE g (edgesOf 22)[p]) = false)

/-! ## Positions in a `filterMap` -/

theorem filterMap_pos {α β : Type} (G : α → Option β) :
    ∀ (L : List α) (t : Nat) (ht : t < (L.filterMap G).length),
      ∃ p, ∃ hp : p < L.length, G L[p] = some (L.filterMap G)[t] ∧
        ((L.take p).filterMap G).length = t
  | [], t, ht => by simp at ht
  | x :: xs, t, ht => by
    cases hx : G x with
    | none =>
      have ht' : t < (xs.filterMap G).length := by simpa [List.filterMap_cons, hx] using ht
      obtain ⟨p, hp, h1, h2⟩ := filterMap_pos G xs t ht'
      refine ⟨p + 1, by simp; omega, ?_, ?_⟩
      · simp only [List.getElem_cons_succ]
        rw [h1]; congr 1; simp [List.filterMap_cons, hx]
      · simp [List.take_succ_cons, List.filterMap_cons, hx, h2]
    | some y =>
      cases t with
      | zero =>
        refine ⟨0, by simp, ?_, by simp⟩
        simp [List.filterMap_cons, hx]
      | succ t =>
        have ht' : t < (xs.filterMap G).length := by
          simp [List.filterMap_cons, hx] at ht; omega
        obtain ⟨p, hp, h1, h2⟩ := filterMap_pos G xs t ht'
        refine ⟨p + 1, by simp; omega, ?_, ?_⟩
        · simp only [List.getElem_cons_succ]
          rw [h1]; congr 1; simp [List.filterMap_cons, hx]
        · simp [List.take_succ_cons, List.filterMap_cons, hx, h2]

theorem filterMap_at {α β : Type} (G : α → Option β) (L : List α) (p : Nat) (hp : p < L.length)
    {y : β} (hy : G L[p] = some y) :
    ∃ h : ((L.take p).filterMap G).length < (L.filterMap G).length,
      (L.filterMap G)[((L.take p).filterMap G).length] = y := by
  have hL : L = L.take p ++ L[p] :: L.drop (p + 1) := by
    rw [← List.drop_eq_getElem_cons hp, List.take_append_drop]
  have hfm : L.filterMap G = (L.take p).filterMap G ++ y :: (L.drop (p + 1)).filterMap G := by
    have := congrArg (List.filterMap G) hL
    rw [List.filterMap_append, List.filterMap_cons, hy] at this
    exact this
  refine ⟨by rw [hfm]; simp, ?_⟩
  simp only [hfm]
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp

theorem take_filterMap_lt {α β : Type} (G : α → Option β) (L : List α) {p' p : Nat} (hpp : p' < p)
    (hp : p ≤ L.length) (hp' : p' < L.length) {y : β} (hy : G L[p'] = some y) :
    ((L.take p').filterMap G).length < ((L.take p).filterMap G).length := by
  have h1 : L.take (p' + 1) = L.take p' ++ [L[p']] := List.take_succ_eq_append_getElem hp'
  have h2 : ((L.take (p' + 1)).filterMap G).length = ((L.take p').filterMap G).length + 1 := by
    rw [h1, List.filterMap_append]; simp [hy]
  have h3 : L.take (p' + 1) = (L.take p).take (p' + 1) := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have h4 : ((L.take (p' + 1)).filterMap G).length ≤ ((L.take p).filterMap G).length := by
    rw [h3]
    exact ((List.take_prefix _ _).filterMap G).sublist.length_le
  omega

/-- The pair list of a vertex map: every moved edge with its image, in `edgesOf 22` order. -/
def gPairs (g : Nat → Nat) : Array ((Nat × Nat) × (Nat × Nat)) :=
  (edgesOf 22).filterMap fun e =>
    let f := srt (g e.1) (g e.2)
    if f != e then some (e, f) else none

theorem lexOK_gPairs (col : Nat → Nat → Bool) (g : Nat → Nat) (hL : LexLeE col g) :
    LexOK col (gPairs g) := by
  intro t ht hpre
  let G : Nat × Nat → Option ((Nat × Nat) × (Nat × Nat)) := fun e =>
    let f := srt (g e.1) (g e.2)
    if f != e then some (e, f) else none
  have hpl : (gPairs g).toList = (edgesOf 22).toList.filterMap G := by
    unfold gPairs; rw [Array.toList_filterMap]
  have ht' : t < ((edgesOf 22).toList.filterMap G).length := by rw [← hpl]; simpa using ht
  obtain ⟨p, hp, hGp, hcnt⟩ := filterMap_pos G _ t ht'
  have hpt : (gPairs g)[t] = ((edgesOf 22).toList.filterMap G)[t] := by
    simp only [← Array.getElem_toList, hpl]
  -- the entry at `t` is `(es[p], imgE g es[p])`
  have hGdef : ∀ e x, G e = some x → x = (e, imgE g e) := by
    intro e x hx
    simp only [G] at hx
    split at hx
    · cases hx; rfl
    · cases hx
  have hx := hGdef _ _ hGp
  have hp' : p < (edgesOf 22).size := by simpa using hp
  have hLp := hL p hp' (fun p' hp'' => ?_)
  · rw [hpt, hx]
    simpa [imgE, Array.getElem_toList] using hLp
  · -- earlier edges: unmoved, or moved and hence an earlier pair
    have hp2 : p' < (edgesOf 22).toList.length := by simp; omega
    cases hG' : G (edgesOf 22).toList[p'] with
    | none =>
      simp only [G] at hG'
      split at hG'
      · cases hG'
      · next hne =>
        simp only [bne_iff_ne, ne_eq, Classical.not_not] at hne
        have : imgE g (edgesOf 22)[p'] = (edgesOf 22)[p'] := by
          simpa [imgE, Array.getElem_toList] using hne
        rw [this]
    | some y =>
      have hy := hGdef _ _ hG'
      have hlt := take_filterMap_lt G _ (p' := p') (p := p) hp'' (by omega) hp2 hG'
      obtain ⟨hs, hys⟩ := filterMap_at G _ p' hp2 hG'
      have hs' : ((List.take p' (edgesOf 22).toList).filterMap G).length < (gPairs g).size := by
        have := congrArg List.length hpl; simp at this; omega
      have hlt' : ((List.take p' (edgesOf 22).toList).filterMap G).length < t := hcnt ▸ hlt
      have := hpre _ hlt'
      have hps : (gPairs g)[((List.take p' (edgesOf 22).toList).filterMap G).length]'(by omega) = y := by
        simp only [← Array.getElem_toList, hpl]; exact hys
      rw [hps, hy] at this
      simpa [imgE, Array.getElem_toList] using this

theorem movedPairs_eq_gPairs (va vb : Nat) :
    movedPairs (edgesOf 22) va vb =
      gPairs (fun x => if x == va then vb else if x == vb then va else x) := rfl

theorem authPairs_eq_gPairs (asg : Array (Nat × Nat)) : authPairs asg = gPairs (imgA asg) := rfl

/-! ## The row-major order of `edgeIdx` -/

theorem edgeIdx_row_succ' {n i : Nat} (hi : 1 ≤ i) (hin : i < n) :
    edgeIdx n (i + 1) (i + 2) = edgeIdx n i n + 1 := by
  unfold edgeIdx
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hA : (i' + 1) * (i' + 1 + 1) = i' * (i' + 1) + 2 * (i' + 1) := by
    rw [Nat.mul_add, Nat.add_mul, Nat.mul_one]
    generalize i' * (i' + 1) = m
    omega
  have hD : (i' + 1) * n = i' * n + n := by rw [Nat.add_mul, Nat.one_mul]
  have hB : i' * (i' + 1) ≤ i' * n := Nat.mul_le_mul_left _ (by omega)
  have hE : (i' + 1) * (i' + 1 + 1) / 2 = i' * (i' + 1) / 2 + (i' + 1) := by
    rw [hA, show i' * (i' + 1) + 2 * (i' + 1) = i' * (i' + 1) + (i' + 1) * 2 by omega,
      Nat.add_mul_div_right _ _ (by decide)]
  omega

theorem edgeIdx_same_row' {n i j j' : Nat} (hij : i < j) (hjj : j < j') :
    edgeIdx n i j < edgeIdx n i j' := by
  unfold edgeIdx; omega

theorem edgeIdx_same_row_le' {n i j j' : Nat} (hjj : j ≤ j') : edgeIdx n i j ≤ edgeIdx n i j' := by
  unfold edgeIdx; omega

theorem edgeIdx_rowStart_mono' {n i i' : Nat} (hi : 1 ≤ i) (hii : i ≤ i') (hin : i' ≤ n) :
    edgeIdx n i (i + 1) ≤ edgeIdx n i' (i' + 1) := by
  induction i' with
  | zero => omega
  | succ m ih =>
    by_cases hm : i ≤ m
    · have h1 := ih hm (by omega)
      have h2 : edgeIdx n (m + 1) (m + 1 + 1) = edgeIdx n m n + 1 :=
        edgeIdx_row_succ' (n := n) (i := m) (by omega) (by omega)
      have h3 : edgeIdx n m (m + 1) ≤ edgeIdx n m n := edgeIdx_same_row_le' (by omega)
      omega
    · have : i = m + 1 := by omega
      subst this; exact Nat.le_refl _

theorem edgeIdx_lt_of_lt' {n i j i' j' : Nat} (hi : 1 ≤ i) (hij : i < j) (hjn : j ≤ n)
    (hij' : i' < j') (hjn' : j' ≤ n) (hlt : i < i' ∨ (i = i' ∧ j < j')) :
    edgeIdx n i j < edgeIdx n i' j' := by
  rcases hlt with hlt | ⟨rfl, hlt⟩
  · have h1 : edgeIdx n i j ≤ edgeIdx n i n := edgeIdx_same_row_le' hjn
    have h2 : edgeIdx n (i + 1) (i + 1 + 1) = edgeIdx n i n + 1 :=
      edgeIdx_row_succ' (n := n) (i := i) hi (by omega)
    have h3 : edgeIdx n (i + 1) (i + 1 + 1) ≤ edgeIdx n i' (i' + 1) :=
      edgeIdx_rowStart_mono' (by omega) hlt (by omega)
    have h4 : edgeIdx n i' (i' + 1) ≤ edgeIdx n i' j' := edgeIdx_same_row_le' (by omega)
    omega
  · exact edgeIdx_same_row' hij hlt

/-- On valid pairs, `edgeIdx` order is the row-major (lexicographic) order. -/
theorem edgeIdx_lt_iff {i j i' j' : Nat} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ 22)
    (hi' : 1 ≤ i') (hij' : i' < j') (hj' : j' ≤ 22) :
    edgeIdx 22 i j < edgeIdx 22 i' j' ↔ (i < i' ∨ (i = i' ∧ j < j')) := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy i i' with h1 | h1 | h1
    · exact Or.inl h1
    · subst h1
      rcases Nat.lt_trichotomy j j' with h2 | h2 | h2
      · exact Or.inr ⟨rfl, h2⟩
      · subst h2; omega
      · have := edgeIdx_same_row' (n := 22) hij' h2; omega
    · have := edgeIdx_lt_of_lt' hi' hij' hj' hij hj (Or.inl h1); omega
  · exact edgeIdx_lt_of_lt' hi hij hj hij' hj'

/-! ## The compact wallpairs list -/

/-- The transposition `(p q)` as a vertex map. -/
def swapF (p q : Nat) : Nat → Nat := fun x => if x == p then q else if x == q then p else x

theorem srt_lt_srt_same {p x y : Nat} (hxp : x ≠ p) (hyp : y ≠ p)
    (h : (srt p y).1 < (srt p x).1 ∨ ((srt p y).1 = (srt p x).1 ∧ (srt p y).2 < (srt p x).2)) : y < x := by
  unfold srt at h; split at h <;> split at h <;> simp at h <;> omega

theorem srt_lt_srt_other {p q x y : Nat} (hpq : p < q) (hxp : x ≠ p) (hxq : x ≠ q) (hyp : y ≠ p)
    (hyq : y ≠ q)
    (h : (srt q y).1 < (srt p x).1 ∨ ((srt q y).1 = (srt p x).1 ∧ (srt q y).2 < (srt p x).2)) : y < x := by
  unfold srt at h; split at h <;> split at h <;> simp at h <;> omega

theorem lexOK_wallPairs (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a) {p q : Nat}
    (hp : 1 ≤ p) (hpq : p < q) (hq : q ≤ 22) (hL : LexLeE col (swapF p q)) :
    LexOK col (wallPairs p q) := by
  intro t ht hpre
  let xs := (List.range' 1 22).filter (fun x => x != p && x != q)
  have hxs : (wallPairs p q).toList = xs.map (fun x => (srt p x, srt q x)) := by
    unfold wallPairs; simp [xs]
  have hsorted : xs.Pairwise (· < ·) := (List.pairwise_lt_range' (s := 1) (n := 22)).filter _
  have hmem : ∀ y, y ∈ xs ↔ (1 ≤ y ∧ y ≤ 22 ∧ y ≠ p ∧ y ≠ q) := by
    intro y; simp only [xs, List.mem_filter, List.mem_range'_1, Bool.and_eq_true, bne_iff_ne, ne_eq]
    omega
  have hlen : (wallPairs p q).size = xs.length := by
    rw [← Array.length_toList, hxs, List.length_map]
  have ht' : t < xs.length := by omega
  have hget : ∀ s (hs : s < xs.length), (wallPairs p q)[s]'(by omega) = (srt p xs[s], srt q xs[s]) := by
    intro s hs; simp [← Array.getElem_toList, hxs]
  obtain ⟨x, hxdef⟩ : ∃ x, xs[t] = x := ⟨_, rfl⟩
  obtain ⟨hx1, hx2, hxp, hxq⟩ := (hmem x).mp (hxdef ▸ List.getElem_mem ht')
  have hve : VPair p x := ⟨hp, by omega, hx1, hx2, fun h => hxp h.symm⟩
  obtain ⟨hs1, hs2⟩ := srt_fst_snd (Ne.symm hxp)
  have hE1 : 1 ≤ (srt p x).1 := by omega
  have hE2 : (srt p x).2 ≤ 22 := by omega
  have hP := edgeIdx_lt hE1 hs1 hE2
  have hPget := edgesOf_get hE1 hs1 hE2
  have hPget' : (edgesOf 22)[edgeIdx 22 (srt p x).1 (srt p x).2]'(by rw [edgesOf_size]; exact hP) =
      ((srt p x).1, (srt p x).2) := Option.some.inj ((Array.getElem?_eq_getElem _).symm.trans hPget)
  have himg : imgE (swapF p q) (srt p x) = srt q x := by
    unfold imgE swapF
    by_cases h : p ≤ x
    · have h1 : srt p x = (p, x) := by simp [srt, h]
      rw [h1]
      simp only [beq_self_eq_true, if_true, beq_iff_eq, hxp, hxq, if_false]
    · have h1 : srt p x = (x, p) := by simp [srt, h]
      rw [h1]
      simp only [beq_self_eq_true, if_true, beq_iff_eq, hxp, hxq, if_false]
      have h2 : srt x q = (x, q) := by simp [srt]; omega
      have h3 : srt q x = (x, q) := by simp [srt]; omega
      rw [h2, h3]
  rw [hget t ht', hxdef]
  have key := hL _ (by rw [edgesOf_size]; exact hP) (fun p' hp' => ?_)
  · rw [hPget'] at key
    simpa [colP, ← himg] using key
  · -- an earlier edge: fixed by the transposition, or an earlier pair of the list
    have hp'' : p' < (edgesOf 22).size := by rw [edgesOf_size]; omega
    obtain ⟨hi1, hij, hj2, hidx⟩ := edgesOf_getElem hp''
    generalize (edgesOf 22)[p'] = e at hi1 hij hj2 hidx ⊢
    obtain ⟨i, j⟩ := e
    dsimp only at hi1 hij hj2 hidx ⊢
    have hlt : edgeIdx 22 i j < edgeIdx 22 (srt p x).1 (srt p x).2 := by omega
    rw [edgeIdx_lt_iff hi1 hij hj2 hE1 hs1 hE2] at hlt
    -- the earlier pair, for a vertex `y` before `x`
    have hpair : ∀ y, y < x → y ≠ p → y ≠ q → 1 ≤ y → colP col (srt p y) = colP col (srt q y) := by
      intro y hyx hyp hyq hy1
      obtain ⟨sidx, hsidx, hsy⟩ := List.getElem_of_mem ((hmem y).mpr ⟨hy1, by omega, hyp, hyq⟩)
      have hst : sidx < t := by
        rcases Nat.lt_trichotomy sidx t with h | h | h
        · exact h
        · subst h; omega
        · have := List.pairwise_iff_getElem.mp hsorted t sidx ht' hsidx h; rw [hxdef] at this; omega
      have := hpre sidx (by omega)
      rw [hget sidx hsidx, hsy] at this
      exact this
    -- the image of `srt a y` (one endpoint `a ∈ {p,q}`, the other `y` outside)
    have hsw : ∀ y, y ≠ p → y ≠ q →
        imgE (swapF p q) (srt p y) = srt q y ∧ imgE (swapF p q) (srt q y) = srt p y := by
      intro y hyp hyq
      unfold imgE swapF srt
      constructor <;> split <;> simp only [beq_iff_eq, if_true, hyp, hyq, if_false] <;>
        (try simp only [show q ≠ p from fun h => by omega, if_false]) <;> split <;> simp_all <;> omega
    have hcol : ∀ a b, colP col (srt a b) = col a b := by
      intro a b; unfold colP srt; split <;> simp [hsym]
    by_cases hin : (i = p ∨ i = q ∨ j = p ∨ j = q)
    · by_cases hpq' : i = p ∧ j = q
      · obtain ⟨hip, hjq⟩ := hpq'
        rw [hip, hjq]
        unfold imgE swapF colP srt
        simp only [beq_self_eq_true, if_true, beq_iff_eq, show q ≠ p from fun h => by omega, if_false]
        split <;> simp_all <;> omega
      · -- exactly one endpoint in `{p, q}`
        have hcases : (i = p ∧ j ≠ q) ∨ (j = p) ∨ (i = q) ∨ (j = q ∧ i ≠ p) := by omega
        rcases hcases with ⟨hip, hjq⟩ | hjp | hiq | ⟨hjq, hip⟩
        · have he : (i, j) = srt p j := by rw [hip]; simp [srt]; omega
          have hlt' : (srt p j).1 < (srt p x).1 ∨ ((srt p j).1 = (srt p x).1 ∧ (srt p j).2 < (srt p x).2) := by
            rw [show (srt p j).1 = i from (congrArg Prod.fst he).symm,
              show (srt p j).2 = j from (congrArg Prod.snd he).symm]; exact hlt
          have hyx : j < x := srt_lt_srt_same hxp (by omega) hlt'
          have := hpair j hyx (by omega) hjq (by omega)
          rw [he, (hsw j (by omega) hjq).1]; exact this
        · have he : (i, j) = srt p i := by rw [hjp]; simp [srt]; omega
          have hlt' : (srt p i).1 < (srt p x).1 ∨ ((srt p i).1 = (srt p x).1 ∧ (srt p i).2 < (srt p x).2) := by
            rw [show (srt p i).1 = i from (congrArg Prod.fst he).symm,
              show (srt p i).2 = j from (congrArg Prod.snd he).symm]; exact hlt
          have hyx : i < x := srt_lt_srt_same hxp (by omega) hlt'
          have := hpair i hyx (by omega) (by omega) hi1
          rw [he, (hsw i (by omega) (by omega)).1]; exact this
        · have he : (i, j) = srt q j := by rw [hiq]; simp [srt]; omega
          have hlt' : (srt q j).1 < (srt p x).1 ∨ ((srt q j).1 = (srt p x).1 ∧ (srt q j).2 < (srt p x).2) := by
            rw [show (srt q j).1 = i from (congrArg Prod.fst he).symm,
              show (srt q j).2 = j from (congrArg Prod.snd he).symm]; exact hlt
          have hyx : j < x := srt_lt_srt_other hpq hxp hxq (by omega) (by omega) hlt'
          have := hpair j hyx (by omega) (by omega) (by omega)
          rw [he, (hsw j (by omega) (by omega)).2]; exact this.symm
        · have he : (i, j) = srt q i := by rw [hjq]; simp [srt]; omega
          have hlt' : (srt q i).1 < (srt p x).1 ∨ ((srt q i).1 = (srt p x).1 ∧ (srt q i).2 < (srt p x).2) := by
            rw [show (srt q i).1 = i from (congrArg Prod.fst he).symm,
              show (srt q i).2 = j from (congrArg Prod.snd he).symm]; exact hlt
          have hyx : i < x := srt_lt_srt_other hpq hxp hxq (by omega) (by omega) hlt'
          have := hpair i hyx (by omega) (by omega) hi1
          rw [he, (hsw i (by omega) (by omega)).2]; exact this.symm
    · -- no endpoint in `{p, q}`: the transposition fixes the edge
      have h1 : swapF p q i = i := by unfold swapF; simp only [beq_iff_eq]; split <;> (try split) <;> omega
      have h2 : swapF p q j = j := by unfold swapF; simp only [beq_iff_eq]; split <;> (try split) <;> omega
      unfold imgE; rw [h1, h2]
      have : srt i j = (i, j) := by simp [srt]; omega
      rw [this]

end SB.Rooted

#print axioms SB.Rooted.lexOK_gPairs
#print axioms SB.Rooted.lexOK_wallPairs

namespace SB.Rooted
open LRATCatcher.Rooted

/-- `CoreCanon` with the three symmetry-breaking premises in first-difference form. -/
structure CoreCanonL (col : Nat → Nat → Bool) (k : Nat) (cells : Cells) (Hs : Array (Nat × Nat))
    (o : Opts) : Prop where
  symm : ∀ a b, col a b = col b a
  row1 : ∀ u, 2 ≤ u → u ≤ 22 → col 1 u = (decide (2 ≤ u) && decide (u ≤ k + 1))
  hunits : ∀ i j, 1 ≤ i → i < j → j ≤ 22 → 2 ≤ i → j ≤ k + 1 → col i j = Hs.contains (i, j)
  deg : DegOK col cells.D
  iv : IvOK col cells.D o.tight
  chan : o.channel = true → ChanOK col cells.D
  bud : o.budget = true → BudOK col cells.D
  capR : o.baseCodegree = true → CapC col 1 7
  capB : o.baseCodegree = true → CapC col 2 4
  wcellsIn : ∀ c ∈ cells.wcells, 1 ≤ c.1 ∧ c.2.1 ≤ 22
  wlex : ∀ c ∈ cells.wcells, ∀ v, c.1 ≤ v → v < c.2.1 → LexLeE col (swapF v (v + 1))
  wall : o.wallpairs = true → ∀ c ∈ cells.wcells, ∀ p q, c.1 ≤ p → p < q → q ≤ c.2.1 →
    LexLeE col (swapF p q)
  ncellsIn : ∀ v ∈ cellVerts (nCellArrays cells), 1 ≤ v ∧ v ≤ 22
  ncellsNodup : (cellVerts (nCellArrays cells)).Nodup
  auth : o.auth = true → ∀ asg ∈ autos (nCellArrays cells) Hs, LexLeE col (imgA asg)
  noShortfall : o.shortfall = false

theorem CoreCanonL.toCoreCanon {col : Nat → Nat → Bool} {k : Nat} {cells : Cells}
    {Hs : Array (Nat × Nat)} {o : Opts} (h : CoreCanonL col k cells Hs o) : CoreCanon col k cells Hs o :=
  { symm := h.symm, row1 := h.row1, hunits := h.hunits, deg := h.deg, iv := h.iv, chan := h.chan,
    bud := h.bud, capR := h.capR, capB := h.capB, wcellsIn := h.wcellsIn,
    wlex := fun c hc v h1 h2 => by
      rw [movedPairs_eq_gPairs]; exact lexOK_gPairs col _ (h.wlex c hc v h1 h2)
    wall := fun hw c hc p q h1 h2 h3 => by
      have hin := h.wcellsIn c hc
      exact lexOK_wallPairs col h.symm (by omega) h2 (by omega) (h.wall hw c hc p q h1 h2 h3)
    ncellsIn := h.ncellsIn, ncellsNodup := h.ncellsNodup,
    auth := fun ha asg hasg => by
      rw [authPairs_eq_gPairs]; exact lexOK_gPairs col _ (h.auth ha asg hasg)
    noShortfall := h.noShortfall }

/-- **The core bridge**, with first-difference premises. -/
theorem rootedFormula_sat_coreL (degs : List Nat) (k : Nat) (comp H : List (Nat × Nat)) (o : Opts)
    (F : Formula) (hF : rootedFormula 22 ["K2x8", "K2x5"] degs k comp H o = .ok F)
    (cells : Cells) (hcells : cellsOf 22 degs k comp = .ok cells)
    (col : Nat → Nat → Bool) (hc : CoreCanonL col k cells (normH H) o) :
    ∃ σ, ClsSat σ F.clauses :=
  rootedFormula_sat_core degs k comp H o F hF cells hcells col hc.toCoreCanon

end SB.Rooted

#print axioms SB.Rooted.rootedFormula_sat_coreL
