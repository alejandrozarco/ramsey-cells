/-
DOL clause layer, part 2: the emitted clause families and their satisfaction by a DOL leader.

Families (all over `DVar (n+1) r`, vertices `0..n`, `m = n` inputs per vertex, indices 0-based):
* `counterClauses c v`  — gen_variant.degree_unaries for vertex `v` (BiCounter, registers `dreg v i j`);
* `orderClauses c`      — `o[v+1][k] → o[v][k]` with `o[v][k] = dreg v (n-1) k`;
* `eqDiffClauses v`     — `diff v k → o[v][k]`, `diff v k → ¬o[v+1][k]`, `eqv v ∨ ⋁_k diff v k`;
* `gatedLexClauses`     — the deposited per-transposition family with `¬eqv v` prepended to every
                          comparison clause (definitional `q`/chain clauses unchanged).
Canonical assignment: deposited variables from `canonAssign a []`, registers truthful (BiCounter),
`eqv` truthful, `diff v k` = (k+1 ≤ deg v ∧ ¬ k+1 ≤ deg (v+1)).
Main theorem `dol_clauses_satisfiable_of_leader`: for `a` with antitone colour-`c` degrees and the
conditional-lex leader property, the canonical assignment satisfies every family.
-/
import Mathlib
import Sbsound.SBClauses
import Sbsound.SBDegree
import Sbsound.BiCounter
import Sbsound.SBDegreeVars

namespace SB

variable {n r : ℕ}

/-! ### Inputs as literals -/

/-- The colour-`c` edge variable from `v` to its `i`-th other vertex. -/
def inVar (c : Fin r) (v : Fin (n + 1)) (i : Fin n) : DVar (n + 1) r :=
  Sum.inl (evar (mkEdge v (v.succAbove i) (Fin.succAbove_ne v i).symm) c)

/-- Register `dreg v i j`. -/
def reg (v : Fin (n + 1)) (i j : ℕ) : DVar (n + 1) r := dregvar v.val i j

/-! ### Degree counter clauses (gen_variant.degree_unaries, 0-based) -/

/-- Clauses at position `i` (0-based), level `j ≤ i`. -/
def counterCell (c : Fin r) (v : Fin (n + 1)) (i j : ℕ) : List (DClause (n + 1) r) :=
  if hi : i < n then
    let x : DVar (n + 1) r := inVar c v ⟨i, hi⟩
    match i with
    | 0 => [[dneg (reg v 0 0), dpos x], [dneg x, dpos (reg v 0 0)]]
    | i' + 1 =>
      -- (a) s_ij → s_{i-1,j} ∨ x_i  (prev exists iff j ≤ i')
      (if j ≤ i' then [[dneg (reg v (i'+1) j), dpos (reg v i' j), dpos x]]
       else [[dneg (reg v (i'+1) j), dpos x]]) ++
      -- (b) s_ij → s_{i-1,j} ∨ s_{i-1,j-1}  (j ≥ 1)
      (if hj : 0 < j then
        (if j ≤ i' then [[dneg (reg v (i'+1) j), dpos (reg v i' j), dpos (reg v i' (j-1))]]
         else [[dneg (reg v (i'+1) j), dpos (reg v i' (j-1))]])
       else []) ++
      -- (c) s_{i-1,j} → s_ij  (j ≤ i')
      (if j ≤ i' then [[dneg (reg v i' j), dpos (reg v (i'+1) j)]] else []) ++
      -- (d) x_i ∧ s_{i-1,j-1} → s_ij ; x_i → s_i0
      (if 0 < j then [[dneg x, dneg (reg v i' (j-1)), dpos (reg v (i'+1) j)]]
       else [[dneg x, dpos (reg v (i'+1) 0)]])
  else []

/-- All counter clauses of vertex `v`: positions `i < n`, levels `j ≤ i`. -/
def counterClauses (c : Fin r) (v : Fin (n + 1)) : List (DClause (n + 1) r) :=
  (List.range n).flatMap fun i => (List.range (i + 1)).flatMap fun j => counterCell c v i j

/-! ### Ordering and gate clauses -/

/-- `o[v+1][k] → o[v][k]` for adjacent `v`, all levels `k < n` (needs `0 < n` for a last row). -/
def orderClauses (c : Fin r) : List (DClause (n + 1) r) :=
  (List.range n).flatMap fun v =>
    if hv : v + 1 < n + 1 then
      (List.range n).map fun k =>
        [dneg (reg (⟨v + 1, hv⟩ : Fin (n + 1)) (n - 1) k), dpos (reg ⟨v, by omega⟩ (n - 1) k)]
    else []

/-- The gate of transposition `v`: `diff → o[v]`, `diff → ¬o[v+1]`, `eqv ∨ ⋁ diff`. -/
def eqDiffClauses (v : ℕ) : List (DClause (n + 1) r) :=
  if hv : v + 1 < n + 1 then
    ((List.range n).flatMap fun k =>
      [[dneg (diffvar v k), dpos (reg (⟨v, by omega⟩ : Fin (n + 1)) (n - 1) k)],
       [dneg (diffvar v k), dneg (reg (⟨v + 1, hv⟩ : Fin (n + 1)) (n - 1) k)]]) ++
    [dpos (eqvvar v) :: (List.range n).map fun k => dpos (diffvar v k)]
  else []

def gateClauses : List (DClause (n + 1) r) := (List.range n).flatMap eqDiffClauses

/-! ### Gated lex clauses -/

/-- Comparison clauses at moved-position `t` with `¬eqv v` prepended. -/
def gatedCmpClauses (v t : ℕ) (e f : Edge (n + 1)) : List (DClause (n + 1) r) :=
  (vlexCmpClauses v t e f).map fun C => dneg (eqvvar v) :: liftD C

def gatedTranspositionClauses (τ : Equiv.Perm (Fin (n + 1))) (v : ℕ) :
    List (DClause (n + 1) r) :=
  (List.finRange (movedList τ).length).flatMap fun t =>
    gatedCmpClauses v t.val ((movedList τ)[t.val]'t.isLt)
        (permEdge τ ((movedList τ)[t.val]'t.isLt)) ++
      if t.val + 1 < (movedList τ).length then
        (vlexQClauses v t.val ((movedList τ)[t.val]'t.isLt)
            (permEdge τ ((movedList τ)[t.val]'t.isLt))).map liftD ++
          (vlexChClauses v t.val).map liftD
      else []

def gatedLexClauses : List (DClause (n + 1) r) :=
  (List.range n).flatMap fun v =>
    if h : v + 1 < n + 1 then gatedTranspositionClauses (vswap (n + 1) v h) v else []

/-- The whole DOL family for ordering colour `c`. -/
def dolClauses (c : Fin r) : List (DClause (n + 1) r) :=
  ((List.finRange (n + 1)).flatMap fun v => counterClauses c v) ++
    orderClauses c ++ gateClauses ++ gatedLexClauses

/-! ### The canonical assignment -/

open Classical in
noncomputable def canonD (a : EColouring (n + 1) r) (c : Fin r) : DAssign (n + 1) r
  | Sum.inl x => canonAssign a [] x
  | Sum.inr (DAux.dreg v i j) =>
    if hv : v < n + 1 then
      if hi : i < n then
        if hj : j < n then BiCounter.truthful (degInputs a c ⟨v, hv⟩) ⟨i, hi⟩ ⟨j, hj⟩
        else true
      else true
    else true
  | Sum.inr (DAux.eqv v) =>
    if hv : v + 1 < n + 1 then decide (deg a c ⟨v, by omega⟩ = deg a c ⟨v + 1, hv⟩) else true
  | Sum.inr (DAux.diff v k) =>
    if hv : v + 1 < n + 1 then
      decide (k + 1 ≤ deg a c ⟨v, by omega⟩ ∧ ¬ k + 1 ≤ deg a c ⟨v + 1, hv⟩)
    else false

lemma canonD_inl (a : EColouring (n + 1) r) (c : Fin r) (x : SVar (n + 1) r) :
    canonD a c (Sum.inl x) = canonAssign a [] x := rfl

lemma canonD_evar (a : EColouring (n + 1) r) (c : Fin r) (e : Edge (n + 1)) (c' : Fin r) :
    canonD a c (Sum.inl (evar e c')) = decide (a e = c') := rfl

lemma canonD_reg (a : EColouring (n + 1) r) (c : Fin r) (v : Fin (n + 1)) (i j : Fin n) :
    canonD a c (reg v i.val j.val) = BiCounter.truthful (degInputs a c v) i j := by
  simp [canonD, reg, dregvar, v.isLt, i.isLt, j.isLt]

lemma canonD_eqv (a : EColouring (n + 1) r) (c : Fin r) (v : ℕ) (hv : v + 1 < n + 1) :
    canonD a c (eqvvar v) = decide (deg a c ⟨v, by omega⟩ = deg a c ⟨v + 1, hv⟩) := by
  simp [canonD, eqvvar, hv]

lemma canonD_diff (a : EColouring (n + 1) r) (c : Fin r) (v k : ℕ) (hv : v + 1 < n + 1) :
    canonD a c (diffvar v k) =
      decide (k + 1 ≤ deg a c ⟨v, by omega⟩ ∧ ¬ k + 1 ≤ deg a c ⟨v + 1, hv⟩) := by
  simp [canonD, diffvar, hv]

/-- The input literal evaluates to the input vector. -/
lemma canonD_inVar (a : EColouring (n + 1) r) (c : Fin r) (v : Fin (n + 1)) (i : Fin n) :
    canonD a c (inVar c v i) = degInputs a c v i := by
  classical
  simp only [inVar, canonD_evar, degInputs]
  have hne : v ≠ v.succAbove i := (Fin.succAbove_ne v i).symm
  rw [colourGraph_adj]
  simp only [colourRel]
  congr 1
  exact propext ⟨fun h => ⟨hne, h⟩, fun ⟨_, h⟩ => h⟩

/-! ### Literal evaluation shorthands -/

@[simp] lemma evalDLit_dpos (β : DAssign n r) (x : DVar n r) : evalDLit β (dpos x) = β x := rfl
@[simp] lemma evalDLit_dneg (β : DAssign n r) (x : DVar n r) : evalDLit β (dneg x) = !β x := rfl

lemma satDClause_cons_of_tail {β : DAssign n r} {l : DLit n r} {C : DClause n r}
    (h : satDClause β C = true) : satDClause β (l :: C) = true := by
  unfold satDClause at h ⊢; simp only [List.any_cons, h, Bool.or_true]

lemma canonD_reg' (a : EColouring (n + 1) r) (c : Fin r) (v : Fin (n + 1)) {i j : ℕ}
    (hi : i < n) (hj : j < n) :
    canonD a c (reg v i j) = BiCounter.truthful (degInputs a c v) ⟨i, hi⟩ ⟨j, hj⟩ :=
  canonD_reg a c v ⟨i, hi⟩ ⟨j, hj⟩

lemma deg_le (a : EColouring (n + 1) r) (c : Fin r) (v : Fin (n + 1)) : deg a c v ≤ n := by
  rw [← card_degInputs a c v]
  exact le_trans (Finset.card_filter_le _ _) (by simp)

/-! ### Counter clauses -/

theorem sat_counterClauses (a : EColouring (n + 1) r) (c : Fin r) (v : Fin (n + 1)) :
    satDCNF (canonD a c) (counterClauses c v) := by
  intro C hC
  simp only [counterClauses, List.mem_flatMap, List.mem_range] at hC
  obtain ⟨i, hi, j, hj, hC⟩ := hC
  have hjn : j < n := by omega
  have hcl := BiCounter.truthful_satisfies (degInputs a c v)
  obtain ⟨cA, cAA, cB, cBB, cC, cD, cDD⟩ := hcl
  set y := degInputs a c v with hy
  set R := BiCounter.truthful y with hR
  -- register and input evaluations
  have hreg : ∀ (i' j' : ℕ) (hi' : i' < n) (hj' : j' < n),
      canonD a c (reg v i' j') = R ⟨i', hi'⟩ ⟨j', hj'⟩ := fun i' j' hi' hj' => canonD_reg' a c v hi' hj'
  have hin : ∀ (i' : ℕ) (hi' : i' < n), canonD a c (inVar c v ⟨i', hi'⟩) = y ⟨i', hi'⟩ :=
    fun i' hi' => canonD_inVar a c v ⟨i', hi'⟩
  simp only [counterCell, dif_pos hi] at hC
  cases i with
  | zero =>
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · -- s_00 → x_0
      by_cases hs : canonD a c (reg v 0 0) = true
      · refine satDClause_of_mem (l := dpos (inVar c v ⟨0, hi⟩)) (by simp) ?_
        rw [evalDLit_dpos, hin 0 hi]
        rw [hreg 0 0 hi hi] at hs
        exact cAA ⟨0, hi⟩ hs
      · exact satDClause_of_mem (l := dneg (reg v 0 0)) (by simp) (by simp [hs])
    · -- x_0 → s_00
      by_cases hx : canonD a c (inVar c v ⟨0, hi⟩) = true
      · refine satDClause_of_mem (l := dpos (reg v 0 0)) (by simp) ?_
        rw [evalDLit_dpos, hreg 0 0 hi hi]
        rw [hin 0 hi] at hx
        exact cDD ⟨0, hi⟩ (by omega) hx
      · exact satDClause_of_mem (l := dneg (inVar c v ⟨0, hi⟩)) (by simp) (by simp [hx])
  | succ i' =>
    have hi' : i' < n := by omega
    have hi1 : (⟨i', hi'⟩ : Fin n).val + 1 < n := by simp; omega
    simp only [List.mem_append] at hC
    rcases hC with ((hA | hB) | hCc) | hD
    · -- group (a)
      by_cases hle : j ≤ i'
      · rw [if_pos hle] at hA
        simp only [List.mem_singleton] at hA; subst hA
        by_cases hs : canonD a c (reg v (i' + 1) j) = true
        · rw [hreg (i'+1) j hi hjn] at hs
          rcases cA ⟨i', hi'⟩ hi1 ⟨j, hjn⟩ hle hs with h1 | h2
          · exact satDClause_of_mem (l := dpos (reg v i' j)) (by simp) (by rw [evalDLit_dpos, hreg i' j hi' hjn]; exact h1)
          · exact satDClause_of_mem (l := dpos (inVar c v ⟨i'+1, hi⟩)) (by simp) (by rw [evalDLit_dpos, hin (i'+1) hi]; exact h2)
        · exact satDClause_of_mem (l := dneg (reg v (i'+1) j)) (by simp) (by simp [hs])
      · rw [if_neg hle] at hA
        simp only [List.mem_singleton] at hA; subst hA
        have hji : j = i' + 1 := by omega
        by_cases hs : canonD a c (reg v (i' + 1) j) = true
        · rw [hreg (i'+1) j hi hjn] at hs
          refine satDClause_of_mem (l := dpos (inVar c v ⟨i'+1, hi⟩)) (by simp) ?_
          rw [evalDLit_dpos, hin (i'+1) hi]
          have : (⟨j, hjn⟩ : Fin n) = ⟨i'+1, hi⟩ := Fin.ext hji
          rw [this] at hs
          exact cAA ⟨i'+1, hi⟩ hs
        · exact satDClause_of_mem (l := dneg (reg v (i'+1) j)) (by simp) (by simp [hs])
    · -- group (b)
      by_cases hj0 : 0 < j
      · rw [dif_pos hj0] at hB
        by_cases hle : j ≤ i'
        · rw [if_pos hle] at hB
          simp only [List.mem_singleton] at hB; subst hB
          by_cases hs : canonD a c (reg v (i' + 1) j) = true
          · rw [hreg (i'+1) j hi hjn] at hs
            rcases cB ⟨i', hi'⟩ hi1 ⟨j, hjn⟩ hj0 hle hs with h1 | h2
            · exact satDClause_of_mem (l := dpos (reg v i' j)) (by simp) (by rw [evalDLit_dpos, hreg i' j hi' hjn]; exact h1)
            · exact satDClause_of_mem (l := dpos (reg v i' (j-1))) (by simp) (by rw [evalDLit_dpos, hreg i' (j-1) hi' (by omega)]; exact h2)
          · exact satDClause_of_mem (l := dneg (reg v (i'+1) j)) (by simp) (by simp [hs])
        · rw [if_neg hle] at hB
          simp only [List.mem_singleton] at hB; subst hB
          have hji : j = i' + 1 := by omega
          by_cases hs : canonD a c (reg v (i' + 1) j) = true
          · rw [hreg (i'+1) j hi hjn] at hs
            have : (⟨j, hjn⟩ : Fin n) = ⟨i'+1, hi⟩ := Fin.ext hji
            rw [this] at hs
            have h2 := cBB ⟨i', hi'⟩ hi1 hs
            refine satDClause_of_mem (l := dpos (reg v i' (j-1))) (by simp) ?_
            rw [evalDLit_dpos, hreg i' (j-1) hi' (by omega)]
            have : (⟨j - 1, by omega⟩ : Fin n) = ⟨i', hi'⟩ := Fin.ext (by simp; omega)
            rw [this]; exact h2
          · exact satDClause_of_mem (l := dneg (reg v (i'+1) j)) (by simp) (by simp [hs])
      · rw [dif_neg hj0] at hB
        exact absurd hB List.not_mem_nil
    · -- group (c)
      by_cases hle : j ≤ i'
      · rw [if_pos hle] at hCc
        simp only [List.mem_singleton] at hCc; subst hCc
        by_cases hs : canonD a c (reg v i' j) = true
        · rw [hreg i' j hi' hjn] at hs
          refine satDClause_of_mem (l := dpos (reg v (i'+1) j)) (by simp) ?_
          rw [evalDLit_dpos, hreg (i'+1) j hi hjn]
          exact cC ⟨i', hi'⟩ hi1 ⟨j, hjn⟩ hle hs
        · exact satDClause_of_mem (l := dneg (reg v i' j)) (by simp) (by simp [hs])
      · rw [if_neg hle] at hCc
        exact absurd hCc List.not_mem_nil
    · -- group (d)
      by_cases hj0 : 0 < j
      · rw [if_pos hj0] at hD
        simp only [List.mem_singleton] at hD; subst hD
        by_cases hx : canonD a c (inVar c v ⟨i'+1, hi⟩) = true
        · by_cases hs : canonD a c (reg v i' (j-1)) = true
          · refine satDClause_of_mem (l := dpos (reg v (i'+1) j)) (by simp) ?_
            rw [evalDLit_dpos, hreg (i'+1) j hi hjn]
            rw [hin (i'+1) hi] at hx
            rw [hreg i' (j-1) hi' (by omega)] at hs
            exact cD ⟨i', hi'⟩ hi1 ⟨j, hjn⟩ hj0 (by simp; omega) hx hs
          · exact satDClause_of_mem (l := dneg (reg v i' (j-1))) (by simp) (by simp [hs])
        · exact satDClause_of_mem (l := dneg (inVar c v ⟨i'+1, hi⟩)) (by simp) (by simp [hx])
      · rw [if_neg hj0] at hD
        simp only [List.mem_singleton] at hD; subst hD
        have hj00 : j = 0 := by omega
        subst hj00
        by_cases hx : canonD a c (inVar c v ⟨i'+1, hi⟩) = true
        · refine satDClause_of_mem (l := dpos (reg v (i'+1) 0)) (by simp) ?_
          rw [evalDLit_dpos, hreg (i'+1) 0 hi (by omega)]
          rw [hin (i'+1) hi] at hx
          exact cDD ⟨i'+1, hi⟩ (by omega) hx
        · exact satDClause_of_mem (l := dneg (inVar c v ⟨i'+1, hi⟩)) (by simp) (by simp [hx])

/-! ### Ordering and gate clauses -/

lemma canonD_last (a : EColouring (n + 1) r) (c : Fin r) (v : Fin (n + 1)) (h0 : 0 < n)
    {k : ℕ} (hk : k < n) :
    canonD a c (reg v (n - 1) k) = decide (k + 1 ≤ deg a c v) := by
  rw [canonD_reg' a c v (by omega) hk, truthful_last_eq_dout a c v h0 ⟨k, hk⟩]; rfl

theorem sat_orderClauses (a : EColouring (n + 1) r) (c : Fin r) (hA : Antitone (deg a c)) :
    satDCNF (canonD a c) (orderClauses c) := by
  intro C hC
  simp only [orderClauses, List.mem_flatMap, List.mem_range] at hC
  obtain ⟨v, hv, hC⟩ := hC
  have hv1 : v + 1 < n + 1 := by omega
  rw [dif_pos hv1] at hC
  simp only [List.mem_map, List.mem_range] at hC
  obtain ⟨k, hk, rfl⟩ := hC
  have h0 : 0 < n := by omega
  by_cases hs : canonD a c (reg (⟨v + 1, hv1⟩ : Fin (n + 1)) (n - 1) k) = true
  · refine satDClause_of_mem (l := dpos (reg (⟨v, by omega⟩ : Fin (n + 1)) (n - 1) k)) (by simp) ?_
    rw [evalDLit_dpos, canonD_last a c _ h0 hk]
    rw [canonD_last a c _ h0 hk, decide_eq_true_eq] at hs
    have hle : deg a c ⟨v + 1, hv1⟩ ≤ deg a c ⟨v, by omega⟩ := hA (Fin.mk_le_mk.mpr (Nat.le_succ v))
    exact decide_eq_true (le_trans hs hle)
  · exact satDClause_of_mem (l := dneg (reg (⟨v + 1, hv1⟩ : Fin (n + 1)) (n - 1) k)) (by simp) (by simp [hs])

theorem sat_gateClauses (a : EColouring (n + 1) r) (c : Fin r) (hA : Antitone (deg a c)) :
    satDCNF (canonD a c) gateClauses := by
  intro C hC
  simp only [gateClauses, List.mem_flatMap, List.mem_range] at hC
  obtain ⟨v, hv, hC⟩ := hC
  have hv1 : v + 1 < n + 1 := by omega
  have h0 : 0 < n := by omega
  simp only [eqDiffClauses, dif_pos hv1, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hC
  rcases hC with ⟨k, hk, rfl | rfl⟩ | rfl
  · -- diff → o[v][k]
    by_cases hd : canonD a c (diffvar v k) = true
    · refine satDClause_of_mem (l := dpos (reg (⟨v, by omega⟩ : Fin (n + 1)) (n - 1) k)) (by simp) ?_
      rw [evalDLit_dpos, canonD_last a c _ h0 hk]
      rw [canonD_diff a c v k hv1, decide_eq_true_eq] at hd
      exact decide_eq_true hd.1
    · exact satDClause_of_mem (l := dneg (diffvar v k)) (by simp) (by simp [hd])
  · -- diff → ¬o[v+1][k]
    by_cases hd : canonD a c (diffvar v k) = true
    · refine satDClause_of_mem (l := dneg (reg (⟨v + 1, hv1⟩ : Fin (n + 1)) (n - 1) k)) (by simp) ?_
      rw [evalDLit_dneg, canonD_last a c _ h0 hk]
      rw [canonD_diff a c v k hv1, decide_eq_true_eq] at hd
      simp [hd.2]
    · exact satDClause_of_mem (l := dneg (diffvar v k)) (by simp) (by simp [hd])
  · -- eqv ∨ ⋁ diff
    by_cases heq : deg a c ⟨v, by omega⟩ = deg a c ⟨v + 1, hv1⟩
    · refine satDClause_of_mem (l := dpos (eqvvar v)) (by simp) ?_
      rw [evalDLit_dpos, canonD_eqv a c v hv1]; exact decide_eq_true heq
    · have hle : deg a c ⟨v + 1, hv1⟩ ≤ deg a c ⟨v, by omega⟩ := hA (Fin.mk_le_mk.mpr (Nat.le_succ v))
      have hlt : deg a c ⟨v + 1, hv1⟩ < deg a c ⟨v, by omega⟩ := lt_of_le_of_ne hle (Ne.symm heq)
      have hdle := deg_le a c ⟨v, by omega⟩
      refine satDClause_of_mem (l := dpos (diffvar v (deg a c ⟨v, by omega⟩ - 1))) ?_ ?_
      · simp only [List.mem_cons, List.mem_map, List.mem_range]
        exact Or.inr ⟨_, by omega, rfl⟩
      · rw [evalDLit_dpos, canonD_diff a c v _ hv1]
        exact decide_eq_true ⟨by omega, by omega⟩

/-! ### Gated lex clauses -/

theorem sat_gatedLexClauses (a : EColouring (n + 1) r) (c : Fin r)
    (hV : ∀ v (h : v + 1 < n + 1), deg a c ⟨v, by omega⟩ = deg a c ⟨v + 1, h⟩ →
      lexView a ≤ lexView (actV (vswap (n + 1) v h) a)) :
    satDCNF (canonD a c) gatedLexClauses := by
  intro C hC
  simp only [gatedLexClauses, List.mem_flatMap, List.mem_range] at hC
  obtain ⟨v, hv, hC⟩ := hC
  have h : v + 1 < n + 1 := by omega
  rw [dif_pos h] at hC
  set τ := vswap (n + 1) v h with hτ
  set β : SAssign (n + 1) r := canonD a c ∘ Sum.inl with hβ
  have hβe : ∀ e c', β (evar e c') = decide (a e = c') := fun e c' => rfl
  have hβq : ∀ t (ht : t < (movedList τ).length), β (qvar v t) =
      decide (a ((movedList τ)[t]'ht) = a (permEdge τ ((movedList τ)[t]'ht))) :=
    fun t ht => canonAssign_vq a [] h ht
  have hβch : ∀ s, β (chvar v s) =
      decide (∀ e ∈ (movedList τ).take (s + 1), a e = a (permEdge τ e)) :=
    canonAssign_vch a [] h
  simp only [gatedTranspositionClauses, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_append] at hC
  obtain ⟨t, hC⟩ := hC
  rcases hC with hcmp | hdef
  · -- gated comparison clause
    simp only [gatedCmpClauses, List.mem_map] at hcmp
    obtain ⟨C', hC', rfl⟩ := hcmp
    by_cases heq : canonD a c (eqvvar v) = true
    · rw [canonD_eqv a c v h, decide_eq_true_eq] at heq
      have hlead := hV v h heq
      have hsat : satSClause β C' = true :=
        sat_vlexCmp a τ v β hβe hβch hlead t.isLt hC'
      apply satDClause_cons_of_tail
      rw [satDClause_liftD]; exact hsat
    · exact satDClause_of_mem (l := dneg (eqvvar v)) (by simp) (by simp [heq])
  · -- definitional q / chain clauses (lifted)
    split_ifs at hdef with ht1
    · simp only [List.mem_append, List.mem_map] at hdef
      rcases hdef with ⟨C', hC', rfl⟩ | ⟨C', hC', rfl⟩
      · rw [satDClause_liftD]
        exact sat_vlexQ a τ v β hβe t.isLt (hβq t.val t.isLt) hC'
      · rw [satDClause_liftD]
        exact sat_vlexCh a τ v β ht1 (hβq t.val (Nat.lt_of_succ_lt ht1)) hβch hC'
    · exact absurd hdef List.not_mem_nil

/-! ### The deliverable of this layer -/

/-- **Satisfiability of the DOL families by a DOL leader.** -/
theorem dol_clauses_satisfiable_of_leader (a : EColouring (n + 1) r) (c : Fin r)
    (hA : Antitone (deg a c))
    (hV : ∀ v (h : v + 1 < n + 1), deg a c ⟨v, by omega⟩ = deg a c ⟨v + 1, h⟩ →
      lexView a ≤ lexView (actV (vswap (n + 1) v h) a)) :
    ∃ β : DAssign (n + 1) r, (∀ e c', β (Sum.inl (evar e c')) = decide (a e = c')) ∧
      satDCNF β (dolClauses c) := by
  refine ⟨canonD a c, fun e c' => rfl, ?_⟩
  simp only [dolClauses, satDCNF_append]
  refine ⟨⟨⟨?_, sat_orderClauses a c hA⟩, sat_gateClauses a c hA⟩, sat_gatedLexClauses a c hV⟩
  intro C hC
  simp only [List.mem_flatMap, List.mem_finRange, true_and] at hC
  obtain ⟨v, hC⟩ := hC
  exact sat_counterClauses a c v C hC

/-- **DOL encode soundness.** If some colouring avoids the forbidden bipartite patterns, then some
colouring avoids them, has truthful codegree counters, and admits an assignment satisfying every
DOL clause (degree counters, ordering, gate, gated lex) while agreeing with it on the edge variables.
Contrapositive: refuting base + codegree + DOL refutes the existence of a colouring. -/
theorem dol_encode_sound {st : Fin r → ℕ × ℕ} (hst : ∀ c, 2 ≤ (st c).2) (c : Fin r)
    (hsat : ∃ a : EColouring (n + 1) r, NoKstFam a st) :
    ∃ a : EColouring (n + 1) r, NoKstFam a st ∧
      (∀ c' : Fin r, ∀ S ∈ Finset.powersetCard (st c').1 (Finset.univ : Finset (Fin (n + 1))),
        Sinz.Clauses (codegreeInputs a c' S)
          (Sinz.truthful (k := (st c').2 - 1) (codegreeInputs a c' S))) ∧
      ∃ β : DAssign (n + 1) r, (∀ e c', β (Sum.inl (evar e c')) = decide (a e = c')) ∧
        satDCNF β (dolClauses c) := by
  obtain ⟨a, hgood, hA, hlead⟩ := exists_dol_leader c hsat
  refine ⟨a, hgood, ?_, ?_⟩
  · intro c' S hS
    exact codegree_clauses_of_noKst a c' (hst c') (hgood c') S hS
  · refine dol_clauses_satisfiable_of_leader a c hA ?_
    intro v h hdeg
    exact hlead ⟨v, by omega⟩ h hdeg

end SB

#print axioms SB.sat_counterClauses
#print axioms SB.dol_clauses_satisfiable_of_leader
#print axioms SB.dol_encode_sound
