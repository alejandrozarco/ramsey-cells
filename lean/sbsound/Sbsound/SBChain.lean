/-
Row-1 colour-chain lemma (the CNF chain clauses, adjacent pair step).

`row1Ind a c` is the Boolean indicator of colour `c` along the row-1 edges
(edges whose first endpoint is vertex 0), indexed by the row-1 edge subtype
with its inherited linear order. If `a` is lex-led by its image under the
colour transposition `swap c c'` with `c < c'`, then the indicator of `c`
dominates the indicator of `c'` lexicographically:
`toLex (row1Ind a c') ≤ toLex (row1Ind a c)`.

Proof shape: otherwise there is a first row-1 index where the indicators
differ, with the `c`-indicator false and the `c'`-indicator true there, so
that edge carries colour `c'`. Earlier row-1 edges carry neither `c` nor
`c'` (agreeing indicators cannot both be true), and every edge below a
row-1 edge in the Edge order is itself row-1, so `swap c c'` fixes `a` on
all edges strictly below that one and strictly decreases it there —
contradicting leaderhood.
-/
import Mathlib
import Sbsound.SBCore
import Sbsound.SBGraph
import Sbsound.SBKeystone

namespace SB

variable {n r : ℕ}

/-- Row-1 edges: edges whose first endpoint is vertex `0` (stated on `Fin.val`
to avoid a `NeZero` hypothesis). As a subtype of `Edge n` it inherits the
row-major linear order. -/
abbrev Row1 (n : ℕ) := {e : Edge n // ((ofLex e.val).1 : ℕ) = 0}

/-- Boolean indicator of colour `c` on the row-1 edges. -/
def row1Ind (a : EColouring n r) (c : Fin r) : Row1 n → Bool :=
  fun j => decide (a j.val = c)

/-- Any edge strictly below a row-1 edge (in the row-major Edge order) is
itself a row-1 edge. -/
private lemma row1_of_lt_row1 {e e₀ : Edge n} (h0 : ((ofLex e₀.val).1 : ℕ) = 0)
    (hlt : e < e₀) : ((ofLex e.val).1 : ℕ) = 0 := by
  have hv : (e.val : Lex (Fin n × Fin n)) < e₀.val := Subtype.coe_lt_coe.mpr hlt
  rcases Prod.Lex.lt_iff.mp hv with hfst | ⟨hfst, -⟩
  · have := Fin.lt_def.mp hfst
    omega
  · rw [hfst]
    exact h0

/-- **Row-1 colour-chain lemma.** If `a` is a lex-leader relative to the
colour transposition `Equiv.swap c c'` with `c < c'`, then along row 1 the
indicator of `c'` is lexicographically at most the indicator of `c` — the
chain clause the CNF emits for adjacent colour pairs. -/
theorem chain_of_leader (a : EColouring n r) (c c' : Fin r)
    (hcc : c < c')
    (hlead : lexView a ≤ lexView (actC (Equiv.swap c c') a)) :
    toLex (row1Ind a c') ≤ toLex (row1Ind a c) := by
  by_contra hcon
  -- By totality, the c-indicator is lex-below the c'-indicator: there is a
  -- first row-1 index j₀ where they differ (this is `Pi.Lex` unfolded).
  have hfirst : ∃ j₀ : Row1 n,
      (∀ j, j < j₀ → row1Ind a c j = row1Ind a c' j) ∧
        row1Ind a c j₀ < row1Ind a c' j₀ :=
    not_le.mp hcon
  obtain ⟨j₀, hbelow, hj₀⟩ := hfirst
  -- At j₀ the c-indicator is false and the c'-indicator true: colour is c'.
  obtain ⟨-, htrue⟩ := Bool.lt_iff.mp hj₀
  have ha : a j₀.val = c' := of_decide_eq_true htrue
  -- The swap strictly decreases `a` in the full edge-lex order, first
  -- difference at the edge j₀.val.
  have hswap : ∃ e₀ : Edge n,
      (∀ e, e < e₀ → actC (Equiv.swap c c') a e = a e) ∧
        actC (Equiv.swap c c') a e₀ < a e₀ := by
    refine ⟨j₀.val, ?_, ?_⟩
    · intro e he
      -- e is below a row-1 edge, hence row-1 itself, with smaller index.
      have he0 : ((ofLex e.val).1 : ℕ) = 0 := row1_of_lt_row1 j₀.prop he
      have hagree : decide (a e = c) = decide (a e = c') :=
        hbelow ⟨e, he0⟩ (Subtype.coe_lt_coe.mp he)
      -- Agreeing indicators cannot both be true, so both are false.
      have hne_c : a e ≠ c := by
        intro hc
        have h' : a e = c' := of_decide_eq_true (by rw [← hagree]; simp [hc])
        exact hcc.ne (hc.symm.trans h')
      have hne_c' : a e ≠ c' := by
        intro hc'
        exact hne_c (of_decide_eq_true (by rw [hagree]; simp [hc']))
      change Equiv.swap c c' (a e) = a e
      exact Equiv.swap_apply_of_ne_of_ne hne_c hne_c'
    · change Equiv.swap c c' (a j₀.val) < a j₀.val
      rw [ha, Equiv.swap_apply_right]
      exact hcc
  -- Package as a lex-order strict inequality and contradict leaderhood.
  have hlt : lexView (actC (Equiv.swap c c') a) < lexView a := hswap
  exact absurd hlead (not_le.mpr hlt)

end SB
