/-
**The encode step, for every bipartite cell the campaign works on.**

`EncodeSound.encode_sound` is general in the number of vertices `n`, the number
of colours `r`, and the forbidden family `st : Fin r → ℕ × ℕ`. It was stated for
`R(K_{3,4}, K_{3,3})` only because that is the cell whose CNF had been refuted.
Nothing in the proof knows that.

So the encode step is not one result. It is one result per cell of the
campaign's bipartite portfolio, and it costs a line each. This file discharges
all thirteen `K_{s,t}` cells in `runs/target_registry.json`, plus a
three-colour instance to show the argument never assumed two colours.

Each corollary is stated for ALL `n`, not for the particular `n` its cell was
searched at: the soundness of the encoding does not depend on where the search
happened to be run, and stating it that way keeps the theorem usable when a
cell moves to a new `n`.
-/
import Mathlib
import Sbsound.EncodeSound
import Sbsound.SBDegreeClauses

namespace SB.Portfolio

open SB

variable {n : ℕ}

/-! ### The two-colour bipartite statement

The pattern `K_{s,t}` is forbidden in colour 0 and `K_{s',t'}` in colour 1.
`gen_ramsey.py` emits, per colour, one Sinz counter per `s`-set bounding its
common neighbourhood by `t - 1`. -/

/-- The encode-soundness conclusion for a two-colour bipartite cell: from a
colouring avoiding both patterns, one that avoids them, is a lex-leader, and
has satisfiable codegree counters at the emitted bounds `t₀-1`, `t₁-1`. -/
def EncodeSoundFor (n s₀ t₀ s₁ t₁ : ℕ) : Prop :=
  (∃ a : EColouring n 2, NoKst a 0 s₀ t₀ ∧ NoKst a 1 s₁ t₁) →
  ∃ a : EColouring n 2,
    (NoKst a 0 s₀ t₀ ∧ NoKst a 1 s₁ t₁) ∧
    (∀ τ : Equiv.Perm (Fin n), lexView a ≤ lexView (actV τ a)) ∧
    (∀ S ∈ Finset.powersetCard s₀ (Finset.univ : Finset (Fin n)),
      Sinz.Clauses (codegreeInputs a 0 S)
        (Sinz.truthful (k := t₀ - 1) (codegreeInputs a 0 S))) ∧
    (∀ S ∈ Finset.powersetCard s₁ (Finset.univ : Finset (Fin n)),
      Sinz.Clauses (codegreeInputs a 1 S)
        (Sinz.truthful (k := t₁ - 1) (codegreeInputs a 1 S)))

/-- **Encode soundness for any two-colour bipartite cell.** -/
theorem encode_sound_bip (s₀ t₀ s₁ t₁ : ℕ) (h₀ : 2 ≤ t₀) (h₁ : 2 ≤ t₁) :
    EncodeSoundFor n s₀ t₀ s₁ t₁ := by
  intro hsat
  have hfam : ∃ a : EColouring n 2, NoKstFam a ![(s₀, t₀), (s₁, t₁)] := by
    obtain ⟨a, hA, hB⟩ := hsat
    refine ⟨a, ?_⟩
    intro c; fin_cases c
    · simpa using hA
    · simpa using hB
  have hst : ∀ c : Fin 2, 2 ≤ ((![(s₀, t₀), (s₁, t₁)] : Fin 2 → ℕ × ℕ) c).2 := by
    intro c; fin_cases c
    · simpa using h₀
    · simpa using h₁
  obtain ⟨a, hgood, hlead, hcnt⟩ := encode_sound hst hfam
  refine ⟨a, ⟨?_, ?_⟩, hlead, ?_, ?_⟩
  · simpa using hgood 0
  · simpa using hgood 1
  · simpa using hcnt 0
  · simpa using hcnt 1

/-! ### The campaign's thirteen bipartite cells

Registry names on the left; `K2x10` is `K_{2,10}`. Every one is covered, for
every `n`, at one line each. -/

theorem sound_K2x10_K2x6 : EncodeSoundFor n 2 10 2 6  := encode_sound_bip 2 10 2 6  (by norm_num) (by norm_num)
theorem sound_K2x10_K2x7 : EncodeSoundFor n 2 10 2 7  := encode_sound_bip 2 10 2 7  (by norm_num) (by norm_num)
theorem sound_K2x11_K2x3 : EncodeSoundFor n 2 11 2 3  := encode_sound_bip 2 11 2 3  (by norm_num) (by norm_num)
theorem sound_K2x11_K2x4 : EncodeSoundFor n 2 11 2 4  := encode_sound_bip 2 11 2 4  (by norm_num) (by norm_num)
theorem sound_K2x11_K2x5 : EncodeSoundFor n 2 11 2 5  := encode_sound_bip 2 11 2 5  (by norm_num) (by norm_num)
theorem sound_K2x11_K2x6 : EncodeSoundFor n 2 11 2 6  := encode_sound_bip 2 11 2 6  (by norm_num) (by norm_num)
theorem sound_K2x2_K2x19 : EncodeSoundFor n 2 2  2 19 := encode_sound_bip 2 2  2 19 (by norm_num) (by norm_num)
theorem sound_K2x8_K2x5  : EncodeSoundFor n 2 8  2 5  := encode_sound_bip 2 8  2 5  (by norm_num) (by norm_num)
theorem sound_K3x4_K3x3  : EncodeSoundFor n 3 4  3 3  := encode_sound_bip 3 4  3 3  (by norm_num) (by norm_num)
theorem sound_K3x5_K2x4  : EncodeSoundFor n 3 5  2 4  := encode_sound_bip 3 5  2 4  (by norm_num) (by norm_num)
theorem sound_K3x5_K2x5  : EncodeSoundFor n 3 5  2 5  := encode_sound_bip 3 5  2 5  (by norm_num) (by norm_num)
theorem sound_K3x5_K3x3  : EncodeSoundFor n 3 5  3 3  := encode_sound_bip 3 5  3 3  (by norm_num) (by norm_num)
theorem sound_K3x5_K3x4  : EncodeSoundFor n 3 5  3 4  := encode_sound_bip 3 5  3 4  (by norm_num) (by norm_num)

/-! ### Three colours

Nothing in `encode_sound` assumed `r = 2`. The campaign has no three-colour
bipartite cell yet; when one is attempted, its encode step is already proved.
Here is the shape, for `K_{2,3}` forbidden in all three colours. -/

theorem sound_three_colour (s t : ℕ) (ht : 2 ≤ t)
    (hsat : ∃ a : EColouring n 3, ∀ c, NoKst a c s t) :
    ∃ a : EColouring n 3,
      (∀ c, NoKst a c s t) ∧
      (∀ τ : Equiv.Perm (Fin n), lexView a ≤ lexView (actV τ a)) ∧
      (∀ c : Fin 3, ∀ S ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)),
        Sinz.Clauses (codegreeInputs a c S)
          (Sinz.truthful (k := t - 1) (codegreeInputs a c S))) := by
  obtain ⟨a, hgood, hlead, hcnt⟩ :=
    encode_sound (st := fun _ : Fin 3 => (s, t)) (fun _ => ht) hsat
  exact ⟨a, hgood, hlead, hcnt⟩

/-! ### The payoff: refuting the broken space refutes everything

This is what makes the campaign's symmetry-broken CNF legitimate. The search
never explores all colourings — it explores only lex-leaders, which is a tiny
fraction (removing the break multiplied the measured search by ~459x). The
theorem below says that costs nothing: if no leader avoids the patterns, then
NO colouring does. Everything the search skipped was a relabelling of something
it looked at. -/

/-- **Refuting the leaders refutes the whole space.** Immediate from
`exists_noKstFam_leader`: any colouring avoiding the patterns would yield a
leader avoiding them. -/
theorem no_colouring_of_no_leader (s₀ t₀ s₁ t₁ : ℕ)
    (hno : ¬ ∃ a : EColouring n 2,
      (NoKst a 0 s₀ t₀ ∧ NoKst a 1 s₁ t₁) ∧
      (∀ τ : Equiv.Perm (Fin n), lexView a ≤ lexView (actV τ a))) :
    ¬ ∃ a : EColouring n 2, NoKst a 0 s₀ t₀ ∧ NoKst a 1 s₁ t₁ := by
  intro hsat
  refine hno ?_
  have hfam : ∃ a : EColouring n 2, NoKstFam a ![(s₀, t₀), (s₁, t₁)] := by
    obtain ⟨a, hA, hB⟩ := hsat
    refine ⟨a, ?_⟩
    intro c; fin_cases c
    · simpa using hA
    · simpa using hB
  obtain ⟨a, hgood, hlead⟩ := exists_noKstFam_leader hfam
  refine ⟨a, ⟨?_, ?_⟩, hlead⟩
  · simpa using hgood 0
  · simpa using hgood 1

/-- Same statement for an arbitrary number of colours and an arbitrary
forbidden family. -/
theorem no_colouring_of_no_leader_fam {r : ℕ} (st : Fin r → ℕ × ℕ)
    (hno : ¬ ∃ a : EColouring n r, NoKstFam a st ∧
      (∀ τ : Equiv.Perm (Fin n), lexView a ≤ lexView (actV τ a))) :
    ¬ ∃ a : EColouring n r, NoKstFam a st := by
  intro hsat
  obtain ⟨a, hgood, hlead⟩ := exists_noKstFam_leader hsat
  exact hno ⟨a, hgood, hlead⟩

/-! ### Beyond Ramsey: the counter half stands alone

`codegree_clauses_of_noKst` never mentions colourings — it says a set system
whose `s`-sets have small common neighbourhoods yields satisfiable Sinz
counters. Anything encoding a codegree bound this way inherits it: Zarankiewicz
problems `z(m,n;s,t)`, Turán-type degree bounds, cage problems. Recorded here
as the general statement rather than left implicit in the Ramsey file. -/

/-- The counter half, with no Ramsey content: an `s`-set with at most `k`
common colour-`c` neighbours has satisfiable counter clauses. -/
theorem counter_sound_of_bound (a : EColouring n 2) (c : Fin 2)
    (S : Finset (Fin n)) {k : ℕ} (hk : 0 < k)
    (hcard : (commonNbrs a c S).card ≤ k) :
    Sinz.Clauses (codegreeInputs a c S)
      (Sinz.truthful (k := k) (codegreeInputs a c S)) :=
  codegree_counter_sound a c S hk hcard


/-! ### Degree ordering + conditional lex (DOL) -/

/-- The DOL encode-soundness conclusion for a two-colour bipartite cell on `n+1` vertices:
from a colouring avoiding both patterns, one that avoids them, has truthful codegree counters,
and admits an assignment of the DOL clause families (degree counters, degree ordering, gate,
gated lex on colour 0) agreeing with it on the edge variables. -/
def DolEncodeSoundFor (n s₀ t₀ s₁ t₁ : ℕ) : Prop :=
  (∃ a : EColouring (n + 1) 2, NoKst a 0 s₀ t₀ ∧ NoKst a 1 s₁ t₁) →
  ∃ a : EColouring (n + 1) 2,
    (NoKst a 0 s₀ t₀ ∧ NoKst a 1 s₁ t₁) ∧
    (∀ S ∈ Finset.powersetCard s₀ (Finset.univ : Finset (Fin (n + 1))),
      Sinz.Clauses (codegreeInputs a 0 S)
        (Sinz.truthful (k := t₀ - 1) (codegreeInputs a 0 S))) ∧
    (∀ S ∈ Finset.powersetCard s₁ (Finset.univ : Finset (Fin (n + 1))),
      Sinz.Clauses (codegreeInputs a 1 S)
        (Sinz.truthful (k := t₁ - 1) (codegreeInputs a 1 S))) ∧
    ∃ β : DAssign (n + 1) 2, (∀ e c', β (Sum.inl (evar e c')) = decide (a e = c')) ∧
      satDCNF β (dolClauses (0 : Fin 2))

/-- **DOL encode soundness for any two-colour bipartite cell.** -/
theorem dol_encode_sound_bip (s₀ t₀ s₁ t₁ : ℕ) (h₀ : 2 ≤ t₀) (h₁ : 2 ≤ t₁) :
    DolEncodeSoundFor n s₀ t₀ s₁ t₁ := by
  intro hsat
  have hfam : ∃ a : EColouring (n + 1) 2, NoKstFam a ![(s₀, t₀), (s₁, t₁)] := by
    obtain ⟨a, hA, hB⟩ := hsat
    refine ⟨a, ?_⟩
    intro c; fin_cases c
    · simpa using hA
    · simpa using hB
  have hst : ∀ c : Fin 2, 2 ≤ ((![(s₀, t₀), (s₁, t₁)] : Fin 2 → ℕ × ℕ) c).2 := by
    intro c; fin_cases c
    · simpa using h₀
    · simpa using h₁
  obtain ⟨a, hgood, hcnt, hβ⟩ := dol_encode_sound hst (0 : Fin 2) hfam
  refine ⟨a, ⟨?_, ?_⟩, ?_, ?_, hβ⟩
  · simpa using hgood 0
  · simpa using hgood 1
  · simpa using hcnt 0
  · simpa using hcnt 1

theorem dol_sound_K2x8_K2x5 : DolEncodeSoundFor n 2 8 2 5 :=
  dol_encode_sound_bip 2 8 2 5 (by norm_num) (by norm_num)
theorem dol_sound_K3x5_K3x3 : DolEncodeSoundFor n 3 5 3 3 :=
  dol_encode_sound_bip 3 5 3 3 (by norm_num) (by norm_num)
theorem dol_sound_K2x11_K2x3 : DolEncodeSoundFor n 2 11 2 3 :=
  dol_encode_sound_bip 2 11 2 3 (by norm_num) (by norm_num)
theorem dol_sound_K2x11_K2x5 : DolEncodeSoundFor n 2 11 2 5 :=
  dol_encode_sound_bip 2 11 2 5 (by norm_num) (by norm_num)

/-- **Refuting the DOL leaders refutes the whole space** (two-colour, colour-0 ordering). -/
theorem no_colouring_of_no_dol_leader_bip (s₀ t₀ s₁ t₁ : ℕ)
    (hno : ¬ ∃ a : EColouring (n + 1) 2,
      (NoKst a 0 s₀ t₀ ∧ NoKst a 1 s₁ t₁) ∧ Antitone (deg a 0) ∧
      ∀ (i : Fin (n + 1)) (hi : i.val + 1 < n + 1), deg a 0 i = deg a 0 (succV i hi) →
        lexView a ≤ lexView (actV (Equiv.swap i (succV i hi)) a)) :
    ¬ ∃ a : EColouring (n + 1) 2, NoKst a 0 s₀ t₀ ∧ NoKst a 1 s₁ t₁ := by
  intro hsat
  have hfam : ∃ a : EColouring (n + 1) 2, NoKstFam a ![(s₀, t₀), (s₁, t₁)] := by
    obtain ⟨a, hA, hB⟩ := hsat
    refine ⟨a, ?_⟩
    intro c; fin_cases c
    · simpa using hA
    · simpa using hB
  obtain ⟨a, hgood, hA, hlead⟩ := exists_dol_leader (0 : Fin 2) hfam
  exact hno ⟨a, ⟨by simpa using hgood 0, by simpa using hgood 1⟩, hA, hlead⟩

#print axioms dol_encode_sound_bip
#print axioms dol_sound_K2x8_K2x5
#print axioms no_colouring_of_no_dol_leader_bip

end SB.Portfolio

#print axioms SB.Portfolio.encode_sound_bip
#print axioms SB.Portfolio.sound_K3x4_K3x3
#print axioms SB.Portfolio.sound_K2x2_K2x19
#print axioms SB.Portfolio.sound_three_colour
#print axioms SB.Portfolio.no_colouring_of_no_leader
#print axioms SB.Portfolio.no_colouring_of_no_leader_fam
