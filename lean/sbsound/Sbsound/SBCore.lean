/-
Static symmetry-breaking soundness — abstract core.

The whole campaign rests on one asserted step: adding lex-leader
symmetry-breaking clauses to the base CNF does not turn a satisfiable
formula unsatisfiable. This file proves the abstract heart of that step.

Reduction (why no group theory is needed): if the model set M of the base
formula is nonempty and CLOSED under each transformation σ we break on,
then the global minimum m of M (any linear order on the finite assignment
space) satisfies m ≤ σ m for every such σ — because σ m ∈ M and m is the
minimum of M. So every constraint of the form "a ≤ σ a" is satisfied by
some model, and conjoining those constraints preserves satisfiability.
Closure of M under σ (NOT the orbit structure) is the only obligation the
concrete instantiation has to discharge.
-/
import Mathlib

variable {A : Type*} [Fintype A] [LinearOrder A]

/-- **Lex-leader existence.** A nonempty model set closed under every
transformation in `T` contains an element `a` with `a ≤ σ a` for all
`σ ∈ T`. -/
theorem exists_sb_leader {M : Set A} (hne : M.Nonempty)
    {T : Set (A → A)} (hclosed : ∀ σ ∈ T, ∀ a ∈ M, σ a ∈ M) :
    ∃ a ∈ M, ∀ σ ∈ T, a ≤ σ a := by
  classical
  have hFne : M.toFinset.Nonempty := Set.toFinset_nonempty.mpr hne
  refine ⟨M.toFinset.min' hFne, ?_, ?_⟩
  · have := M.toFinset.min'_mem hFne
    simpa using this
  · intro σ hσ
    apply M.toFinset.min'_le
    have hm : M.toFinset.min' hFne ∈ M := by
      have := M.toFinset.min'_mem hFne; simpa using this
    simpa using hclosed σ hσ _ hm

/-- **Soundness of static symmetry breaking**, stated at the level of an
arbitrary "satisfies the SB constraints" predicate `sb`: if every model
that is a lex-leader w.r.t. `T` satisfies `sb`, then SAT of the base
model set implies SAT of the base-plus-SB model set. Contrapositive:
refuting base ∧ SB refutes base. -/
theorem sb_preserves_sat {M : Set A} {T : Set (A → A)}
    (hclosed : ∀ σ ∈ T, ∀ a ∈ M, σ a ∈ M)
    {sb : A → Prop}
    (himp : ∀ a ∈ M, (∀ σ ∈ T, a ≤ σ a) → sb a) :
    M.Nonempty → ∃ a ∈ M, sb a := by
  intro hne
  obtain ⟨a, haM, hle⟩ := exists_sb_leader hne hclosed
  exact ⟨a, haM, himp a haM hle⟩
