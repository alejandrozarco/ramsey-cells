/-
Codegree soundness: a colouring with no `K_{s,t}` yields register values
satisfying the Sinz counter clauses the CNF emits for every `s`-set.

This is the composition the campaign was missing. Both ingredients existed and
neither had been joined to the other:

* `SB.codegree_iff` (Codegree.lean) — no `K_{s,t}` in colour `c` **iff** every
  `s`-set has fewer than `t` common colour-`c` neighbours.
* `SB.Sinz.truthful_satisfies` (Sinz.lean) — the sequential counter's clauses
  are satisfied by the truthful register assignment whenever the count really
  is within the bound.

Chaining them gives the direction the UNSAT verdict consumes: if a good
colouring existed, the codegree clauses of the emitted CNF would be
satisfiable, so their unsatisfiability rules out any good colouring. The other
direction is deliberately not proved and not needed — SAT outcomes are
witnesses, and witnesses are checked directly against the colouring
(`Witness18.lean`), never through the encoder.
-/
import Mathlib
import Sbsound.Codegree
import Sbsound.Sinz

namespace SB

variable {n r : ℕ}

/-! ### The counter's input vector

For an `s`-set `S`, the encoder counts how many vertices are common colour-`c`
neighbours of `S`. Vertices of `S` itself are never counted: `commonNbrs`
excludes them. -/

/-- The Boolean input vector fed to the counter for the `s`-set `S`. -/
def codegreeInputs (a : EColouring n r) (c : Fin r) (S : Finset (Fin n)) :
    Fin n → Bool :=
  fun v => decide (v ∈ commonNbrs a c S)

@[simp] lemma codegreeInputs_eq_true (a : EColouring n r) (c : Fin r)
    (S : Finset (Fin n)) (v : Fin n) :
    codegreeInputs a c S v = true ↔ v ∈ commonNbrs a c S := by
  simp [codegreeInputs]

/-- The vector's support is exactly the common neighbourhood. -/
lemma filter_codegreeInputs (a : EColouring n r) (c : Fin r)
    (S : Finset (Fin n)) :
    (Finset.univ.filter fun v => codegreeInputs a c S v = true)
      = commonNbrs a c S := by
  ext v
  simp

/-! ### A prefix never exceeds the total -/

/-- Every prefix count is bounded by the number of true inputs. The counter's
obligation is stated prefix-wise, but the codegree bound is a statement about
the total, so this is the step that connects them. -/
lemma prefixCount_le_total {m : ℕ} (y : Fin m → Bool) (i : Fin m) :
    Sinz.prefixCount y i ≤ (Finset.univ.filter fun v => y v = true).card :=
  Finset.card_le_card (by
    intro v hv
    rw [Sinz.mem_prefixSet] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv.2⟩)

/-! ### Soundness, per `s`-set -/

/-- **The counter is satisfiable for one `s`-set.** If `S` has at most `k`
common colour-`c` neighbours, the truthful registers satisfy every clause the
encoder emits for `S`. -/
theorem codegree_counter_sound (a : EColouring n r) (c : Fin r)
    (S : Finset (Fin n)) {k : ℕ} (hk : 0 < k)
    (hcard : (commonNbrs a c S).card ≤ k) :
    Sinz.Clauses (codegreeInputs a c S)
      (Sinz.truthful (k := k) (codegreeInputs a c S)) := by
  refine Sinz.truthful_satisfies _ hk ?_
  intro i
  calc Sinz.prefixCount (codegreeInputs a c S) i
      ≤ (Finset.univ.filter fun v => codegreeInputs a c S v = true).card :=
        prefixCount_le_total _ i
    _ = (commonNbrs a c S).card := by rw [filter_codegreeInputs]
    _ ≤ k := hcard

/-! ### Soundness, for the whole colour class -/

/-- **The deliverable.** A colouring whose colour `c` contains no `K_{s,t}`
supplies register values satisfying the counter clauses of *every* `s`-set at
once — with the bound `t - 1`, which is what `gen_ramsey.py` emits (`≤ 3`
common neighbours for `K_{3,4}`, `≤ 2` for `K_{3,3}`).

Contrapositive, which is the direction the search consumes: if those clauses
are jointly unsatisfiable, no such colouring exists. -/
theorem codegree_clauses_of_noKst (a : EColouring n r) (c : Fin r) {s t : ℕ}
    (ht : 2 ≤ t) (hgood : NoKst a c s t) :
    ∀ S ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)),
      Sinz.Clauses (codegreeInputs a c S)
        (Sinz.truthful (k := t - 1) (codegreeInputs a c S)) := by
  intro S hS
  have hlt : (commonNbrs a c S).card < t := (codegree_iff a c s t).mp hgood S hS
  refine codegree_counter_sound a c S ?_ ?_
  · omega
  · omega

/-- Specialisation to the two colour classes of this campaign's cell:
`K_{3,4}` forbidden in colour 0, `K_{3,3}` in colour 1. -/
theorem codegree_clauses_k34k33 (a : EColouring n 2)
    (h0 : NoKst a 0 3 4) (h1 : NoKst a 1 3 3) :
    (∀ S ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin n)),
        Sinz.Clauses (codegreeInputs a 0 S)
          (Sinz.truthful (k := 3) (codegreeInputs a 0 S))) ∧
    (∀ S ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin n)),
        Sinz.Clauses (codegreeInputs a 1 S)
          (Sinz.truthful (k := 2) (codegreeInputs a 1 S))) := by
  constructor
  · simpa using codegree_clauses_of_noKst a 0 (by norm_num) h0
  · simpa using codegree_clauses_of_noKst a 1 (by norm_num) h1

end SB
