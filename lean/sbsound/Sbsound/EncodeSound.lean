/-
**Encode soundness for the bipartite cells.**

The deliverable: if any colouring of `K_n` avoids the forbidden complete
bipartite patterns, then one exists that *simultaneously*

1. still avoids them,
2. is a lex-leader under every vertex relabelling — hence satisfies the
   emitted `--vertex-lex` clauses, via `sb_clauses_satisfiable_of_leader`, and
3. supplies register values satisfying every codegree counter clause the
   encoder emits.

Contrapositive, which is the direction an UNSAT verdict consumes: if the
emitted CNF has no model, no such colouring exists.

Why this needs its own file rather than reusing `SBEncode`: that module encodes
a forbidden graph as one clause per copy, which is combinatorially hopeless for
`K_{3,4}`. The campaign's CNF encodes the same constraint by codegree counting,
so the base-CNF half of soundness has to be redone against `NoKst` — done here,
on top of `Codegree` and `CodegreeEncode`.

`NoKst` is a containment statement (only the crossing edges are constrained),
so it is closed under relabelling directly; there is no need to route through
the embedding-based `Good` or to build `K_{s,t}` as a `SimpleGraph` first.
-/
import Mathlib
import Sbsound.SBKeystone
import Sbsound.CodegreeEncode

namespace SB

variable {n r : ℕ}

/-! ### Transporting the colour relation along a relabelling -/

/-- Relabelling moves the colour relation by `τ`. This is the body of
`colourGraph_actV`, stated at the level of the relation so the finite-set
arguments below can use it without passing through `SimpleGraph`. -/
lemma colourRel_actV (τ : Equiv.Perm (Fin n)) (a : EColouring n r) (c : Fin r)
    (i j : Fin n) :
    colourRel (actV τ a) c i j ↔ colourRel a c (τ i) (τ j) := by
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨τ.injective.ne h, by rw [← actV_mkEdge τ a h]; exact hc⟩
  · rintro ⟨h, hc⟩
    have hne : i ≠ j := fun hij => h (congrArg τ hij)
    exact ⟨hne, by rw [actV_mkEdge τ a hne]; exact hc⟩

/-! ### Closure of `NoKst` under relabelling -/

/-- **Closure.** Relabelling the vertices cannot create a `K_{s,t}`: push the
two sides through `τ`, which preserves their sizes and disjointness. -/
theorem noKst_closed_actV (τ : Equiv.Perm (Fin n)) (a : EColouring n r)
    (c : Fin r) (s t : ℕ) (h : NoKst a c s t) : NoKst (actV τ a) c s t := by
  intro S T hS hT hd hcross
  refine h (S.image τ) (T.image τ) ?_ ?_ ?_ ?_
  · rw [Finset.card_image_of_injective _ τ.injective]; exact hS
  · rw [Finset.card_image_of_injective _ τ.injective]; exact hT
  · exact (Finset.disjoint_image τ.injective).mpr hd
  · intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    exact (colourRel_actV τ a c u' v').mp (hcross u' hu' v' hv')

/-! ### The forbidden family, and its lex-leader -/

/-- A forbidden complete bipartite pattern per colour: colour `c` must contain
no `K_{(st c).1, (st c).2}`. For this campaign's cell,
`st = ![(3,4), (3,3)]`. -/
def NoKstFam (a : EColouring n r) (st : Fin r → ℕ × ℕ) : Prop :=
  ∀ c, NoKst a c (st c).1 (st c).2

theorem noKstFam_closed_actV (τ : Equiv.Perm (Fin n)) (a : EColouring n r)
    {st : Fin r → ℕ × ℕ} (h : NoKstFam a st) : NoKstFam (actV τ a) st :=
  fun c => noKst_closed_actV τ a c _ _ (h c)

/-- **Lex-leader existence for the bipartite family.** Mirrors
`exists_good_leader`, but for `NoKstFam`, whose closure was just proved
directly. Only vertex relabellings are used: the two forbidden patterns differ,
so no colour permutation preserves the family. -/
theorem exists_noKstFam_leader {st : Fin r → ℕ × ℕ}
    (hsat : ∃ a : EColouring n r, NoKstFam a st) :
    ∃ a : EColouring n r, NoKstFam a st ∧
      (∀ τ : Equiv.Perm (Fin n), lexView a ≤ lexView (actV τ a)) := by
  classical
  obtain ⟨a₀, h₀⟩ := hsat
  let M : Set (Lex (Edge n → Fin r)) := {x | NoKstFam (ofLex x) st}
  let T : Set (Lex (Edge n → Fin r) → Lex (Edge n → Fin r)) :=
    (fun f => toLex ∘ f ∘ ofLex) '' {f | ∃ τ : Equiv.Perm (Fin n), f = actV τ}
  have hclosed : ∀ g ∈ T, ∀ x ∈ M, g x ∈ M := by
    rintro g ⟨f, ⟨τ, rfl⟩, rfl⟩ x hx
    exact noKstFam_closed_actV τ (ofLex x) hx
  obtain ⟨x, hxM, hle⟩ := exists_sb_leader (M := M) ⟨toLex a₀, h₀⟩ hclosed
  exact ⟨ofLex x, hxM, fun τ => hle _ ⟨actV τ, ⟨τ, rfl⟩, rfl⟩⟩

/-! ### The deliverable -/

/-- **Encode soundness.** If some colouring avoids the forbidden bipartite
patterns, then some colouring avoids them *and* is a lex-leader *and* supplies
register values satisfying every emitted codegree counter clause.

Clause (2) is the hypothesis of `sb_clauses_satisfiable_of_leader`, restricted
to the adjacent transpositions the encoder actually breaks on; clause (3) is
the codegree half. Together they say: a model of the base problem yields a
model of the *emitted* CNF, symmetry-breaking clauses and counters included —
so refuting the emitted CNF refutes the base problem. -/
theorem encode_sound {st : Fin r → ℕ × ℕ} (hst : ∀ c, 2 ≤ (st c).2)
    (hsat : ∃ a : EColouring n r, NoKstFam a st) :
    ∃ a : EColouring n r,
      NoKstFam a st ∧
      (∀ τ : Equiv.Perm (Fin n), lexView a ≤ lexView (actV τ a)) ∧
      (∀ c : Fin r, ∀ S ∈ Finset.powersetCard (st c).1
            (Finset.univ : Finset (Fin n)),
        Sinz.Clauses (codegreeInputs a c S)
          (Sinz.truthful (k := (st c).2 - 1) (codegreeInputs a c S))) := by
  obtain ⟨a, hgood, hlead⟩ := exists_noKstFam_leader hsat
  refine ⟨a, hgood, hlead, ?_⟩
  intro c S hS
  exact codegree_clauses_of_noKst a c (hst c) (hgood c) S hS

/-! ### The campaign's cell -/

/-- The forbidden family of this campaign: `K_{3,4}` in colour 0, `K_{3,3}` in
colour 1. -/
def k34k33 : Fin 2 → ℕ × ℕ := ![(3, 4), (3, 3)]

/-- **Specialisation to `R(K_{3,4}, K_{3,3})`.** A colouring of `K_n` with no
`K_{3,4}` in colour 0 and no `K_{3,3}` in colour 1 yields a lex-leader with the
same property whose codegree counters are satisfiable at bounds 3 and 2 — the
exact bounds `gen_ramsey.py` emits.

This is the semantic content of the encode step for the cell the campaign
refuted at `n = 19`. -/
theorem encode_sound_k34k33
    (hsat : ∃ a : EColouring n 2, NoKst a 0 3 4 ∧ NoKst a 1 3 3) :
    ∃ a : EColouring n 2,
      (NoKst a 0 3 4 ∧ NoKst a 1 3 3) ∧
      (∀ τ : Equiv.Perm (Fin n), lexView a ≤ lexView (actV τ a)) ∧
      (∀ S ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin n)),
        Sinz.Clauses (codegreeInputs a 0 S)
          (Sinz.truthful (k := 3) (codegreeInputs a 0 S))) ∧
      (∀ S ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin n)),
        Sinz.Clauses (codegreeInputs a 1 S)
          (Sinz.truthful (k := 2) (codegreeInputs a 1 S))) := by
  have hfam : ∃ a : EColouring n 2, NoKstFam a k34k33 := by
    obtain ⟨a, h0, h1⟩ := hsat
    refine ⟨a, ?_⟩
    intro c
    fin_cases c
    · simpa [k34k33] using h0
    · simpa [k34k33] using h1
  have hst : ∀ c : Fin 2, 2 ≤ (k34k33 c).2 := by
    intro c; fin_cases c <;> norm_num [k34k33]
  obtain ⟨a, hgood, hlead, hcnt⟩ := encode_sound hst hfam
  refine ⟨a, ⟨?_, ?_⟩, hlead, ?_, ?_⟩
  · simpa [k34k33] using hgood 0
  · simpa [k34k33] using hgood 1
  · simpa [k34k33] using hcnt 0
  · simpa [k34k33] using hcnt 1

end SB

#print axioms SB.noKst_closed_actV
#print axioms SB.exists_noKstFam_leader
#print axioms SB.encode_sound
#print axioms SB.encode_sound_k34k33
