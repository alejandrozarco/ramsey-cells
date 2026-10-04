/-
The s-side/t-side duality, for an ARBITRARY colouring.

`Witness18.codegree_iff` proves exactly this statement, but only for the fixed
colouring `w18` of `K_18`, because that is all the lower-bound witness needed.
Its proof uses nothing about `w18` beyond the abstract relation `colourRel`, so
it lifts verbatim to any `a : EColouring n r`.

Why this file exists: our CNF does NOT encode "no K_{s,t}" with one clause per
copy — that is combinatorially hopeless for K_{3,4}. It encodes the codegree
form ("every 3-set has at most 3 common neighbours") through Sinz sequential
counters, which is why the n=19 formula has 105,213 variables rather than an
explosion of clauses. This lemma is the bridge between the mathematical
statement and the thing the encoder actually constrains, and it is the missing
link between `Sinz.truthful_satisfies` (the counter is satisfiable when the
bound holds) and `SB.Good` (the colouring has no forbidden subgraph).
-/
import Mathlib
import Sbsound.SBGraph

namespace SB

variable {n r : ℕ}

/-! ### Decidability

`colourRel` is decidable for every colouring, not just concrete ones: `Fin n`
has decidable equality and so does `Fin r`. Keeping this computable (rather
than reaching for `Classical`) is what lets the codegree statement be settled
by evaluation later. -/

instance decColourRel (a : EColouring n r) (c : Fin r) (i j : Fin n) :
    Decidable (colourRel a c i j) :=
  if h : i = j then
    isFalse (by rintro ⟨hne, -⟩; exact hne h)
  else
    decidable_of_iff (a (mkEdge i j h) = c)
      ⟨fun hc => ⟨h, hc⟩, fun ⟨_, hc⟩ => hc⟩

/-! ### The two statements -/

/-- **The mathematical predicate.** Colour `c` of `a` contains no `K_{s,t}`:
no pair of disjoint vertex sets of sizes `s` and `t` has all `s*t` crossing
edges coloured `c`. Edges inside `S` or inside `T` are unconstrained, and no
checker is mentioned. -/
def NoKst (a : EColouring n r) (c : Fin r) (s t : ℕ) : Prop :=
  ∀ S T : Finset (Fin n), S.card = s → T.card = t → Disjoint S T →
    ¬ (∀ u ∈ S, ∀ v ∈ T, colourRel a c u v)

/-- The common colour-`c` neighbourhood of `S`: vertices outside `S` joined to
every element of `S` by a colour-`c` edge. -/
def commonNbrs (a : EColouring n r) (c : Fin r) (S : Finset (Fin n)) :
    Finset (Fin n) :=
  Finset.univ.filter fun v => v ∉ S ∧ ∀ u ∈ S, colourRel a c u v

/-- **The encodable form.** Every `s`-set has fewer than `t` common colour-`c`
neighbours — one cardinality bound per `s`-set, which is what the Sinz counters
in the CNF constrain. -/
def SmallCodegree (a : EColouring n r) (c : Fin r) (s t : ℕ) : Prop :=
  ∀ S ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)),
    (commonNbrs a c S).card < t

/-! ### The duality -/

/-- **The bridge.** A monochromatic `K_{s,t}` in colour `c` exists exactly when
some `s`-set has `t` or more common colour-`c` neighbours.

Forward: the `t`-side of a copy sits inside the common neighbourhood of the
`s`-side. Backward: any `t`-subset of a large enough common neighbourhood *is*
the `t`-side of a copy. -/
theorem codegree_iff (a : EColouring n r) (c : Fin r) (s t : ℕ) :
    NoKst a c s t ↔ SmallCodegree a c s t := by
  constructor
  · intro h S hS
    by_contra hcon
    have hge : t ≤ (commonNbrs a c S).card := Nat.not_lt.mp hcon
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hge
    refine h S T (Finset.mem_powersetCard.mp hS).2 hTcard ?_ ?_
    · rw [Finset.disjoint_right]
      intro v hv hvS
      exact (Finset.mem_filter.mp (hTsub hv)).2.1 hvS
    · intro u hu v hv
      exact (Finset.mem_filter.mp (hTsub hv)).2.2 u hu
  · intro h S T hS hT hd hcross
    have hTsub : T ⊆ commonNbrs a c S := by
      intro v hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact fun hvS => (Finset.disjoint_left.mp hd hvS) hv
      · intro u hu; exact hcross u hu v hv
    have hle : t ≤ (commonNbrs a c S).card := hT ▸ Finset.card_le_card hTsub
    exact absurd hle (Nat.not_le.mpr (h S (Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hS⟩)))

/-- The contrapositive shape the encoder actually consumes: if some `s`-set has
`t` or more common neighbours, a `K_{s,t}` exists. -/
theorem exists_Kst_of_large_codegree (a : EColouring n r) (c : Fin r) {s t : ℕ}
    (S : Finset (Fin n)) (hS : S.card = s) (hbig : t ≤ (commonNbrs a c S).card) :
    ¬ NoKst a c s t := by
  intro h
  have := (codegree_iff a c s t).mp h S
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩)
  exact absurd hbig (Nat.not_le.mpr this)

end SB
