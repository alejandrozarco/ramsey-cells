/-
Base CNF encoding — the BASE part of gen_ramsey.py — and its correctness.

Variables: one Boolean per (edge, colour). Clauses: ALO per edge, pairwise
AMO per edge, and one all-negative clause per injective copy of the
forbidden graph per colour.

What a copy clause forbids is a FORWARD-hom copy: an injective vertex map
sending every edge of the forbidden graph to a colour-`c` edge, with no
constraint on non-adjacent vertex pairs. That is `SimpleGraph.Copy` /
`SimpleGraph.IsContained` (`⊑`), not the iff-embedding `↪g` of `SB.Good`:
an embedding also *reflects* adjacency, so for non-complete forbidden
graphs `Good` is strictly weaker than what the CNF enforces. Correctness
is therefore proved against the containment-based predicate `Good'`
(which implies `Good`: `good_of_good'`), and the closure + keystone
theorems are re-proved for `Good'` from the exported `colourGraph_actV` /
`colourGraph_actC` equalities and `exists_sb_leader`.
-/
import Mathlib
import Sbsound.SBCore
import Sbsound.SBGraph
import Sbsound.SBKeystone

namespace SB

open scoped SimpleGraph

variable {n r : ℕ}

/-! ### Boolean assignments -/

/-- A Boolean assignment: one Boolean per (edge, colour) variable. -/
abbrev BAssign (n r : ℕ) := Edge n → Fin r → Bool

/-- The assignment induced by an edge colouring. -/
def ofColouring (a : EColouring n r) : BAssign n r := fun e c => decide (a e = c)

/-! ### Literals, clauses, CNF satisfaction -/

/-- A literal: a variable `(e, c)` together with a polarity (`true` = positive). -/
abbrev Lit (n r : ℕ) := (Edge n × Fin r) × Bool

/-- A clause: a disjunction of literals. -/
abbrev Clause (n r : ℕ) := List (Lit n r)

/-- Literal evaluation. -/
def evalLit (β : BAssign n r) : Lit n r → Bool
  | ((e, c), true) => β e c
  | ((e, c), false) => !β e c

/-- A clause is satisfied when some literal evaluates to `true`. -/
def satClause (β : BAssign n r) (C : Clause n r) : Bool := C.any (evalLit β)

/-- A CNF (list of clauses) is satisfied when every clause is. -/
def satCNF (β : BAssign n r) (F : List (Clause n r)) : Prop :=
  ∀ C ∈ F, satClause β C = true

lemma satCNF_append {β : BAssign n r} {F₁ F₂ : List (Clause n r)} :
    satCNF β (F₁ ++ F₂) ↔ satCNF β F₁ ∧ satCNF β F₂ := by
  simp [satCNF, List.mem_append, or_imp, forall_and]

/-! ### The base clause families -/

/-- All edges of `K_n`, as a list (row-major, computable). -/
def edgeList (n : ℕ) : List (Edge n) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).filterMap fun j =>
      if h : i < j then some ⟨toLex (i, j), h⟩ else none

@[simp] lemma mem_edgeList (e : Edge n) : e ∈ edgeList n := by
  simp only [edgeList, List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and]
  exact ⟨(ofLex e.val).1, (ofLex e.val).2, by rw [dif_pos e.prop]; rfl⟩

/-- ALO clause for edge `e`: `e` carries at least one colour. -/
def aloClause (e : Edge n) : Clause n r := (List.finRange r).map fun c => ((e, c), true)

/-- ALO clauses, one per edge. -/
def aloClauses (n r : ℕ) : List (Clause n r) := (edgeList n).map aloClause

/-- AMO clause for edge `e` and colour pair `(c, c')`: not both. -/
def amoClause (e : Edge n) (c c' : Fin r) : Clause n r :=
  [((e, c), false), ((e, c'), false)]

/-- Pairwise AMO clauses: one per edge and colour pair `c < c'`. -/
def amoClauses (n r : ℕ) : List (Clause n r) :=
  (edgeList n).flatMap fun e =>
    (List.finRange r).flatMap fun c =>
      ((List.finRange r).filter fun c' => decide (c < c')).map fun c' => amoClause e c c'

open Classical in
/-- The edge set of the copy of `G` in `K_n` under the vertex map `f`: all
edges `{f u, f v}` with `u`, `v` adjacent in `G`. (Meaningful when `f` is
injective; defined for any `f`.) -/
noncomputable def copyEdges {k : ℕ} (G : SimpleGraph (Fin k)) (f : Fin k → Fin n) :
    Finset (Edge n) :=
  Finset.univ.filter fun e =>
    ∃ u v, ∃ _ : G.Adj u v, ∃ hne : f u ≠ f v, e = mkEdge (f u) (f v) hne

lemma mem_copyEdges {k : ℕ} {G : SimpleGraph (Fin k)} {f : Fin k → Fin n} {e : Edge n} :
    e ∈ copyEdges G f ↔
      ∃ u v, ∃ _ : G.Adj u v, ∃ hne : f u ≠ f v, e = mkEdge (f u) (f v) hne := by
  classical
  simp [copyEdges]

/-- The clause forbidding the copy of `G` under `f` from being monochromatic in
colour `c`: negative literals over the copy's edges. -/
noncomputable def copyClause (c : Fin r) {k : ℕ} (G : SimpleGraph (Fin k))
    (f : Fin k → Fin n) : Clause n r :=
  (copyEdges G f).toList.map fun e => ((e, c), false)

/-- Copy clauses: for each colour `c` and each injective vertex map of the
forbidden graph `(H c).2` into `K_n`, forbid the image edge set from being
entirely colour `c`. (Distinct maps with the same edge image produce repeated
clauses — gen_ramsey.py de-duplicates them — which does not affect
satisfaction.) -/
noncomputable def copyClauses (n r : ℕ) (H : Fin r → Σ k, SimpleGraph (Fin k)) :
    List (Clause n r) :=
  (List.finRange r).flatMap fun c =>
    ((Finset.univ.filter fun f : Fin (H c).1 → Fin n => Function.Injective f).toList).map
      fun f => copyClause c (H c).2 f

/-! ### Membership characterisations -/

lemma mem_aloClauses {C : Clause n r} :
    C ∈ aloClauses n r ↔ ∃ e : Edge n, C = aloClause e := by
  simp only [aloClauses, List.mem_map, mem_edgeList, true_and]
  exact ⟨fun ⟨e, he⟩ => ⟨e, he.symm⟩, fun ⟨e, he⟩ => ⟨e, he.symm⟩⟩

lemma mem_amoClauses {C : Clause n r} :
    C ∈ amoClauses n r ↔ ∃ e c c', c < c' ∧ C = amoClause e c c' := by
  constructor
  · intro h
    simp only [amoClauses, List.mem_flatMap, List.mem_map, List.mem_filter,
      decide_eq_true_eq] at h
    obtain ⟨e, -, c, -, c', ⟨-, hlt⟩, rfl⟩ := h
    exact ⟨e, c, c', hlt, rfl⟩
  · rintro ⟨e, c, c', hlt, rfl⟩
    simp only [amoClauses, List.mem_flatMap, List.mem_map, List.mem_filter,
      decide_eq_true_eq]
    exact ⟨e, mem_edgeList e, c, List.mem_finRange c, c',
      ⟨List.mem_finRange c', hlt⟩, rfl⟩

lemma copyClause_mem_copyClauses (H : Fin r → Σ k, SimpleGraph (Fin k)) (c : Fin r)
    {f : Fin (H c).1 → Fin n} (hf : Function.Injective f) :
    copyClause c (H c).2 f ∈ copyClauses n r H := by
  simp only [copyClauses, List.mem_flatMap, List.mem_map, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨c, List.mem_finRange c, f, hf, rfl⟩

lemma mem_copyClauses {H : Fin r → Σ k, SimpleGraph (Fin k)} {C : Clause n r} :
    C ∈ copyClauses n r H ↔
      ∃ c, ∃ f : Fin (H c).1 → Fin n, Function.Injective f ∧ C = copyClause c (H c).2 f := by
  constructor
  · intro h
    simp only [copyClauses, List.mem_flatMap, List.mem_map, Finset.mem_toList,
      Finset.mem_filter, Finset.mem_univ, true_and] at h
    obtain ⟨c, -, f, hf, rfl⟩ := h
    exact ⟨c, f, hf, rfl⟩
  · rintro ⟨c, f, hf, rfl⟩
    exact copyClause_mem_copyClauses H c hf

/-! ### Satisfaction of the three families under `ofColouring` -/

lemma satClause_alo (a : EColouring n r) (e : Edge n) :
    satClause (ofColouring a) (aloClause e) = true := by
  simp only [satClause]
  refine List.any_eq_true.mpr ⟨((e, a e), true), ?_, ?_⟩
  · exact List.mem_map.mpr ⟨a e, List.mem_finRange _, rfl⟩
  · simp [evalLit, ofColouring]

lemma satClause_amo (a : EColouring n r) (e : Edge n) {c c' : Fin r} (hne : c ≠ c') :
    satClause (ofColouring a) (amoClause e c c') = true := by
  rcases eq_or_ne (a e) c with hc | hc
  · have hc' : a e ≠ c' := fun h => hne (hc.symm.trans h)
    simp [satClause, amoClause, evalLit, ofColouring, hc']
  · simp [satClause, amoClause, evalLit, ofColouring, hc]

lemma satClause_copyClause {a : EColouring n r} {c : Fin r} {k : ℕ}
    (G : SimpleGraph (Fin k)) (f : Fin k → Fin n) :
    satClause (ofColouring a) (copyClause c G f) = true ↔
      ∃ e ∈ copyEdges G f, a e ≠ c := by
  simp [satClause, copyClause, List.any_eq_true, evalLit, ofColouring]

/-! ### Copies vs monochromatic edge sets -/

/-- A forward hom into `colourGraph a c` makes its copy's edges colour `c`. -/
lemma monochromatic_of_forward {a : EColouring n r} {c : Fin r} {k : ℕ}
    {G : SimpleGraph (Fin k)} {f : Fin k → Fin n}
    (hhom : ∀ ⦃u v⦄, G.Adj u v → (colourGraph a c).Adj (f u) (f v)) :
    ∀ e ∈ copyEdges G f, a e = c := by
  intro e he
  obtain ⟨u, v, huv, hne, rfl⟩ := mem_copyEdges.mp he
  obtain ⟨h', hc⟩ := (colourGraph_adj a c _ _).mp (hhom huv)
  exact hc

/-- Conversely, an injective map whose copy edges are all colour `c` is a
`Copy` of `G` inside `colourGraph a c`. -/
lemma isContained_of_monochromatic {a : EColouring n r} {c : Fin r} {k : ℕ}
    {G : SimpleGraph (Fin k)} {f : Fin k → Fin n} (hf : Function.Injective f)
    (hmono : ∀ e ∈ copyEdges G f, a e = c) :
    G ⊑ colourGraph a c := by
  refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
  intro u v huv
  have hne : f u ≠ f v := hf.ne huv.ne
  rw [colourGraph_adj]
  exact ⟨hne, hmono _ (mem_copyEdges.mpr ⟨u, v, huv, hne, rfl⟩)⟩

/-! ### `Good'` and encoder correctness -/

/-- Containment-based goodness: no colour class contains an injective-hom
copy of its forbidden graph. This is exactly what the base CNF forbids. -/
def Good' (H : Fin r → Σ k, SimpleGraph (Fin k)) (a : EColouring n r) : Prop :=
  ∀ c, ¬ (H c).2 ⊑ colourGraph a c

/-- Containment-goodness implies embedding-goodness (`SB.Good`): an
iff-embedding is in particular an injective forward hom. (The converse fails
for non-complete forbidden graphs, which is why the encoder is verified
against `Good'`.) -/
theorem good_of_good' (H : Fin r → Σ k, SimpleGraph (Fin k)) (a : EColouring n r)
    (h : Good' H a) : Good H a := by
  intro c
  constructor
  intro fEmb
  exact h c fEmb.isContained

/-- **Encoder correctness.** The induced assignment of a colouring satisfies
the base CNF (ALO + AMO + copy clauses) iff the colouring is `Good'`. -/
theorem satBase_iff_good' (H : Fin r → Σ k, SimpleGraph (Fin k)) (a : EColouring n r) :
    satCNF (ofColouring a) (aloClauses n r ++ amoClauses n r ++ copyClauses n r H) ↔
      Good' H a := by
  rw [satCNF_append, satCNF_append]
  constructor
  · rintro ⟨-, hcopy⟩ c hcon
    obtain ⟨φ⟩ := hcon
    have hs := hcopy _ (copyClause_mem_copyClauses H c φ.injective)
    rw [satClause_copyClause] at hs
    obtain ⟨e, he, hne⟩ := hs
    exact hne (monochromatic_of_forward (fun u v huv => φ.toHom.map_adj huv) e he)
  · intro hgood
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro C hC
      obtain ⟨e, rfl⟩ := mem_aloClauses.mp hC
      exact satClause_alo a e
    · intro C hC
      obtain ⟨e, c, c', hlt, rfl⟩ := mem_amoClauses.mp hC
      exact satClause_amo a e (ne_of_lt hlt)
    · intro C hC
      obtain ⟨c, f, hf, rfl⟩ := mem_copyClauses.mp hC
      by_contra hfalse
      refine hgood c (isContained_of_monochromatic hf ?_)
      intro e he
      by_contra hnec
      exact hfalse ((satClause_copyClause _ _).mpr ⟨e, he, hnec⟩)

/-! ### Closure and keystone for `Good'` -/

/-- **Closure under vertex relabelling** for `Good'` (mirrors
`good_closed_actV`). -/
theorem good'_closed_actV (H : Fin r → Σ k, SimpleGraph (Fin k))
    (τ : Equiv.Perm (Fin n)) (a : EColouring n r)
    (hg : Good' H a) : Good' H (actV τ a) := by
  intro c hcon
  rw [colourGraph_actV] at hcon
  exact hg c (hcon.trans
    (SimpleGraph.Embedding.comap τ.toEmbedding (colourGraph a c)).isContained)

/-- **Closure under colour permutation** for `Good'` (mirrors
`good_closed_actC`). -/
theorem good'_closed_actC (H : Fin r → Σ k, SimpleGraph (Fin k))
    (σ : Equiv.Perm (Fin r)) (hH : ∀ c, H (σ c) = H c)
    (a : EColouring n r) (hg : Good' H a) : Good' H (actC σ a) := by
  intro c hcon
  rw [colourGraph_actC] at hcon
  have hHc : H (σ.symm c) = H c := by
    have h1 := hH (σ.symm c)
    rw [Equiv.apply_symm_apply] at h1
    exact h1.symm
  rw [← hHc] at hcon
  exact hg (σ.symm c) hcon

/-- **Keystone for `Good'`.** If a `Good'` colouring exists, a `Good'`
lex-leader exists (mirrors `exists_good_leader`). -/
theorem exists_good'_leader (H : Fin r → Σ k, SimpleGraph (Fin k))
    (hsat : ∃ a : EColouring n r, Good' H a) :
    ∃ a : EColouring n r, Good' H a ∧
      (∀ τ : Equiv.Perm (Fin n), lexView a ≤ lexView (actV τ a)) ∧
      (∀ σ : Equiv.Perm (Fin r), (∀ c, H (σ c) = H c) →
        lexView a ≤ lexView (actC σ a)) := by
  classical
  obtain ⟨a₀, h₀⟩ := hsat
  let M : Set (Lex (Edge n → Fin r)) := {x | Good' H (ofLex x)}
  let T : Set (Lex (Edge n → Fin r) → Lex (Edge n → Fin r)) :=
    (fun f => toLex ∘ f ∘ ofLex) '' symSet H
  have hclosed : ∀ g ∈ T, ∀ x ∈ M, g x ∈ M := by
    rintro g ⟨f, hf, rfl⟩ x hx
    rcases hf with ⟨τ, rfl⟩ | ⟨σ, hσ, rfl⟩
    · exact good'_closed_actV H τ (ofLex x) hx
    · exact good'_closed_actC H σ hσ (ofLex x) hx
  obtain ⟨x, hxM, hle⟩ := exists_sb_leader (M := M) ⟨toLex a₀, h₀⟩ hclosed
  refine ⟨ofLex x, hxM, ?_, ?_⟩
  · intro τ
    exact hle _ ⟨actV τ, Or.inl ⟨τ, rfl⟩, rfl⟩
  · intro σ hσ
    exact hle _ ⟨actC σ, Or.inr ⟨σ, hσ, rfl⟩, rfl⟩

end SB

#print axioms SB.satBase_iff_good'
#print axioms SB.good_of_good'
#print axioms SB.good'_closed_actV
#print axioms SB.good'_closed_actC
#print axioms SB.exists_good'_leader
