/-
Concrete instantiation, part 1: assignment space + closure theorems (O4, O5).
Colourings on ordered pairs (i,j), i<j; Good is generic in one forbidden
graph per colour. Transformations are bare functions — SBCore needs closure
only, no invertibility.
-/
import Mathlib
import Sbsound.SBCore

/-- Edges of `K_n`: ordered pairs under the LEX product order, so the subtype
inherits a coherent LinearOrder/WellFoundedLT from mathlib (row-major, matching
`gen_ramsey.py`'s edge enumeration). -/
abbrev Edge (n : ℕ) := {p : Lex (Fin n × Fin n) // (ofLex p).1 < (ofLex p).2}
abbrev EColouring (n r : ℕ) := Edge n → Fin r

namespace SB

variable {n r : ℕ}

/-- The edge on the unordered pair `{i, j}`, `i ≠ j`. -/
def mkEdge (i j : Fin n) (h : i ≠ j) : Edge n :=
  if hij : i < j then ⟨toLex (i, j), hij⟩
  else ⟨toLex (j, i), (lt_or_gt_of_ne h).resolve_left hij⟩

lemma mkEdge_pos {i j : Fin n} (h : i ≠ j) (hij : i < j) :
    mkEdge i j h = ⟨toLex (i, j), hij⟩ := by simp [mkEdge, hij]

lemma mkEdge_neg {i j : Fin n} (h : i ≠ j) (hji : j < i) :
    mkEdge i j h = ⟨toLex (j, i), hji⟩ := by simp [mkEdge, asymm hji]

lemma mkEdge_comm (i j : Fin n) (h : i ≠ j) :
    mkEdge j i h.symm = mkEdge i j h := by
  rcases lt_or_gt_of_ne h with hij | hji
  · rw [mkEdge_pos h hij, mkEdge_neg h.symm hij]
  · rw [mkEdge_neg h hji, mkEdge_pos h.symm hji]

/-- Vertex relabelling action. -/
def actV (τ : Equiv.Perm (Fin n)) (a : EColouring n r) : EColouring n r :=
  fun e => a (mkEdge (τ (ofLex e.val).1) (τ (ofLex e.val).2)
    (τ.injective.ne (ne_of_lt e.prop)))

/-- Colour permutation action. -/
def actC (σ : Equiv.Perm (Fin r)) (a : EColouring n r) : EColouring n r :=
  fun e => σ (a e)

/-- The colour-`c` relation on vertices. -/
def colourRel (a : EColouring n r) (c : Fin r) (i j : Fin n) : Prop :=
  ∃ h : i ≠ j, a (mkEdge i j h) = c

/-- The graph formed by the colour-`c` edges. -/
def colourGraph (a : EColouring n r) (c : Fin r) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (colourRel a c)

lemma colourGraph_adj (a : EColouring n r) (c : Fin r) (i j : Fin n) :
    (colourGraph a c).Adj i j ↔ colourRel a c i j := by
  constructor
  · rintro ⟨hne, hrel | hrel⟩
    · exact hrel
    · obtain ⟨h, hc⟩ := hrel
      exact ⟨h.symm, by rw [mkEdge_comm]; exact hc⟩
  · intro hrel
    exact ⟨hrel.1, Or.inl hrel⟩

lemma actV_mkEdge (τ : Equiv.Perm (Fin n)) (a : EColouring n r)
    {i j : Fin n} (h : i ≠ j) :
    actV τ a (mkEdge i j h) = a (mkEdge (τ i) (τ j) (τ.injective.ne h)) := by
  rcases lt_or_gt_of_ne h with hij | hji
  · rw [mkEdge_pos h hij]; rfl
  · rw [mkEdge_neg h hji]
    show a (mkEdge (τ j) (τ i) _) = _
    rw [mkEdge_comm (τ i) (τ j) (τ.injective.ne h)]

/-- `colourGraph (actV τ a) c` is the comap of `colourGraph a c` along `τ`. -/
lemma colourGraph_actV (τ : Equiv.Perm (Fin n)) (a : EColouring n r) (c : Fin r) :
    colourGraph (actV τ a) c = (colourGraph a c).comap τ := by
  ext i j
  rw [SimpleGraph.comap_adj, colourGraph_adj, colourGraph_adj]
  show (∃ h : i ≠ j, actV τ a (mkEdge i j h) = c) ↔
       (∃ h : τ i ≠ τ j, a (mkEdge (τ i) (τ j) h) = c)
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨τ.injective.ne h, by rw [← actV_mkEdge τ a h]; exact hc⟩
  · rintro ⟨h, hc⟩
    have hne : i ≠ j := fun hij => h (congrArg τ hij)
    exact ⟨hne, by rw [actV_mkEdge τ a hne]; exact hc⟩

/-- Colour-`c` edges of `actC σ a` are the colour-`σ⁻¹ c` edges of `a`. -/
lemma colourGraph_actC (σ : Equiv.Perm (Fin r)) (a : EColouring n r) (c : Fin r) :
    colourGraph (actC σ a) c = colourGraph a (σ.symm c) := by
  ext i j
  rw [colourGraph_adj, colourGraph_adj]
  show (∃ h : i ≠ j, σ (a (mkEdge i j h)) = c) ↔ (∃ h : i ≠ j, a (mkEdge i j h) = σ.symm c)
  constructor
  · rintro ⟨h, hc⟩; exact ⟨h, by rw [← hc]; simp⟩
  · rintro ⟨h, hc⟩; exact ⟨h, by rw [hc]; simp⟩

/-- Base constraints: no colour contains its forbidden graph. -/
def Good (H : Fin r → Σ k, SimpleGraph (Fin k)) (a : EColouring n r) : Prop :=
  ∀ c, IsEmpty ((H c).2 ↪g colourGraph a c)

/-- **Closure under vertex relabelling** (obligation O4). -/
theorem good_closed_actV (H : Fin r → Σ k, SimpleGraph (Fin k))
    (τ : Equiv.Perm (Fin n)) (a : EColouring n r)
    (hg : Good H a) : Good H (actV τ a) := by
  intro c
  constructor
  intro f
  rw [colourGraph_actV] at f
  exact (hg c).false (f.trans (SimpleGraph.Embedding.comap τ.toEmbedding (colourGraph a c)))

/-- **Closure under colour permutation** (obligation O5), for any colour
permutation preserving the forbidden family. -/
theorem good_closed_actC (H : Fin r → Σ k, SimpleGraph (Fin k))
    (σ : Equiv.Perm (Fin r)) (hH : ∀ c, H (σ c) = H c)
    (a : EColouring n r) (hg : Good H a) : Good H (actC σ a) := by
  intro c
  constructor
  intro f
  rw [colourGraph_actC] at f
  have hHc : H (σ.symm c) = H c := by
    have h1 := hH (σ.symm c)
    rw [Equiv.apply_symm_apply] at h1
    exact h1.symm
  rw [← hHc] at f
  exact (hg (σ.symm c)).false f
end SB
