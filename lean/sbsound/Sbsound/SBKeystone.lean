/-
Keystone: SBCore + closure theorems ⇒ a Good lex-leader exists.

Order design: Edge n is a subtype of `Lex (Fin n × Fin n)`, so it inherits
the row-major linear order (= gen_ramsey.py's edge enumeration) coherently.
Colourings are compared in `Lex (Edge n → Fin r)` — the value-sequence
order the CNF's vertex-lex clauses encode. Leaderhood is stated through
`toLex` to keep the pointwise Pi order out of the picture.
-/
import Mathlib
import Sbsound.SBCore
import Sbsound.SBGraph

namespace SB

variable {n r : ℕ}

/-- Lex view of a colouring. -/
noncomputable abbrev lexView (a : EColouring n r) : Lex (Edge n → Fin r) := toLex a

/-- The transformation set used by the campaign's SB clauses. -/
def symSet (H : Fin r → Σ k, SimpleGraph (Fin k)) :
    Set (EColouring n r → EColouring n r) :=
  {f | ∃ τ : Equiv.Perm (Fin n), f = actV τ} ∪
  {f | ∃ σ : Equiv.Perm (Fin r), (∀ c, H (σ c) = H c) ∧ f = actC σ}

/-- **Keystone.** If a Good colouring exists, a Good lex-leader exists:
one whose lex view is ≤ that of each of its images under every vertex
relabelling and every family-preserving colour permutation. -/
theorem exists_good_leader (H : Fin r → Σ k, SimpleGraph (Fin k))
    (hsat : ∃ a : EColouring n r, Good H a) :
    ∃ a : EColouring n r, Good H a ∧
      (∀ τ : Equiv.Perm (Fin n), lexView a ≤ lexView (actV τ a)) ∧
      (∀ σ : Equiv.Perm (Fin r), (∀ c, H (σ c) = H c) →
        lexView a ≤ lexView (actC σ a)) := by
  classical
  obtain ⟨a₀, h₀⟩ := hsat
  -- work in the Lex synonym so SBCore's LinearOrder is the lex order
  let M : Set (Lex (Edge n → Fin r)) := {x | Good H (ofLex x)}
  let T : Set (Lex (Edge n → Fin r) → Lex (Edge n → Fin r)) :=
    (fun f => toLex ∘ f ∘ ofLex) '' symSet H
  have hclosed : ∀ g ∈ T, ∀ x ∈ M, g x ∈ M := by
    rintro g ⟨f, hf, rfl⟩ x hx
    rcases hf with ⟨τ, rfl⟩ | ⟨σ, hσ, rfl⟩
    · exact good_closed_actV H τ (ofLex x) hx
    · exact good_closed_actC H σ hσ (ofLex x) hx
  obtain ⟨x, hxM, hle⟩ := exists_sb_leader (M := M) ⟨toLex a₀, h₀⟩ hclosed
  refine ⟨ofLex x, hxM, ?_, ?_⟩
  · intro τ
    exact hle _ ⟨actV τ, Or.inl ⟨τ, rfl⟩, rfl⟩
  · intro σ hσ
    exact hle _ ⟨actC σ, Or.inr ⟨σ, hσ, rfl⟩, rfl⟩

end SB
