/-
Degree ordering + conditional lex (the "DOL" symmetry breaking), semantic layer.

Model set: colourings avoiding the forbidden family whose colour-`c` degree
sequence is antitone in the vertex index. Transformations: for each adjacent
pair (i, i+1), swap the two vertices when their colour-`c` degrees are equal,
otherwise do nothing. Both preserve the model set, so SBCore's `exists_sb_leader`
gives a good, degree-sorted colouring that is lex-minimal among its conditional
swaps: exactly the semantic content of the DO + L clause families.
-/
import Mathlib
import Sbsound.SBCore
import Sbsound.SBGraph
import Sbsound.SBKeystone
import Sbsound.EncodeSound

namespace SB

variable {n r : ℕ}

open Classical in
/-- Colour-`c` degree of vertex `v`: the number of `w` joined to `v` by a colour-`c` edge. -/
noncomputable def deg (a : EColouring n r) (c : Fin r) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun w => (colourGraph a c).Adj v w).card

/-- Relabelling permutes degrees: the degree of `v` in `actV τ a` is the degree of `τ v` in `a`. -/
theorem deg_actV (τ : Equiv.Perm (Fin n)) (a : EColouring n r) (c : Fin r) (v : Fin n) :
    deg (actV τ a) c v = deg a c (τ v) := by
  classical
  unfold deg
  rw [colourGraph_actV]
  refine Finset.card_equiv τ ?_
  intro w
  simp [SimpleGraph.comap_adj]

theorem deg_actV_fun (τ : Equiv.Perm (Fin n)) (a : EColouring n r) (c : Fin r) :
    deg (actV τ a) c = deg a c ∘ τ := by
  funext v; exact deg_actV τ a c v

/-- Some relabelling sorts the colour-`c` degrees into antitone order. -/
theorem exists_sorting_relabel (a : EColouring n r) (c : Fin r) :
    ∃ τ : Equiv.Perm (Fin n), Antitone (deg (actV τ a) c) := by
  classical
  let f : Fin n → ℕᵒᵈ := fun v => OrderDual.toDual (deg a c v)
  refine ⟨Tuple.sort f, ?_⟩
  rw [deg_actV_fun]
  have hmono : Monotone (f ∘ Tuple.sort f) := Tuple.monotone_sort f
  have : Monotone (OrderDual.toDual ∘ (deg a c ∘ Tuple.sort f)) := hmono
  exact monotone_toDual_comp_iff.mp this

/-- The vertex after `i`. -/
def succV (i : Fin n) (hi : i.val + 1 < n) : Fin n := ⟨i.val + 1, hi⟩

lemma succV_ne (i : Fin n) (hi : i.val + 1 < n) : i ≠ succV i hi := by
  intro h; have := congrArg Fin.val h; simp [succV] at this

/-- Conditional adjacent swap: exchange `i` and `i+1` iff their colour-`c` degrees agree. -/
noncomputable def swapIf (a : EColouring n r) (c : Fin r) (i : Fin n) (hi : i.val + 1 < n) :
    EColouring n r :=
  if deg a c i = deg a c (succV i hi) then actV (Equiv.swap i (succV i hi)) a else a

/-- Swapping two vertices of equal degree leaves the degree function unchanged. -/
theorem deg_swap_eq (a : EColouring n r) (c : Fin r) (i j : Fin n)
    (hij : deg a c i = deg a c j) :
    deg (actV (Equiv.swap i j) a) c = deg a c := by
  funext u
  rw [deg_actV]
  by_cases hu : u = i
  · subst hu; rw [Equiv.swap_apply_left]; exact hij.symm
  · by_cases hu' : u = j
    · subst hu'; rw [Equiv.swap_apply_right]; exact hij
    · rw [Equiv.swap_apply_of_ne_of_ne hu hu']

/-- Antitone degree sequences are preserved by conditional swaps. -/
theorem antitone_swapIf (a : EColouring n r) (c : Fin r) (i : Fin n) (hi : i.val + 1 < n)
    (ha : Antitone (deg a c)) : Antitone (deg (swapIf a c i hi) c) := by
  unfold swapIf
  split_ifs with h
  · rw [deg_swap_eq a c i (succV i hi) h]; exact ha
  · exact ha

/-- Any predicate closed under relabelling is preserved by conditional swaps. -/
theorem closed_swapIf (P : EColouring n r → Prop)
    (hP : ∀ (τ : Equiv.Perm (Fin n)) (a : EColouring n r), P a → P (actV τ a))
    (a : EColouring n r) (c : Fin r) (i : Fin n) (hi : i.val + 1 < n)
    (ha : P a) : P (swapIf a c i hi) := by
  unfold swapIf
  split_ifs with h
  · exact hP _ a ha
  · exact ha

/-- **DOL leader, generic form.** For any relabelling-closed predicate `P` (the forbidden-
family constraint) that some colouring satisfies, there is a colouring satisfying `P` whose
colour-`c` degrees are antitone and whose lex view is ≤ that of the swap of any two adjacent
vertices of equal degree. -/
theorem exists_dol_leader_of_closed (P : EColouring n r → Prop)
    (hP : ∀ (τ : Equiv.Perm (Fin n)) (a : EColouring n r), P a → P (actV τ a))
    (c : Fin r) (hsat : ∃ a : EColouring n r, P a) :
    ∃ a : EColouring n r, P a ∧ Antitone (deg a c) ∧
      ∀ (i : Fin n) (hi : i.val + 1 < n), deg a c i = deg a c (succV i hi) →
        lexView a ≤ lexView (actV (Equiv.swap i (succV i hi)) a) := by
  classical
  obtain ⟨a₀, h₀⟩ := hsat
  obtain ⟨τ₀, hτ₀⟩ := exists_sorting_relabel a₀ c
  let M : Set (Lex (Edge n → Fin r)) := {x | P (ofLex x) ∧ Antitone (deg (ofLex x) c)}
  let T : Set (Lex (Edge n → Fin r) → Lex (Edge n → Fin r)) :=
    Set.range fun p : {i : Fin n // i.val + 1 < n} =>
      fun x => toLex (swapIf (ofLex x) c p.1 p.2)
  have hne : M.Nonempty := ⟨toLex (actV τ₀ a₀), hP τ₀ a₀ h₀, hτ₀⟩
  have hclosed : ∀ g ∈ T, ∀ x ∈ M, g x ∈ M := by
    rintro g ⟨p, rfl⟩ x ⟨hx1, hx2⟩
    exact ⟨closed_swapIf P hP (ofLex x) c p.1 p.2 hx1, antitone_swapIf (ofLex x) c p.1 p.2 hx2⟩
  obtain ⟨x, ⟨hxP, hxA⟩, hle⟩ := exists_sb_leader (M := M) hne hclosed
  refine ⟨ofLex x, hxP, hxA, ?_⟩
  intro i hi hdeg
  have h := hle _ ⟨⟨i, hi⟩, rfl⟩
  simp only [swapIf, hdeg, if_true] at h
  exact h

/-- DOL leader for the bipartite forbidden families used by the search. -/
theorem exists_dol_leader {st : Fin r → ℕ × ℕ} (c : Fin r)
    (hsat : ∃ a : EColouring n r, NoKstFam a st) :
    ∃ a : EColouring n r, NoKstFam a st ∧ Antitone (deg a c) ∧
      ∀ (i : Fin n) (hi : i.val + 1 < n), deg a c i = deg a c (succV i hi) →
        lexView a ≤ lexView (actV (Equiv.swap i (succV i hi)) a) :=
  exists_dol_leader_of_closed (fun a => NoKstFam a st)
    (fun τ a h => noKstFam_closed_actV τ a h) c hsat

/-- DOL leader for an arbitrary forbidden family (one graph per colour). -/
theorem exists_dol_leader_good (H : Fin r → Σ k, SimpleGraph (Fin k)) (c : Fin r)
    (hsat : ∃ a : EColouring n r, Good H a) :
    ∃ a : EColouring n r, Good H a ∧ Antitone (deg a c) ∧
      ∀ (i : Fin n) (hi : i.val + 1 < n), deg a c i = deg a c (succV i hi) →
        lexView a ≤ lexView (actV (Equiv.swap i (succV i hi)) a) :=
  exists_dol_leader_of_closed (Good H) (fun τ a h => good_closed_actV H τ a h) c hsat

/-- **Refuting the DOL leaders refutes the whole space** (bipartite families). -/
theorem no_colouring_of_no_dol_leader {st : Fin r → ℕ × ℕ} (c : Fin r)
    (hno : ¬ ∃ a : EColouring n r, NoKstFam a st ∧ Antitone (deg a c) ∧
      ∀ (i : Fin n) (hi : i.val + 1 < n), deg a c i = deg a c (succV i hi) →
        lexView a ≤ lexView (actV (Equiv.swap i (succV i hi)) a)) :
    ¬ ∃ a : EColouring n r, NoKstFam a st :=
  fun hsat => hno (exists_dol_leader c hsat)

/-- Same for an arbitrary forbidden family. -/
theorem no_colouring_of_no_dol_leader_good (H : Fin r → Σ k, SimpleGraph (Fin k)) (c : Fin r)
    (hno : ¬ ∃ a : EColouring n r, Good H a ∧ Antitone (deg a c) ∧
      ∀ (i : Fin n) (hi : i.val + 1 < n), deg a c i = deg a c (succV i hi) →
        lexView a ≤ lexView (actV (Equiv.swap i (succV i hi)) a)) :
    ¬ ∃ a : EColouring n r, Good H a :=
  fun hsat => hno (exists_dol_leader_good H c hsat)

#print axioms no_colouring_of_no_dol_leader
#print axioms no_colouring_of_no_dol_leader_good

end SB
