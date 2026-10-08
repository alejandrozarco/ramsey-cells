/-
# M3: split children

`splitChild F tag units` (split_certify.py) is `F`'s clauses followed by one unit clause per literal.
* `splitChild_sat`: an assignment satisfying `F` and all the units satisfies the child.
* `coversB`: a decidable check that a list of unit lists is a complete case split (at every node
  every child starts with `+v` or `-v` for one variable `v` and both signs are covered, or some
  child has no units left). `coversB_sound`: then every assignment satisfies all units of some
  child. `split_unsat`: if `coversB` holds and every child is unsatisfiable, so is the parent.
  The per-parent check `coversB _ units = true` is meant to be discharged by `decide`.
-/
import RootedBridge.Spec

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

theorem splitChild_clauses (F : Formula) (tag : String) (units : List Int) :
    (splitChild F tag units).clauses = F.clauses ++ (units.map fun l => #[l]).toArray := rfl

/-- A satisfying assignment of the parent that makes every unit true satisfies the child. -/
theorem splitChild_sat (F : Formula) (tag : String) (units : List Int) (σ : Nat → Bool)
    (hF : ClsSat σ F.clauses) (hu : ∀ l ∈ units, LitSat σ l) :
    ClsSat σ (splitChild F tag units).clauses := by
  intro c hc
  rw [splitChild_clauses] at hc
  rcases Array.mem_append.mp hc with h | h
  · exact hF c h
  · simp only [List.mem_toArray, List.mem_map] at h
    obtain ⟨l, hl, rfl⟩ := h
    exact ⟨l, by simp, hu l hl⟩

/-- Complete case split over unit lists (fuel-bounded recursion). -/
def coversB : Nat → List (List Int) → Bool
  | 0, _ => false
  | n + 1, us =>
    us.any (·.isEmpty) ||
    (match us.head? with
     | some (l :: _) =>
       (l != 0) && (us.all fun u => u.head? == some l || u.head? == some (-l)) &&
       coversB n (us.filterMap fun u => if u.head? == some l then some u.tail else none) &&
       coversB n (us.filterMap fun u => if u.head? == some (-l) then some u.tail else none)
     | _ => false)

theorem coversB_sound : ∀ (n : Nat) (us : List (List Int)), coversB n us = true →
    ∀ σ : Nat → Bool, ∃ u ∈ us, ∀ l ∈ u, LitSat σ l
  | 0, us, h, σ => by simp [coversB] at h
  | n + 1, us, h, σ => by
    unfold coversB at h
    rcases Bool.or_eq_true_iff.mp h with h1 | h1
    · obtain ⟨u, hu, he⟩ := List.any_eq_true.mp h1
      refine ⟨u, hu, fun l hl => ?_⟩
      simp only [List.isEmpty_iff] at he; subst he; simp at hl
    · split at h1
      · next l rest hhead =>
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h1
        obtain ⟨⟨⟨hl0, hall⟩, hpos⟩, hneg⟩ := h1
        by_cases hσ : lv σ l = true
        · obtain ⟨u', hu', hlits⟩ := coversB_sound n _ hpos σ
          obtain ⟨u, hu, hu'eq⟩ := List.mem_filterMap.mp hu'
          split at hu'eq
          · next hh =>
            cases hu'eq
            refine ⟨u, hu, fun x hx => ?_⟩
            have hh' : u.head? = some l := by simpa using hh
            cases u with
            | nil => simp at hh'
            | cons a t =>
              simp at hh'; subst hh'
              rcases List.mem_cons.mp hx with rfl | hx
              · exact (litSat_iff hl0).mpr hσ
              · exact hlits x hx
          · cases hu'eq
        · obtain ⟨u', hu', hlits⟩ := coversB_sound n _ hneg σ
          obtain ⟨u, hu, hu'eq⟩ := List.mem_filterMap.mp hu'
          split at hu'eq
          · next hh =>
            cases hu'eq
            refine ⟨u, hu, fun x hx => ?_⟩
            have hh' : u.head? = some (-l) := by simpa using hh
            cases u with
            | nil => simp at hh'
            | cons a t =>
              simp at hh'; subst hh'
              rcases List.mem_cons.mp hx with rfl | hx
              · rw [litSat_neg]
                exact ⟨hl0, by simpa using hσ⟩
              · exact hlits x hx
          · cases hu'eq
      · simp at h1

/-- **Children unsatisfiable ⇒ parent unsatisfiable**, for a complete case split. -/
theorem split_unsat (F : Formula) (tag : String) (us : List (List Int)) (n : Nat)
    (hcov : coversB n us = true)
    (hchild : ∀ u ∈ us, ∀ σ : Nat → Bool, ¬ ClsSat σ (splitChild F tag u).clauses) :
    ∀ σ : Nat → Bool, ¬ ClsSat σ F.clauses := by
  intro σ hσ
  obtain ⟨u, hu, hlits⟩ := coversB_sound n us hcov σ
  exact hchild u hu σ (splitChild_sat F tag u σ hσ hlits)

/-- Sanity check of the checker on the top-level shape of `split_certify` (all `2^2` patterns). -/
example : coversB 3 [[5, 7], [5, -7], [-5, 7], [-5, -7]] = true := by decide
/-- …and with one recursed child (`[5, 7]` split further on `9`). -/
example : coversB 4 [[5, 7, 9], [5, 7, -9], [5, -7], [-5, 7], [-5, -7]] = true := by decide
/-- A missing pattern is rejected. -/
example : coversB 4 [[5, 7], [5, -7], [-5, 7]] = false := by decide

end SB.Rooted

#print axioms SB.Rooted.split_unsat
