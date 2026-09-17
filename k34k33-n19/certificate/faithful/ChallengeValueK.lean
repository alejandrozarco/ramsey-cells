/-
# Comparator CHALLENGE: R(K_{3,4}, K_{3,3}) = 19, stated about colourings, no native_decide permitted

As `Faithful/ChallengeValue.lean` but the configuration permits only the three standard axioms and
the two cake_lpr verdicts, so the K_18 colouring must be checked by the kernel.
-/
import LRATCatcher.ComparatorAxioms
import Sbsound.Codegree

theorem LRATCatcher.FaithfulC.k34k33_eq_19 :
    (¬ ∃ a : EColouring 19 2, SB.NoKst a 0 3 4 ∧ SB.NoKst a 1 3 3) ∧
    (∃ a : EColouring 18 2, SB.NoKst a 0 3 4 ∧ SB.NoKst a 1 3 3) := sorry
