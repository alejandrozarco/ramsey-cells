/-
# Comparator CHALLENGE: R(K_{3,5}, K_{2,5}) = 22, stated about colourings

No good colouring of K_22, and a good colouring of K_21. Same vocabulary and the same two permitted
external cake_lpr verdicts as `ChallengeK35K25.lean`; the K_21 colouring must be checked by the kernel.
-/
import LRATCatcher.ComparatorAxiomsK35K25
import Sbsound.Codegree

theorem LRATCatcher.FaithfulK35K25.k35k25_eq_22 :
    (¬ ∃ a : EColouring 22 2, SB.NoKst a 0 3 5 ∧ SB.NoKst a 1 2 5) ∧
    (∃ a : EColouring 21 2, SB.NoKst a 0 3 5 ∧ SB.NoKst a 1 2 5) := sorry
