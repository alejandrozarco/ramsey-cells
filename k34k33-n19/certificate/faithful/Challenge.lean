/-
# Comparator CHALLENGE: R(K_{3,4}, K_{3,3}) <= 19, stated about colourings

The trusted file. `EColouring 19 2` is a map from the edges of K_19 (pairs i < j) to two colours;
`SB.NoKst a c s t` says colour c contains no K_{s,t}: no disjoint vertex sets S, T with |S| = s,
|T| = t and every S-T edge coloured c. Both are defined in lean-sb (`Sbsound/SBGraph.lean`,
`Sbsound/Codegree.lean`), imported here.

`LRATCatcher.ComparatorAxioms` is imported so that the two external cake_lpr verdicts the solution
may use are declared on this side, where Comparator reads the permitted axioms from.
-/
import LRATCatcher.ComparatorAxioms
import Sbsound.Codegree

theorem LRATCatcher.FaithfulC.no_good_colouring_K19 :
    ¬ ∃ a : EColouring 19 2, SB.NoKst a 0 3 4 ∧ SB.NoKst a 1 3 3 := sorry
