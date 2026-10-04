/-
# Comparator CHALLENGE: R(K_{3,5}, K_{2,5}) <= 22, stated about colourings

The trusted file. `EColouring 22 2` is a map from the edges of K_22 (pairs i < j) to two colours;
`SB.NoKst a c s t` says colour c contains no K_{s,t}: no disjoint vertex sets S, T with |S| = s,
|T| = t and every S-T edge coloured c. Both are defined in lean-sb (`Sbsound/SBGraph.lean`,
`Sbsound/Codegree.lean`), imported here.

`LRATCatcher.ComparatorAxiomsK35K25` is imported so that the two external cake_lpr verdicts the solution
may use are declared on this side, where Comparator reads the permitted axioms from.
-/
import LRATCatcher.ComparatorAxiomsK35K25
import Sbsound.Codegree

theorem LRATCatcher.FaithfulK35K25.no_good_colouring_K22 :
    ¬ ∃ a : EColouring 22 2, SB.NoKst a 0 3 5 ∧ SB.NoKst a 1 2 5 := sorry
