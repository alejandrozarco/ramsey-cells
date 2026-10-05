/-
# Comparator CHALLENGE: R(K_{3,5}, K_{2,4}) = 19, stated about colourings

`EColouring n 2` maps the edges of K_n (pairs i < j) to two colours; `SB.NoKst a c s t` says colour c contains
no K_{s,t}. Both are defined in lean-sb (`Sbsound/SBGraph.lean`, `Sbsound/Codegree.lean`), imported here.
`LRATCatcher.ComparatorAxiomsK35K24` declares the two external cake_lpr verdicts the solution may use.
-/
import LRATCatcher.ComparatorAxiomsK35K24
import Sbsound.Codegree

theorem LRATCatcher.FaithfulK35K24.k35k24_eq_19 :
    (¬ ∃ a : EColouring 19 2, SB.NoKst a 0 3 5 ∧ SB.NoKst a 1 2 4) ∧
    (∃ a : EColouring 18 2, SB.NoKst a 0 3 5 ∧ SB.NoKst a 1 2 4) := sorry
