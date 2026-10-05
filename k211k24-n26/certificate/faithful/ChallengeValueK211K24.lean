/-
# Comparator CHALLENGE: R(K_{2,11}, K_{2,4}) = 26, stated about colourings

`EColouring n 2` maps the edges of K_n (pairs i < j) to two colours; `SB.NoKst a c s t` says colour c contains
no K_{s,t}. Both are defined in lean-sb (`Sbsound/SBGraph.lean`, `Sbsound/Codegree.lean`), imported here.
`LRATCatcher.ComparatorAxiomsK211K24` declares the two external cake_lpr verdicts the solution may use.
-/
import LRATCatcher.ComparatorAxiomsK211K24
import Sbsound.Codegree

theorem LRATCatcher.FaithfulK211K24.k211k24_eq_26 :
    (¬ ∃ a : EColouring 26 2, SB.NoKst a 0 2 11 ∧ SB.NoKst a 1 2 4) ∧
    (∃ a : EColouring 25 2, SB.NoKst a 0 2 11 ∧ SB.NoKst a 1 2 4) := sorry
