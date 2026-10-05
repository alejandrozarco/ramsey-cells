/-
# Comparator CHALLENGE: R(K_{2,11}, K_{2,3}) = 22, stated about colourings

`EColouring n 2` maps the edges of K_n (pairs i < j) to two colours; `SB.NoKst a c s t` says colour c contains
no K_{s,t}. Both are defined in lean-sb (`Sbsound/SBGraph.lean`, `Sbsound/Codegree.lean`), imported here.
`LRATCatcher.ComparatorAxiomsK211K23` declares the two external cake_lpr verdicts the solution may use.
-/
import LRATCatcher.ComparatorAxiomsK211K23
import Sbsound.Codegree

theorem LRATCatcher.FaithfulK211K23.k211k23_eq_22 :
    (¬ ∃ a : EColouring 22 2, SB.NoKst a 0 2 11 ∧ SB.NoKst a 1 2 3) ∧
    (∃ a : EColouring 21 2, SB.NoKst a 0 2 11 ∧ SB.NoKst a 1 2 3) := sorry
