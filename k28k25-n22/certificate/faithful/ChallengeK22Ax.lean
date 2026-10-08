/-
# Comparator challenge module for the 2003 cell (wrapper)

`Faithful.ChallengeK22` is `ramsey-cells/k28k25-n22/statement/ChallengeK22.lean`, byte-identical (sha256
ba92cca24659ec5e2d1525cca8f02b3dc027f2019953ae02f9a5dfebbcf35029). It imports only `Sbsound.Codegree`,
so the named cake_lpr verdicts that its own comment permits ("declared on the challenge side") are
brought in here, as in the K_19 and K_22 (K35K25) challenges:
* `RootedM4.CoverAxiom`: `SB.Rooted.M4.CoverData.cover_cakelpr` (53 H-cover CNFs);
* `RootedM5.Axioms`: `SB.Rooted.M5.direct_cakelpr`, `SB.Rooted.M5.leaves_cakelpr` (census cubes).
Nothing else is declared here.
-/
import Faithful.ChallengeK22
import RootedM4.CoverAxiom
import RootedM5.Axioms
