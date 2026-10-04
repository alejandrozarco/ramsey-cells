# Comparator check of the value, stated about colorings (2026-10-04)

Cell: R(K_{3,5}, K_{2,5}), n = 22. Not a claim, unconfirmed, not peer reviewed.

[Comparator](https://github.com/leanprover/comparator) builds a trusted challenge file and a
solution in a sandbox, exports both, checks that the solution proves the challenge's statements
using only the permitted axioms, and replays the solution in the Lean kernel and, here, also in
nanoda, an independent kernel.

## What was checked

| config | challenge | theorem | permitted axioms | result |
|---|---|---|---|---|
| `faithful-value-k35k25.json` | `ChallengeValueK35K25.lean` | `LRATCatcher.FaithfulK35K25.k35k25_eq_22` | `propext`, `Quot.sound`, `Classical.choice`, `LRATCatcher.Comparator.K35K25.leaves_cakelpr`, `LRATCatcher.Comparator.K35K25.cover_cakelpr` | nanoda and Lean kernel accept (`PASS_faithful-value-k35k25_2026-10-04.log`) |
| `faithful-k35k25.json` | `ChallengeK35K25.lean` | `LRATCatcher.FaithfulK35K25.no_good_colouring_K22` | the same five | nanoda and Lean kernel accept (`PASS_faithful-k35k25_2026-10-04.log`) |

The statement of `k35k25_eq_22`, from `ChallengeValueK35K25.lean`:

```
(¬ ∃ a : EColouring 22 2, SB.NoKst a 0 3 5 ∧ SB.NoKst a 1 2 5) ∧
(∃ a : EColouring 21 2, SB.NoKst a 0 3 5 ∧ SB.NoKst a 1 2 5)
```

`EColouring n 2` maps the edges of K_n (pairs i < j) to two colors. `SB.NoKst a c s t` says
color `c` contains no K_{s,t}: no disjoint vertex sets S, T with |S| = s, |T| = t and every
edge between them colored `c`. Lean's colors 0 and 1 are colors 1 and 2 of the deposited files.
No `native_decide` is permitted, so none is used.

The two named axioms are the ones `../CERTIFICATE_k35k25.md` describes: cake_lpr, the
CakeML-verified LRAT checker, accepted the 137,350 leaf files and the cover file printed from the
Lean terms (`../k35k25_cakelpr_encoder_ledger.jsonl`).

## The solution

`../../lean/FaithfulK35K25Comparator.lean`, without its two `#print axioms` lines (the solution module
was `Faithful.SolutionK35K25`). It combines three pieces:
* `LRATCatcher.Comparator.K35K25.encoded_unsat`, the encoder's formula refuted through the two
  cake_lpr axioms;
* `SB.BipBridge.no_colouring_of_toCNFV_unsat` (`../../../lean/sbsound/`): if the encoder's formula is
  unsatisfiable, no coloring avoids the two patterns (encoding faithfulness and vertex-lex symmetry
  breaking; three standard axioms);
* `SB.Witness21.witness21_kernel` (`../../../lean/sbsound/`): the K_21 coloring of
  `../../../k35k25-lb22/witness/`, checked by `decide +kernel`. The table is read from one natural
  number with `Nat.testBit`; its symmetry is checked on all 441 vertex pairs, and the codegree
  conditions are counted over sorted triples (color 0) and sorted pairs (color 1).

## How it was run

On one Linux machine (x86_64): Lean v4.30.0, comparator 71b52ec, nanoda_lib 68d5ca9,
lean4export v4.30.0 (a3e35a5), landrun, the same tool builds as for `k34k33-n19/certificate/faithful/`. The
workspace was sbsound (identical to `../../../lean/sbsound/` except for comments in `EncoderVendored.lean` and
`Witness18Kernel.lean`, where machine paths were removed for publication) with the lrat-catcher modules behind `encoded_unsat` (`Basic`, `Kernel`,
`Reflect`, `Cover`, `Encoder`, `ComparatorAxiomsK35K25`, `ComparatorCubesK35K25`, `K35K25FlatIcnf0`–`7`,
`ComparatorUnsatK35K25`, byte-identical to `../../../lean/lrat-catcher/`) copied in as a second library
(`lakefile.toml` here). Dependencies were built first; the challenge and solution modules were built by
Comparator. Driver: `run_cmp35.sh`. Wall time 7 min 28 s and 12 min 12 s; peak memory 5.3 GB and 4.9 GB.

In the transcripts the workspace path and the home directory are written `$WORKSPACE` and `$HOME`.
Style lints such as line length carry no meaning for the result.
