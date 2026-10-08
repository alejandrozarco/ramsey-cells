# Comparator check of the value, stated about colorings (2026-10-08)

Cell: R(K_{2,8}, K_{2,5}), n = 22. Not a claim, unconfirmed, not peer reviewed.

Same method and tool builds as `../../../k35k25-n22/certificate/faithful/` (see its README for what
Comparator does).

## What was checked

| config | challenge | theorem | permitted axioms | result |
|---|---|---|---|---|
| `faithful-value-k28k25.json` | `ChallengeK22Ax.lean` (imports `../../statement/ChallengeK22.lean`) | `LRATCatcher.FaithfulC.k28k25_eq_22` | `propext`, `Quot.sound`, `Classical.choice`, `SB.Rooted.M4.CoverData.cover_cakelpr`, `SB.Rooted.M5.direct_cakelpr`, `SB.Rooted.M5.leaves_cakelpr` | nanoda and Lean kernel accept (`PASS_faithful-value-k28k25_2026-10-08.log`) |
| `faithful-k28k25.json` | the same | `LRATCatcher.FaithfulC.no_good_colouring_K22` | the same six | not run separately |

Only the value configuration was run. Its theorem `k28k25_eq_22` is the conjunction of
`no_good_colouring_K22` and the K_21 witness, and the challenge module declares both statements, so the
transcript covers the refutation as well; `faithful-k28k25.json` is deposited for anyone who wants to run
the refutation alone.

The challenge is the statement fixed on 2026-09-27, `../../statement/ChallengeK22.lean` (sha256
`ba92cca24659ec5e2d1525cca8f02b3dc027f2019953ae02f9a5dfebbcf35029`), unchanged. It imports only
`Sbsound.Codegree`. Comparator looks up every permitted axiom in the challenge environment, so
`ChallengeK22Ax.lean` imports the fixed file together with the two modules that declare the named axioms
(`RootedM4.CoverAxiom`, `RootedM5.Axioms` in `../../../lean/sbsound/`) and declares nothing itself. The
statements:

```
theorem no_good_colouring_K22 :
    ¬ ∃ a : EColouring 22 2, SB.NoKst a 0 2 8 ∧ SB.NoKst a 1 2 5
theorem k28k25_eq_22 :
    (¬ ∃ a : EColouring 22 2, SB.NoKst a 0 2 8 ∧ SB.NoKst a 1 2 5) ∧
    (∃ a : EColouring 21 2, SB.NoKst a 0 2 8 ∧ SB.NoKst a 1 2 5)
```

`EColouring n 2` maps the edges of K_n (pairs i < j) to two colors; `SB.NoKst a c s t` says color `c`
contains no K_{s,t}. Lean's colors 0 and 1 are colors 1 and 2 of the deposited files. No `native_decide`
is permitted, so none is used.

The three named axioms (exact statements in `../../../lean/sbsound/RootedM4/CoverAxiom.lean` and
`RootedM5/Axioms.lean`):

* `cover_cakelpr`: the 53 H-cover CNFs `famCNF fc`, `fc ∈ allCerts`, are unsatisfiable;
* `direct_cakelpr`: for every table row with verdict `direct` (22,457 cubes), the rooted encoder's formula
  `Row.clauses r` is unsatisfiable;
* `leaves_cakelpr`: for every table row with verdict `split` (1,429 cubes) and every leaf `u` of its split
  (126,351 leaves), `Row.leafClauses r t u` is unsatisfiable.

Each stands for cake_lpr (CakeML-verified LRAT checker) verdicts on files printed from these Lean terms:
see `../../README.md`, sections *Coverage* and *Binding of the verdicts to the Lean terms*. If the encoder
returned an error on some row, its clause list would be empty, the empty CNF is satisfiable, and the axiom
would be refutable rather than vacuous.

## The solution

`../../lean/FaithfulK28K25Comparator.lean`, without its two `#print axioms` lines (the solution module
was `Faithful.SolutionK28K25`). It combines
* `SB.Rooted.M5.no_good_K22_of_pending'` (`RootedM5/Close.lean`), which rests on the census lemmas
  (`RootedLemmas/`, `Lemma12.lean`), the encoder soundness bridge (`RootedBridge/`), the canonical form
  and H-cover (`RootedM4/`), the kernel checks of the cube table (`RootedM5/Checks`, `RootedM5/Keys`) and the
  three named axioms;
* `SB.Rooted.M5.no_pending` (`RootedM5/Attached.lean`): no row of the table is pending (`decide +kernel`);
* `SB.Witness21K28.witness_kernel` (`RootedM5/Witness21.lean`): the K_21 coloring of `../../witness/`
  (sha256 `49984dbd…`), checked by `decide +kernel`.

`#print axioms` for both theorems (`../../runs/k28_rooted/m5_final/print_axioms_FaithfulK28K25Comparator.txt`):
`propext`, `Classical.choice`, `Quot.sound`, `SB.Rooted.M5.direct_cakelpr`, `SB.Rooted.M5.leaves_cakelpr`,
`SB.Rooted.M4.CoverData.cover_cakelpr`.

## How it was run

On one Linux machine (x86_64), 2026-10-08 02:29:09Z to 05:16:17Z, return code 0: Lean v4.30.0,
comparator 71b52ec, nanoda_lib 68d5ca9, lean4export v4.30.0 (a3e35a5), landrun, the same tool builds as for
`../../../k35k25-n22/certificate/faithful/`. Driver: `run_cmp28.sh` (holds a lock file, waits for free
memory, runs Comparator under `nice` and `/usr/bin/time -v`). Comparator wall time 2 h 47 min, peak memory
6.6 GB.

The workspace was the development that is published as `../../../lean/sbsound/` (Mathlib v4.30.0,
`lake-manifest.json` as there), with `lakefile.toml` here (the one of `lean/sbsound/` plus the library
`Faithful`), and
* `Faithful/ChallengeK22.lean` = `../../statement/ChallengeK22.lean` (byte-identical),
  `Faithful/ChallengeK22Ax.lean` = `ChallengeK22Ax.lean` here,
  `Faithful/SolutionK28K25.lean` = `../../lean/FaithfulK28K25Comparator.lean` without the two `#print axioms` lines;
* `Comparator/k28k25/faithful-value-k28k25.json`, `faithful-k28k25.json` = the two files here.

The 365 Lean files in the import closure of the challenge and the solution, and the printer
`RootedM5Print.lean`, had the same sha256 on the run machine as in the source commit. The published copies in
`../../../lean/sbsound/` are byte-identical to them except for comments in three files, where machine paths and a
host name were removed for publication: `Lemma12.lean`, `RootedM5/FamDefs.lean` (this deposit) and
`Sbsound/EncoderVendored.lean` (as published earlier). `LRATCatcher/RootedEncoder.lean` is byte-identical to
`../../../lean/lrat-catcher/LRATCatcher/RootedEncoder.lean`.
The workspace also held further `Sbsound` modules that are outside the import closure.

In the transcript the workspace path and the home directory are written `$WORKSPACE` and `$HOME`.
Style lints such as line length carry no meaning for the result.
