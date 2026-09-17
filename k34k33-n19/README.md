# K(3,4) / K(3,3) at n = 19

Forbidden here: **K_{3,4} in color 1, K_{3,3} in color 2**.

Inputs and outputs of a computation, deposited so it can be repeated. Not a claim,
unconfirmed, not peer reviewed.

DS1 rev #18, Table IVb, row 3,4 column 3,3: `19-20`. A K_{3,4}/K_{3,3}-free coloring of
K_18 gives R > 18; unsatisfiability at n = 19 gives R <= 19. Together, 19.

`lean/Encoder.lean` writes the encoding of `tools/gen_ramsey.py` in Lean and
`lean/EncoderBridge.lean` checks it against `instance/k34k33_n19.cnf` by evaluation.
`lean/FaithfulK34K33.lean` (added 2026-09-16) states the value itself as one Lean theorem
about colorings, and `lean/FaithfulK34K33Comparator.lean` (2026-09-17) proves the same theorem
without `native_decide`, checked by Comparator; see [Scope](#scope) for what that covers and what
it still leaves out.

## The K_18 coloring is not ours

`witness/witness_k34k33_n18.txt` is Steven Van Overberghe's published construction,
byte-equivalent to `K(3,4)K(3,3)n18.g6` in
<https://github.com/Steven-VO/circulant-Ramsey> (that repository is GPL-3.0), cited in
DS1 as [VO]. It is
here so the lower bound can be checked beside the upper-bound computation, which is the
part done here.

<!-- svg:start -->
<img src="witness/coloring.svg" alt="adjacency matrix of the coloring of K_18" width="100%">

Left, vertices in their original order 1..18. Right, the same coloring with vertices grouped by the orbits of a recovered automorphism (2+2+2+2+2+2+2+2+1+1); white rules mark the orbit boundaries. Relabeling never changes an edge's color.
<!-- svg:end -->

<details><summary>the same grid as text</summary>

<!-- matrix:start -->
```
     1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 
   1 ▒▒████░░░░░░░░████████░░██░░████░░░░
   2 ██▒▒████░░░░░░░░██░░████░░██░░████░░
   3 ████▒▒████░░░░░░░░░░░░████░░██░░████
   4 ░░████▒▒████░░░░░░██░░░░████░░██░░██
   5 ░░░░████▒▒████░░░░████░░░░████░░██░░
   6 ░░░░░░████▒▒████░░░░████░░░░████░░██
   7 ░░░░░░░░████▒▒██████░░████░░░░████░░
   8 ██░░░░░░░░████▒▒██░░██░░████░░░░████
   9 ████░░░░░░░░████▒▒██░░██░░████░░░░██
  10 ██░░░░████░░██░░██▒▒░░░░████████░░░░
  11 ████░░░░████░░██░░░░▒▒░░░░████████░░
  12 ░░████░░░░████░░██░░░░▒▒░░░░████████
  13 ██░░████░░░░████░░██░░░░▒▒░░░░██████
  14 ░░██░░████░░░░████████░░░░▒▒░░░░████
  15 ██░░██░░████░░░░████████░░░░▒▒░░░░██
  16 ████░░██░░████░░░░████████░░░░▒▒░░░░
  17 ░░████░░██░░████░░░░████████░░░░▒▒░░
  18 ░░░░████░░██░░████░░░░████████░░░░▒▒
```
<!-- matrix:end -->

</details>

## The upper bound

`instance/k34k33_n19.cnf`, from `tools/gen_ramsey.py`, is intended to be satisfiable
exactly when a K_{3,4}/K_{3,3}-free coloring of K_19 exists, and carries static vertex-lex
symmetry-breaking clauses. It was split into the 571 cubes of
`instance/k34k33_n19_d10.icnf`; CaDiCaL reported every one unsatisfiable and `lrat-check`
accepted every certificate. `instance/cover.lrat` refutes the conjunction of the negated
cubes, so the cubes leave no assignment uncovered. The refutations compose into a Lean 4
theorem `base_unsat : base.Unsat`, where `base` is the DIMACS text of the shipped CNF
embedded in the statement:

```
sha256(instance/k34k33_n19.cnf) = 6a889aa40e0144c8d88b630dd4bc087430e4e719f845566142c53a4440fb8b66
```

The string embedded in the Lean statement hashes to the same value.

The proof itself cannot be shipped: the 571 certificates are about 12 GB and the Lean chunk
modules about 16 GB. Here instead are the statement (`lean/Base.lean`), the composition
(`lean/Main.lean`), the exhaustiveness theorem (`lean/Cover.lean`), one leaf module, one
subcube certificate (`sample/`), the per-cube verdicts (`ledger/`), `reconstruct.sh`,
which regenerates and re-checks every certificate in roughly 2.4 CPU-hours, and
`lean/rebuild.sh`, which goes further and rebuilds the Lean theorem itself.

## Scope

Machine-checked: each of the 571 cubes is unsatisfiable; the decomposition is exhaustive;
`base_unsat` holds in Lean.

**Update 2026-09-16: the encoding step is machine-checked as well.** Until then this section
said that the link from the formula to colorings was argued informally. One Lean theorem,
`LRATCatcher.Faithful.k34k33_eq_19` in `lean/FaithfulK34K33.lean`, now states the result
about colorings instead of about a formula:

```
(¬ ∃ a : EColouring 19 2, NoKst a 0 3 4 ∧ NoKst a 1 3 3) ∧
(∃ a : EColouring 18 2, NoKst a 0 3 4 ∧ NoKst a 1 3 3)
```

`NoKst a c s t` says that color `c` contains no K_{s,t}: there are no disjoint vertex sets S
and T with |S| = s, |T| = t and every edge between them colored `c`. Lean's colors 0 and 1
are colors 1 and 2 on this page. The proof puts together three pieces:

* `encoded_unsat` (`lean/EncodedUnsat.lean`): the formula built by the Lean encoder is
  unsatisfiable, by `encode_eq_base` and `base_unsat` above.
* A bridge theorem: for all n, s0, t0, s1, t1 with s + 2 <= n and t >= 2, if the encoder's
  formula is unsatisfiable then no coloring of K_n avoids K_{s0,t0} in color 0 and
  K_{s1,t1} in color 1. It works by showing that any such coloring has a relabeling that
  satisfies the formula, so it covers the Sinz counter layer (105,213 variables, of which
  342 are edge variables) and the vertex-lex symmetry-breaking clauses. Its own axioms are
  `propext`, `Classical.choice` and `Quot.sound` only.
* The K_18 coloring of `witness/`, checked in Lean by evaluation. It is the same coloring
  as the deposited file, all 153 edge colors under the same vertex labels.

The `#print axioms` output is in `AXIOMS_FAITHFUL.txt`: `propext`, `Classical.choice`,
`Quot.sound`, and 575 `native_decide` axioms (the 571 chunks, `coverThm`,
`encode_eq_clauses`, and two for the K_18 coloring). There is no `sorryAx` and no other
axiom. The theorem was compiled once, on 2026-09-16 (Lean 4.30.0, aarch64 Linux), against
all 574 generated modules rebuilt from the archived sources, each hash-checked before use;
`Base`, `Cover`, `Main` and `Chunk232` are byte-identical to the copies in `lean/`. The
lrat-catcher `Encoder.lean` used is the snapshot in `../lean/lrat-catcher/`, which extends
`lean/Encoder.lean` with later cells; `lean/FaithfulK34K33.lean` proves its `encodeBip` equal
to a verbatim copy of the one in `lean/Encoder.lean`.

What this still leaves outside Lean: the kernel and, through `native_decide`, the Lean
compiler; and a reading of `NoKst` against the definition of R(K_{3,4}, K_{3,3}). Only the
direction the upper bound needs is proved (a good coloring would satisfy the formula), not
the converse.

The bridge is part of a separate Lean development, `sbsound`, whose sources are not in this
repository (`../REVIEWER.md`, section 5). `lean/FaithfulK34K33.lean` can be read here, but
it cannot yet be rebuilt from this repository alone.

`native_decide` puts the Lean compiler in the trusted base alongside the kernel. One
implementation, one run, not independently re-derived.

**Update 2026-09-17: the same value without `native_decide`, checked by Comparator.**
`lean/FaithfulK34K33Comparator.lean` proves `k34k33_eq_19` (same statement) from two
different pieces:

* `encoded_unsat` is taken from `certificate/`, where it rests on two named axioms,
  `leaves_cakelpr` and `cover_cakelpr`. Each stands for a verdict of cake_lpr, the
  CakeML-verified LRAT checker, on files printed from the Lean terms (`certificate/CERTIFICATE.md`).
  This replaces the 573 `native_decide` uses above.
* The K_18 coloring is checked by `decide +kernel` instead of `native_decide`: the table is read
  from one natural number and proved equal to it on all 324 vertex pairs.

Comparator accepted `k34k33_eq_19` with permitted axioms `propext`, `Quot.sound`,
`Classical.choice`, `leaves_cakelpr` and `cover_cakelpr` only. Both the Lean kernel and nanoda,
an independent kernel, accepted the replay (`certificate/faithful/`, which also holds the
challenge files, configurations and transcripts). For that statement the trusted base is the
kernel (either one), cake_lpr's checker, the printer and cube list behind the files cake_lpr
read, Comparator's own tooling, and a reading of the challenge statement. The bridge and the
kernel witness are in `sbsound`, so this run also cannot yet be repeated from this repository
alone.

## Files

| path | what |
|---|---|
| `witness/` | the K_18 coloring (Van Overberghe's) and its matrix |
| `instance/` | the formula, its 571-cube decomposition, the cover certificate |
| `lean/` | statement, cover theorem, composing module, one leaf module |
| `sample/leaf1.lrat` | one subcube's certificate, checkable alone |
| `ledger/` | per-cube result, certificate size, `verified` |
| `AXIOMS.txt`, `LEAN.md` | axiom output; how to rebuild the theorem |
| `lean/FaithfulK34K33.lean`, `AXIOMS_FAITHFUL.txt` | the value as one theorem about colorings, and its axiom output |
| `certificate/` | a check of `encoded_unsat` by Comparator and cake_lpr, without `native_decide` |
| `lean/FaithfulK34K33Comparator.lean`, `certificate/faithful/` | the value without `native_decide`; its Comparator check |
| `lean/rebuild.sh` | rebuilds the theorem from this repository, end to end |
| `tools/` | encoder, and a checker sharing no code with it |
| `reconstruct.sh`, `SHA256SUMS` | redo the computation; checksums |
