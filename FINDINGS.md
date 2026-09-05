# Findings

Everything the search has produced, including the parts that are not deposited and the
parts that turned out to be wrong. Unconfirmed, not peer reviewed. Nothing here is a claim.

Bounds quoted as `DS1` are Radziszowski's dynamic survey *Small Ramsey Numbers*, revision
#18. Its grid tables are complete over their stated ranges; its running text is a selection,
so absence from the prose means nothing.

## 1. Deposited

The nine cells in the [README](README.md) table. Seven are colourings, which need only the
definition of subgraph containment to check. Two pair a colouring with a refutation at the
next order, and those two say in their own directories exactly which parts are machine-
checked and which are argued informally.

Every deposited colouring re-verifies under `tools/check_any.py`, which was written
separately from the encoder and from the three older checkers.

## 2. Computed, deliberately not deposited

Two three-colour cells were recorded here as computed to a verdict. **On 2026-08-29 an audit
of the raw ledgers found that claim wrong for one of them and unproven for the other.** The
corrected statement is below; the original wording is quoted in section 6 so the change is
visible rather than silent.

| cell | DS1 | what the ledgers actually show | standing |
|---|---|---|---|
| R(K_3, K_4-e, K_4-e) | 21-22 | **Coverage audit run 2026-08-29: FAILED.** Against the cube files (3049 level-1 subcubes, not the ledger's own row count) the union of all seven ledgers resolves 3041. Regenerating all 169 split parents found **40 whose recorded children are a strict prefix of the true split — 2353 child cubes never solved** — plus 25 that regenerate fewer children than recorded and cannot be mapped to any reconstructible cube list. The gap was invisible because recorded child indices run contiguously 1..k in all 169 parents: a run killed partway through a child list leaves no hole. The split cubes were written to /tmp and deleted, and march_cu is not build-deterministic across builds, so this ledger cannot be completed into a proof — only re-run with the cubes retained | **not a result** — no refutation, and no witness either (0 SAT) |
| R(C_4, C_4, K_4) | 20-21 | 554 level-1 cubes: **84 UNSAT, 470 TIMEOUT**. Of those 470, **13** were re-split (10,179 children, 279 still timing out). **457 parents were never attempted at any depth** | **not a result** — no refutation, and no witness either (0 SAT) |

The error in the second row was a single word: "554 subcubes" counted the cubes the
decomposition *generated*, not the cubes it *resolved*. About 15% of that search ran. A reader
would have taken the old table to mean the cell was settled at 20 pending certification. It is
not settled at all. **Neither cell should be cited from this repository as a determined
value.**

A reproduction attempt on 2026-08-26 makes the gap concrete rather than hypothetical. With
colour-swap and vertex-lex symmetry breaking, `K_3,K_4-e,K_4-e` at n=21 cubes into 3,779
parts at depth 14; 3,685 were refuted and 94 hit a 600 s cap. Re-splitting a capped part
yields on the order of 900 children that individually run past 110 s, which measures out at
roughly 16 days for that cell and 100 days for `C_4,C_4,K_4` on the hardware in use. Closing
these needs a better decomposition, not more time. Until one exists the cells stay here.

The lower bound 21 for `R(K_3, K_4-e, K_4-e)` is published (Shetler-Wurtz-Radziszowski
2012); the colouring of K_20 verified during this work is theirs, not ours.

## 3. Screened and cleared, not attempted

Cells that passed both gates below and are open as far as we can tell. Listed so the work is
not repeated silently.

| cell | DS1 | why interesting |
|---|---|---|
| R(B_4, B_9) | 27-28 | a K_27 colouring would settle it at 28 |
| R(B_7, B_11) | 37-38 | a K_37 colouring would settle it at 38 |
| R(W_7, C_8) | grid blank | smallest open case of a conjecture in DS1 4.3 |
| R_5(C_4) | 27-29 | one colour class is forced extremal, which collapses the search |

`R(B_4, B_9)` carries real scoop risk: automated search of the book tables is active
elsewhere, and the neighbouring cell `R(B_8, B_10)` was settled in June 2026.

## 4. Ruled out by the literature

A cell is only worth compute if no published source states the value **and** no published
construction mechanism reaches it. The second test is the one that gets skipped, and it cost
ten cells here.

| cells | killed by |
|---|---|
| eight C_4-versus-book cells | Lin-Peng, JGT 103 (2023) 309-322, Lemma 1, combined with the starred values in DS1 Table IVa |
| R(B_8, B_10) | Kalfus-Lidicky, 2026 |
| R(K_7, K_4-e) | Wesley, arXiv:2606.17021, which settles it at 28 after DS1 rev #18 went to press |

Two further routes were closed without a paper. First, enumerating every feasible strongly
regular parameter set on 26, 28 and 30 vertices shows none reaches the K_{2,n} cells above --
the relevant construction in DS1 5.3(l) cannot get there. (An earlier note here claimed no
such graph exists on those orders at all, which is false: T(8) is SRG(28,12,6,4). The
parameter sets exist; they just do not land on these cells.) Second, algebraic constructions
of Cayley/cyclotomic type are subsets of circulants, and circulants were already enumerated
exhaustively for these cells by Van Overberghe -- which is precisely why the colourings
deposited here are non-circulant. A direct sweep of symmetric cyclotomic connection sets at
every prime order in range returned nothing, consistent with that argument.

Relatedly, prescribing a non-cyclic group is provably redundant: invariance under a group
implies invariance under each of its generators, so sweeping single-generator cycle types
already covers every group-invariant colouring.

## 5. Searches that found nothing

Null results, recorded because they are the bulk of the work and because an unrecorded null
gets repeated.

- Prescribed-automorphism sweeps for `R(K_{3,5}, K_{3,4})` at n=25 and `R(K_{3,5}, K_{3,3})`
  at n=21: several hundred cycle types refuted, no colouring.
- A defect/free-set sweep over 702 cycle types for the book cell `R(B_5, B_9)` at n=29.
- Twenty-two encoding and search variations benchmarked against this instance family; one
  showed a possible speedup (a degree-regularity streamliner, ~1.8x on a single measurement,
  unreplicated, and no gain at all on the open cell where it would have mattered). A separate
  screen of twenty solver-level levers found none that survived scrutiny: `--factor=true`, for
  instance, is 11-16% *slower* on the unsatisfiable instances that dominate the workload.

## 6. Corrections

Defects found in this repository's own tooling, listed because the results above were
produced by it and a reader should know what was wrong and for how long.

**A checker verified the wrong property.** `tools/check_mixed.py` matched `K_sxt` by regular
expression and fell through to a book reading for everything else, so the token `K3` was
parsed as `int("3")` and checked as the book B_3 rather than as a triangle. No deposited
result depended on the fallthrough — every deposited spec is bipartite or a book — but the
failure mode is the dangerous one, because a checker that silently answers a different
question still prints `VALID`. The fallthrough is now a hard error, and
`tools/check_any.py` supersedes it: it handles any number of colours, takes bipartite and
book cells by codegree and cliques, cycles, wheels and K_4-e by injective embedding, and
refuses an unrecognised token instead of guessing.

**A search recorded crashes as timeouts.** The sweep driver shared one parsed formula
between worker threads and published its clause count and its body to globals under a lock,
then read them back outside it. Two workers on different cycle types could therefore pair
one type's header with another's body; the solver rejected the mismatch in a fraction of a
second, and because the driver's verdict logic treated "no answer" as a timeout, the crash
was logged as a hard instance. Six such rows appeared in one sweep. Header and body are now
captured together, and a timeout is recorded only when the timeout actually fires.

**A search could not report success.** The same driver decoded models on the assumption of
two colours and bipartite graph names. A three-colour or book search would therefore raise
an exception at the moment it found a colouring — the one path that had never been exercised,
because these searches almost always end in refutation. Model decoding now follows the
encoder's own variable convention for any number of colours, and every witness is verified by
an independent checker before it is written.

**A search that was ~15% finished was recorded as a completed refutation.** Until 2026-08-29
the table in section 2 read `R(C_4, C_4, K_4) | 20-21 | UNSAT at n=20, 554 subcubes`. The
ledger behind it (`c4c4k4_sweep_ledger.BROKEN.jsonl` — and the `.BROKEN` suffix was itself a
clue nobody followed) records 84 UNSAT and 470 TIMEOUT over those 554 cubes, with 457 of the
timed-out parents never re-split at any depth. The summary counted generated cubes as if they
were resolved ones. Nothing downstream depended on it — the cell was never deposited and no
other result cites it — but it stood here as a computed verdict for three days, and it is the
same failure this section already documents twice: work that did not finish, wearing the
costume of work that did. The registry entry asserting `=20` now reads `NOT ESTABLISHED`.

**Prescribed-automorphism sweeps are not exhaustive.** The cycle types enumerated cover
elements whose order divides a fixed list. That misses every automorphism of prime order
outside the list, including all involutions at n=21. A sweep that refutes every enumerated
type therefore shows that no colouring exists *with one of those symmetries* — it is search
evidence, and it is not a refutation. Nothing deposited here rests on such a sweep.

Since 2026-08-28 the enumeration can be made complete. By Cauchy's theorem every nontrivial
finite group contains an element of prime order, so sweeping every prime-order cycle type
covers every colouring with any nontrivial automorphism. The complete cover is also *smaller*
than the ad-hoc list it replaces — 26 types against 120 at n=20 — because composite orders are
redundant once their prime divisors are swept. A sweep that resolves every prime-order type
does license the stronger statement. Resolving them all is now the binding constraint: the
cells tried so far still leave roughly a third of their types at the time cap.

## 7. Method

`R(G, H) > n` is witnessed by a colouring of K_n avoiding G in colour 1 and H in colour 2;
checking one is direct. `R(G, H) <= n` needs the absence of any such colouring, which is a
refutation over the whole space and is the expensive half by a wide margin.

Bipartite and book constraints are encoded by codegree rather than by enumerating copies:
K_{s,t} is present exactly when some s-set has t common neighbours, and the book B_t exactly
when some *edge* has t common neighbours. The gate on the spine edge is what separates the
two; without it the book encoding silently becomes a K_{2,t} encoding.

Colourings are found by prescribing an automorphism: fix a permutation's cycle type, force
the colouring to be invariant under it, and solve on edge orbits instead of edges. This
shrinks instances several-fold and is why the deposited colourings were findable at all. It
also biases the search toward symmetric colourings, which is why a null sweep proves nothing.

Refutations are cube-and-conquer: split the formula into cubes, refute each, and separately
certify that the cubes cover everything. That last step is not optional — the coverage
certificate, not the splitter's internal behaviour, is what makes the decomposition a proof.


## 2026-09-05

* `k35k25-n22/`: a cube-and-conquer search at n = 22 for R(K_{3,5}, K_{2,5}) finished with every
  leaf UNSAT and every proof checked (137,350 leaves; cover audited against the cube files;
  0 SAT). With the K_21 coloring in `k35k25-lb22/`, the value would be 22. The re-derivation of
  the leaf verdicts by cake_lpr was in progress at commit time (`certificate/cake_lpr_ledger_IN_PROGRESS.jsonl`).
* `k34k33-n19/certificate/`, `k35k24-n19/certificate/`: the two n = 19 refutations now carry
  Comparator transcripts and complete cake_lpr ledgers (572/572 and 774/774 files verified).
  `k35k24-n19`'s search was re-run with per-leaf proof checking on 2026-09-04 because the cube
  files of the 2026-08-20 run had not been retained.
* The published lower bound R(K_{2,5}, K_{3,5}) >= 20 (Ghebleh, Al-Yakoob, Kanso, Stevanović,
  arXiv:2403.20055, 2024) is the most recent prior work found on this cell.
