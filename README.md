# ramsey-cells

Colorings for small graph Ramsey cells, with the encoder, an independent checker, and the
scripts that redo the work.

Status: **computation records, not peer reviewed.** Unconfirmed; nothing here is a claim.
**Produced by AI models** under the direction of the repository owner; see
[`AI_DISCLOSURE.md`](AI_DISCLOSURE.md).

> [!IMPORTANT]
> This repository is a public, timestamped, AI-produced **warrant** for the Ramsey-number verdicts stated in
> the table below (bounds from the Dynamic Survey DS1, revision 18): machine-checked certificates that no human
> has yet digested. We do not regard the questions as settled by it. Independent verification and
> human-readable expositions are welcome, and credit for a human-readable proof belongs to whoever writes one.
> To refer to the computational results, please cite this repository (no archived release yet). Questions,
> checks and corrections: [GitHub issues](https://github.com/alejandrozarco/ramsey-cells/issues).

| cell | DS1 rev #18 | deposited | |
|---|---|---|---|
| R(K_{2,10}, K_{2,7}) | 29-31 | K_30 | [`k2x10-k2x7-lb31/`](k2x10-k2x7-lb31/) |
| R(K_{2,10}, K_{2,6}) | 27-29 | K_28 | [`k2x10-k2x6-lb29/`](k2x10-k2x6-lb29/) |
| R(K_{2,2}, K_{2,19}) | 28/29 | K_28 | [`k2x2-k2x19-lb29/`](k2x2-k2x19-lb29/) |
| R(K_{2,11}, K_{2,4}) | >= 25 | K_25 + refutation at n=26 | [`k2x11-k2x4-lb26/`](k2x11-k2x4-lb26/), [`k211k24-n26/`](k211k24-n26/) |
| R(K_{2,11}, K_{2,6}) | >= 29 | K_29 | [`k2x11-k2x6-lb30/`](k2x11-k2x6-lb30/) |
| R(K_{3,5}, K_{2,5}) | 21-23 | K_21 + refutation at n=22 | [`k35k25-lb22/`](k35k25-lb22/), [`k35k25-n22/`](k35k25-n22/) |
| R(B_5, B_9) | >= 28 | K_28 | [`b5b9-lb29/`](b5b9-lb29/) |
| R(K_{3,4}, K_{3,3}) | 19-20 | refutation at n=19 | [`k34k33-n19/`](k34k33-n19/) |
| R(K_{2,8}, K_{2,5}) | 22-23 | K_21 + rooted census at n=22, complete as a computation; verification in progress (see its README) | [`k28k25-n22/`](k28k25-n22/) |
| R(K_{3,5}, K_{2,4}) | 19-20 | K_18 + refutation at n=19 | [`k35k24-n19/`](k35k24-n19/) |
| R(K_{2,11}, K_{2,3}) | >= 22 | refutation at n=22 | [`k211k23-n22/`](k211k23-n22/) |
| R(K_{3,5}, K_{3,3}) | 21-24 | refutation at n=21 (SMS-clause formula; one grade below the other refutations, see its README) | [`k35k33-n21/`](k35k33-n21/) |
| R(K_{2,11}, K_{2,5}) | >= 28 | K_27 (reproduces the published lower bound); the upper bound 28 is Lortz-Mengersen's lemmas evaluated, so the value follows from published work and is not new | [`k211k25-n28/`](k211k25-n28/) |
| R(K_{2,n}, K_{2,m}), n = 12..15 | not tabulated | 21 colourings over 20 cells; four of them meet the published upper bound | [`k2-rows-12-15/`](k2-rows-12-15/) |

Start with [VERIFY.md](VERIFY.md) for the shortest path to checking the two strongest results.

A coloring of K_n gives R > n. Checking one needs only the definition of subgraph
containment. The refutation needs more: a faithful encoding, sound symmetry breaking, and an
exhaustive search. Each directory says which parts are machine-checked. For
R(K_{3,4}, K_{3,3}) = 19, R(K_{3,5}, K_{2,5}) = 22, R(K_{2,11}, K_{2,4}) = 26, R(K_{2,11}, K_{2,3}) = 22 and
R(K_{3,5}, K_{2,4}) = 19 all three are composed into one Lean theorem about colorings, checked by
Comparator (each cell's `certificate/faithful/`); the encoding and symmetry-breaking step is
[`lean/sbsound/`](lean/sbsound/).

[`REVIEWER.md`](REVIEWER.md) says how to check each kind of entry, with the tool versions used.

[`FINDINGS.md`](FINDINGS.md) is the complete record: what is deposited, two three-colour
cells computed to a verdict but held back because they do not meet the bar set here, cells
screened and left open, cells ruled out by published work, searches that found nothing, and
the defects since found in this repository's own tooling.

See [`NOTICE.md`](NOTICE.md) — the K_18 coloring in `k34k33-n19/` is Van Overberghe's.

## Check

```
python3 tools/check_ramsey.py k2x10-k2x7-lb31/witness/witness_k2x10k2x7_n30.txt K2x10,K2x7
```

Or open `bench.html` and paste any coloring. It shares no code with the encoder.

`tools/` has four checkers, each written from the definitions: `check_any.py`
(any number of colors; bipartite and books by codegree, cliques/cycles/wheels/K_4-e by
embedding; an unrecognized token is an error, never a guess), and the three older ones it
supersedes -- `check_ramsey.py` (complete bipartite and cliques), `check_book.py` (books
B_t), `check_mixed.py` (both). Every coloring above verifies under `check_any.py` as well as
under the checker it was originally accepted by. See FINDINGS.md section 6 for why
`check_mixed.py` was superseded.

Each witness declares its own parameters:

```
# spec: K3x5,K2x5
# name: K(3,5)/K(2,5) on K21
```

`python3 tools/gen_views.py` regenerates every matrix, SVG and `bench.html` from the
witnesses. The witnesses are the artifacts; everything else is derived.
