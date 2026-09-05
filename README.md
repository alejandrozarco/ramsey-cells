# ramsey-cells

Colorings for small graph Ramsey cells, with the encoder, an independent checker, and the
scripts that redo the work. Unconfirmed, not peer reviewed. Nothing here is a claim.

| cell | DS1 rev #18 | deposited | |
|---|---|---|---|
| R(K_{2,10}, K_{2,7}) | 29-31 | K_30 | [`k2x10-k2x7-lb31/`](k2x10-k2x7-lb31/) |
| R(K_{2,10}, K_{2,6}) | 27-29 | K_28 | [`k2x10-k2x6-lb29/`](k2x10-k2x6-lb29/) |
| R(K_{2,2}, K_{2,19}) | 28/29 | K_28 | [`k2x2-k2x19-lb29/`](k2x2-k2x19-lb29/) |
| R(K_{2,11}, K_{2,4}) | >= 25 | K_25 | [`k2x11-k2x4-lb26/`](k2x11-k2x4-lb26/) |
| R(K_{2,11}, K_{2,6}) | >= 29 | K_29 | [`k2x11-k2x6-lb30/`](k2x11-k2x6-lb30/) |
| R(K_{3,5}, K_{2,5}) | 21-23 | K_21 + refutation at n=22 | [`k35k25-lb22/`](k35k25-lb22/), [`k35k25-n22/`](k35k25-n22/) |
| R(B_5, B_9) | >= 28 | K_28 | [`b5b9-lb29/`](b5b9-lb29/) |
| R(K_{3,4}, K_{3,3}) | 19-20 | refutation at n=19 | [`k34k33-n19/`](k34k33-n19/) |
| R(K_{3,5}, K_{2,4}) | 19-20 | K_18 + refutation at n=19 | [`k35k24-n19/`](k35k24-n19/) |

A coloring of K_n gives R > n. Checking one needs only the definition of subgraph
containment. The refutation needs more: a faithful encoding, sound symmetry breaking, and an
exhaustive search. Each directory says which parts are machine-checked.

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
