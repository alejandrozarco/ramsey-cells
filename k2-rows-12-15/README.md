# R(K(2,n), K(2,m)) for n = 12..15: twenty cells outside the survey table

Unconfirmed, not peer reviewed. Nothing here is a claim.

Radziszowski's dynamic survey tabulates R(K_{2,n}, K_{2,m}) only for n <= 11 (DS1 rev #18, Table IVc), and Van
Overberghe's circulant repository stops at K_{2,11}. The twenty cells below had no directly computed bounds; what stood
for a lower bound was the row-11 value carried up by monotonicity (or, for a few cells, a strongly regular graph).

This directory holds the colourings themselves. Each file is a plain edge list `u v colour` over 1..N, one edge per
line, colour 1 = the first graph, colour 2 = the second. A file named `..._nN_semiregM[f1].txt` is a colouring of K_N
invariant under a prescribed automorphism built from cycles of length M (with `f1` = one extra fixed point). Check any
of them with the arbiter in this repository, which is written from the definitions and shares no code with the search:

    python3 tools/check_any.py k2-rows-12-15/witnesses/<file> K2x14,K2x9      # prints VALID or INVALID

A colouring of K_N with neither forbidden subgraph proves R > N, hence R >= N+1.

## The cells

`prev` is the best lower bound previously on record. `LM` is the Lortz-Mengersen general bound
R(K_{2,n-s}, K_{2,n}) <= 4n-2s-3 (JGT 43 (2003) 252-268; DS1 item 3.3.2(j)), which for this family is 2n+2m-3.
`computed` is that paper's own Lemmas 2.2 and 2.3 evaluated at these parameters. Those lemmas are counting inequalities
on the common neighbours of a pair and on the neighbourhood of one vertex; `counting_bound.py` in the working repository
implements them. The lemmas are Lortz and Mengersen's, not ours. What was missing from the record is their numerical
consequence at n = 12..15, because their Table I stops at 10; those are the numbers below.

| cell | prev | lower (here) | upper | source of upper | LM | witness | shape |
|---|---:|---:|---:|---|---:|---|---|
| R(K2,12; K2,3) | 22 | **23** | 24 | Lemmas 2.2/2.3 evaluated | 27 | `witness_k2x12k2x3_n22_semireg2.txt` | 11 x 2 |
| R(K2,12; K2,4) | 25 | **26** | 27 | Lemmas 2.2/2.3 evaluated | 29 | `witness_k2x12k2x4_n25_semireg5.txt` | 5 x 5 |
| R(K2,12; K2,5) | 28 | **29** | 30 | Lemmas 2.2/2.3 evaluated | 31 | `witness_k2x12k2x5_n28_semireg7.txt` | 4 x 7 |
| R(K2,12; K2,6) | 29 | **31** | 32 | Lemmas 2.2/2.3 evaluated | 33 | `witness_k2x12k2x6_n30_semireg15.txt` | 2 x 15 |
| R(K2,12; K2,7) | 33 | **35** | 35 | Lortz-Mengersen (published) | 35 | `witness_k2x12k2x7_n34_semireg17.txt` | 2 x 17 |
| R(K2,12; K2,8) | 35 | **37** | 37 | Lortz-Mengersen (published) | 37 | `witness_k2x12k2x8_n36_semireg18.txt` | 2 x 18 |
| R(K2,13; K2,3) | 22 | **25** | 26 | Lemmas 2.2/2.3 evaluated | 29 | `witness_k2x13k2x3_n24_semireg12.txt` | 2 x 12 |
| R(K2,13; K2,4) | 26 | **28** | 29 | Lemmas 2.2/2.3 evaluated | 31 | `witness_k2x13k2x4_n27_semireg9.txt` | 3 x 9 |
| R(K2,13; K2,5) | 28 | **31** | 32 | Lemmas 2.2/2.3 evaluated | 33 | `witness_k2x13k2x5_n30_semireg10.txt` | 3 x 10 |
| R(K2,13; K2,6) | 29 | **32** | 34 | Lemmas 2.2/2.3 evaluated | 35 | `witness_k2x13k2x6_n31_semireg10f1.txt` | 3 x 10 + 1 fixed |
| R(K2,13; K2,9) | 37 | **41** | 41 | Lortz-Mengersen (published) | 41 | `witness_k2x13k2x9_n40_semireg20.txt` | 2 x 20 |
| R(K2,14; K2,3) | 22 | **26** | 27 | Lemmas 2.2/2.3 evaluated | 31 | `witness_k2x14k2x3_n25_semireg5.txt` | 5 x 5 |
| R(K2,14; K2,4) | 26 | **29** | 30 | Lemmas 2.2/2.3 evaluated | 33 | `witness_k2x14k2x4_n28_semireg14.txt` | 2 x 14 |
| R(K2,14; K2,5) | 28 | **31** | 33 | Lemmas 2.2/2.3 evaluated | 35 | `witness_k2x14k2x5_n30_semireg30.txt` | 1 x 30 |
| R(K2,14; K2,6) | 29 | **34** | 36 | Lemmas 2.2/2.3 evaluated | 37 | `witness_k2x14k2x6_n33_semireg11.txt` | 3 x 11 |
| R(K2,14; K2,9) | 37 | **43** | 43 | Lortz-Mengersen (published) | 43 | `witness_k2x14k2x9_n42_semireg21.txt` | 2 x 21 |
| R(K2,15; K2,3) | 24 | **27** | 28 | Lemmas 2.2/2.3 evaluated | 33 | `witness_k2x15k2x3_n26_semireg13.txt` | 2 x 13 |
| R(K2,15; K2,4) | 26 | **30** | 32 | Lemmas 2.2/2.3 evaluated | 35 | `witness_k2x15k2x4_n29_semireg7f1.txt` | 4 x 7 + 1 fixed |
| R(K2,15; K2,5) | 28 | **33** | 35 | Lemmas 2.2/2.3 evaluated | 37 | `witness_k2x15k2x5_n32_semireg16.txt` | 2 x 16 |
| R(K2,15; K2,6) | 29 | **35** | 37 | Lemmas 2.2/2.3 evaluated | 39 | `witness_k2x15k2x6_n34_semireg17.txt` | 2 x 17 |

## What is closed and what is not

Four cells are closed, because the colouring here meets the published Lortz-Mengersen upper bound exactly:
**R(K2,12; K2,7) = 35**, **R(K2,12; K2,8) = 37**, **R(K2,13; K2,9) = 41**, **R(K2,14; K2,9) = 43**.

The other sixteen are windows of width 1 to 3. In those the upper bound comes from evaluating Lortz and Mengersen's
Lemmas 2.2 and 2.3 at these parameters, which lands 1 to 6 below their own general bound 2n+2m-3; the lower bound is the
colouring deposited here. The colourings are the new objects; the upper bounds are arithmetic on published inequalities. Closing one needs either a colouring
of K_(upper-1) or a refutation at upper-1 vertices.

## Method

Each colouring is a CaDiCaL model of the plain two-colour codegree formula (no lexicographic symmetry breaking) with
one extra constraint: the colour of an edge equals the colour of its image under a fixed permutation sigma made of
equal-length cycles. That collapses the search to one variable per edge orbit, so a cell that is far out of reach in
general becomes a formula of a few thousand variables. The search over shapes is exhaustive in the divisors of N and
N-1. It can only find colourings that happen to be that symmetric, so a miss proves nothing.

Every file here was checked twice: by `tools/check_any.py` and by an independent recount of common neighbours against
the codegree caps, done in a different program from the one that produced it.

## Priority

The full text of Lortz and Mengersen has not been read: "Off-diagonal and asymptotic results on the Ramsey number
r(K_{2,m}, K_{2,n})", J. Graph Theory 43 (2003) 252-268; "Bounds on Ramsey numbers of certain complete bipartite
graphs", Results Math. 41 (2002) 140-149; and "Further Ramsey numbers for small complete bipartite graphs",
Ars Combin. 79 (2006) 195-203. Those papers discuss equality cases for this family, so an earlier construction for any
of these cells cannot be excluded. The upper bounds here are NOT a new lemma: an independent check on 2026-09-10
reimplemented Lemmas 2.2 and 2.3 straight from the paper and reproduced every one of them. The flag-algebra and
semidefinite-programming method of Lidicky and Pfender (SIAM Review 68 (2026) 385-403) gives upper bounds for other
complete bipartite cells but does not treat any R(K_{2,m}, K_{2,n}); it has not been aimed at this family.

