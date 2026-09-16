# K(2,11) / K(2,5) at n = 28

Unconfirmed, not peer reviewed. Nothing here is a claim.

Forbidden: **K_{2,11} in colour 1, K_{2,5} in colour 2**. DS1 rev #18 Table IVc (row n = 11, column
m = 5) prints `>= 28` with source [VO]; the survey's general bound 3.3.2(j) gives <= 29. So the cell
was open at 28-29.

**Lower bound, held here.** `witness/witness_k211k25_n27.txt` is a colouring of K_27 with no
K_{2,11} in colour 1 and no K_{2,5} in colour 2: colour 1 is 16-regular with at most 10 common
neighbours on any pair, colour 2 is 10-regular with at most 4. It was found on 2026-09-10 as a
CaDiCaL model of the plain two-colour formula with a prescribed fixed-point-free automorphism of
order 9 (three orbits of nine vertices; `ramsey/scripts/lemma/semireg_witness.py 27 K2x11,K2x5 --m 9`,
23 s). Checked by `tools/check_any.py witness/witness_k211k25_n27.txt K2x11,K2x5` -> VALID (the
arbiter shares no code with the encoder). Circulant colourings of K_27 do not exist for this cell
(the same search with a 27-cycle is UNSAT in 3 s). Its full colour-preserving automorphism group has order 36,
isomorphic to Z_2 x D_9: the 9-fold rotation, nine reflections, and an involution swapping the first and third
orbits; the vertex orbits are {1..9, 19..27} and {10..18}, so the colouring is not vertex-transitive and not a
Cayley colouring. No vertex-transitive witness exists at all: an exhaustive SAT search over Cayley
colourings of every group of order 27 (`ramsey/scripts/lemma/cayley_sat.py`, all five groups UNSAT within
seconds) combined with the theorem that vertex-transitive graphs of order p^3 are Cayley graphs (Marusic)
shows every good colouring of K_27 for this cell has at least two vertex orbits. So R >= 28 independently of [VO].

**Upper bound, from Lortz and Mengersen (2003).** Their Lemma 2.3 and Lemma 2.2(1),(2), evaluated at
n = 28, b = 4, r = 10, exclude every colour-2 degree: the pair-counting identities confine it to
{10, 11}, where the per-vertex deficit budget is negative, so no good colouring of K_28 exists.
`counting/PROOF_NOTE.md` works the arithmetic and `counting/counting_bound.py 28 4 10` reproduces it;
the same script reproduces the known values 29, 31, 33 of the neighbouring cells. This is an
evaluation of their published lemmas at a parameter their Table I does not reach, **not a new
argument**. An earlier version of this page presented it as ours; on 2026-09-10 an implementation
written from their printed paper reproduced every one of this repository's finite counting bounds,
and the attribution is corrected here (2026-09-16).

**Standing.** Both bounds follow from published work: the lower bound 28 is printed in DS1 [VO], and
the upper bound is Lortz and Mengersen's lemmas evaluated. R(K_{2,11}, K_{2,5}) = 28 is therefore a
consequence of the literature that is not printed anywhere, **not a new determination**. What this
directory adds is the K_27 colouring above, which reproduces the published lower bound
independently of [VO], and the observation that no vertex-transitive colouring achieves it.
