# K(2,12) / K(2,5): lower bound 29

Unconfirmed, not peer reviewed. Nothing here is a claim.

Forbidden: **K_{2,12} in colour 1, K_{2,5} in colour 2**. This cell lies outside the survey's Table IVc (DS1 rev #18
tabulates 6 <= n <= 11). Previously recorded lower bound: 28 (VO row-11 by monotonicity); published upper bound: the Lortz-Mengersen
general bound 4n - 2s - 3 = 31; our elementary counting lemma (ramsey/scripts/lemma/counting_bound.py) gives <= 30.

**Lower bound, held here.** `witness/witness_k2x12k2x5_n28_semireg7.txt` is a colouring of K_28 avoiding both forbidden graphs,
found on 2026-09-10 as a CaDiCaL model of the plain two-colour formula with a prescribed automorphism
(4 cycles of length 7; `ramsey/scripts/lemma/semireg_witness.py 28 K2x12,K2x5 --m 7 --fixed 0`),
checked by `tools/check_any.py <witness> K2x12,K2x5` -> VALID (the arbiter shares no code with the encoder) and by an
independent codegree recount. Hence **R(K_{2,12}, K_{2,5}) >= 29**.

**Window.** With the counting upper bound, 29 <= R(K_{2,12}, K_{2,5}) <= 30. Closing it needs either a colouring of
K_29 or a refutation at 29 vertices.

Priority note: the survey does not tabulate this cell and Van Overberghe's circulant repository stops at K_{2,11}; the full
text of Lortz-Mengersen 2003 has not been read, so an earlier construction cannot be excluded.
