# K(2,12) / K(2,3): lower bound 23

Unconfirmed, not peer reviewed. Nothing here is a claim.

Forbidden: **K_{2,12} in colour 1, K_{2,3} in colour 2**. This cell lies outside the survey's Table IVc (DS1 rev #18
tabulates 6 <= n <= 11). Previously recorded lower bound: 22 (VO row-11 by monotonicity); published upper bound: the Lortz-Mengersen
general bound 4n - 2s - 3 = 27; our elementary counting lemma (ramsey/scripts/lemma/counting_bound.py) gives <= 24.

**Lower bound, held here.** `witness/witness_k2x12k2x3_n22_semireg2.txt` is a colouring of K_22 avoiding both forbidden graphs,
found on 2026-09-10 as a CaDiCaL model of the plain two-colour formula with a prescribed automorphism
(11 cycles of length 2; `ramsey/scripts/lemma/semireg_witness.py 22 K2x12,K2x3 --m 2 --fixed 0`),
checked by `tools/check_any.py <witness> K2x12,K2x3` -> VALID (the arbiter shares no code with the encoder) and by an
independent codegree recount. Hence **R(K_{2,12}, K_{2,3}) >= 23**.

**Window.** With the counting upper bound, 23 <= R(K_{2,12}, K_{2,3}) <= 24. Closing it needs either a colouring of
K_23 or a refutation at 23 vertices.

Priority note: the survey does not tabulate this cell and Van Overberghe's circulant repository stops at K_{2,11}; the full
text of Lortz-Mengersen 2003 has not been read, so an earlier construction cannot be excluded.
