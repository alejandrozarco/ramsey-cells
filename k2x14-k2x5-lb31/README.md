# K(2,14) / K(2,5): lower bound 31

Unconfirmed, not peer reviewed. Nothing here is a claim.

Forbidden: **K_{2,14} in colour 1, K_{2,5} in colour 2**. This cell lies outside the survey's Table IVc (DS1 rev #18
tabulates 6 <= n <= 11). Previously recorded lower bound: 28 (VO row-11 by monotonicity); published upper bound: the Lortz-Mengersen
general bound 4n - 2s - 3 = 35; our elementary counting lemma (ramsey/scripts/lemma/counting_bound.py) gives <= 33.

**Lower bound, held here.** `witness/witness_k2x14k2x5_n30_semireg30.txt` is a colouring of K_30 avoiding both forbidden graphs,
found on 2026-09-10 as a CaDiCaL model of the plain two-colour formula with a prescribed automorphism
(1 cycles of length 30; `ramsey/scripts/lemma/semireg_witness.py 30 K2x14,K2x5 --m 30 --fixed 0`),
checked by `tools/check_any.py <witness> K2x14,K2x5` -> VALID (the arbiter shares no code with the encoder) and by an
independent codegree recount. Hence **R(K_{2,14}, K_{2,5}) >= 31**.

**Window.** With the counting upper bound, 31 <= R(K_{2,14}, K_{2,5}) <= 33. Closing it needs either a colouring of
K_32 or a refutation at 32 vertices.

Priority note: the survey does not tabulate this cell and Van Overberghe's circulant repository stops at K_{2,11}; the full
text of Lortz-Mengersen 2003 has not been read, so an earlier construction cannot be excluded.
