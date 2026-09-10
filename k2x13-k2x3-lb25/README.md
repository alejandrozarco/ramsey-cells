# K(2,13) / K(2,3): lower bound 25

Unconfirmed, not peer reviewed. Nothing here is a claim.

Forbidden: **K_{2,13} in colour 1, K_{2,3} in colour 2**. This cell lies outside the survey's Table IVc (DS1 rev #18
tabulates 6 <= n <= 11). Previously recorded lower bound: 22 (VO row-11 by monotonicity); published upper bound: the Lortz-Mengersen
general bound 4n - 2s - 3 = 29; our elementary counting lemma (ramsey/scripts/lemma/counting_bound.py) gives <= 26.

**Lower bound, held here.** `witness/witness_k2x13k2x3_n24_semireg12.txt` is a colouring of K_24 avoiding both forbidden graphs,
found on 2026-09-10 as a CaDiCaL model of the plain two-colour formula with a prescribed automorphism
(2 cycles of length 12; `ramsey/scripts/lemma/semireg_witness.py 24 K2x13,K2x3 --m 12 --fixed 0`),
checked by `tools/check_any.py <witness> K2x13,K2x3` -> VALID (the arbiter shares no code with the encoder) and by an
independent codegree recount. Hence **R(K_{2,13}, K_{2,3}) >= 25**.

**Window.** With the counting upper bound, 25 <= R(K_{2,13}, K_{2,3}) <= 26. Closing it needs either a colouring of
K_25 or a refutation at 25 vertices.

Priority note: the survey does not tabulate this cell and Van Overberghe's circulant repository stops at K_{2,11}; the full
text of Lortz-Mengersen 2003 has not been read, so an earlier construction cannot be excluded.
