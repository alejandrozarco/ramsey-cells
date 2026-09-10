# K(2,13) / K(2,4): lower bound 28

Unconfirmed, not peer reviewed. Nothing here is a claim.

Forbidden: **K_{2,13} in colour 1, K_{2,4} in colour 2**. This cell lies outside the survey's Table IVc (DS1 rev #18
tabulates 6 <= n <= 11). Previously recorded lower bound: 26 (SRG(25,8,3,2)); published upper bound: the Lortz-Mengersen
general bound 4n - 2s - 3 = 31; our elementary counting lemma (ramsey/scripts/lemma/counting_bound.py) gives <= 29.

**Lower bound, held here.** `witness/witness_k2x13k2x4_n27_semireg9.txt` is a colouring of K_27 avoiding both forbidden graphs,
found on 2026-09-10 as a CaDiCaL model of the plain two-colour formula with a prescribed automorphism
(3 cycles of length 9; `ramsey/scripts/lemma/semireg_witness.py 27 K2x13,K2x4 --m 9 --fixed 0`),
checked by `tools/check_any.py <witness> K2x13,K2x4` -> VALID (the arbiter shares no code with the encoder) and by an
independent codegree recount. Hence **R(K_{2,13}, K_{2,4}) >= 28**.

**Window.** With the counting upper bound, 28 <= R(K_{2,13}, K_{2,4}) <= 29. Closing it needs either a colouring of
K_28 or a refutation at 28 vertices.

Priority note: the survey does not tabulate this cell and Van Overberghe's circulant repository stops at K_{2,11}; the full
text of Lortz-Mengersen 2003 has not been read, so an earlier construction cannot be excluded.
