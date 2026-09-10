# K(2,15) / K(2,3): lower bound 27

Unconfirmed, not peer reviewed. Nothing here is a claim.

Forbidden: **K_{2,15} in colour 1, K_{2,3} in colour 2**. This cell lies outside the survey's Table IVc (DS1 rev #18
tabulates 6 <= n <= 11). Previously recorded lower bound: 24 (Dybizbanski); published upper bound: the Lortz-Mengersen
general bound 4n - 2s - 3 = 33; our elementary counting lemma (ramsey/scripts/lemma/counting_bound.py) gives <= 28.

**Lower bound, held here.** `witness/witness_k2x15k2x3_n26_semireg13.txt` is a colouring of K_26 avoiding both forbidden graphs,
found on 2026-09-10 as a CaDiCaL model of the plain two-colour formula with a prescribed automorphism
(2 cycles of length 13; `ramsey/scripts/lemma/semireg_witness.py 26 K2x15,K2x3 --m 13 --fixed 0`),
checked by `tools/check_any.py <witness> K2x15,K2x3` -> VALID (the arbiter shares no code with the encoder) and by an
independent codegree recount. Hence **R(K_{2,15}, K_{2,3}) >= 27**.

**Window.** With the counting upper bound, 27 <= R(K_{2,15}, K_{2,3}) <= 28. Closing it needs either a colouring of
K_27 or a refutation at 27 vertices.

Priority note: the survey does not tabulate this cell and Van Overberghe's circulant repository stops at K_{2,11}; the full
text of Lortz-Mengersen 2003 has not been read, so an earlier construction cannot be excluded.
