# K(2,14) / K(2,6): lower bound 34

Unconfirmed, not peer reviewed. Nothing here is a claim.

Forbidden: **K_{2,14} in colour 1, K_{2,6} in colour 2**. Outside the survey's Table IVc (6 <= n <= 11). Previously recorded
lower bound: 29 (VO monotone); published upper bound: Lortz-Mengersen 4n - 2s - 3 = 37; our counting lemma gives <= 36.

**Lower bound, held here.** `witness/witness_k2x14k2x6_n33_semireg11.txt` is a colouring of K_33 avoiding both forbidden graphs, found
2026-09-10 as a CaDiCaL model of the plain two-colour formula with a prescribed automorphism (3 cycles of length 11;
`ramsey/scripts/lemma/semireg_witness.py 33 K2x14,K2x6 --m 11 --fixed 0`), checked by `tools/check_any.py <witness> K2x14,K2x6` -> VALID
and by an independent codegree recount. Hence **R(K_{2,14}, K_{2,6}) >= 34**; with the counting bound, 34 <= R <= 36.

Priority note: the full text of Lortz-Mengersen 2003 has not been read; an earlier construction cannot be excluded.
