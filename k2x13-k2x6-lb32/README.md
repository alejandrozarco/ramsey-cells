# K(2,13) / K(2,6): lower bound 32

Unconfirmed, not peer reviewed. Nothing here is a claim.

Forbidden: **K_{2,13} in colour 1, K_{2,6} in colour 2**. Outside the survey's Table IVc (6 <= n <= 11). Previously recorded
lower bound: 29 (VO monotone); published upper bound: Lortz-Mengersen 4n - 2s - 3 = 35; our counting lemma gives <= 34.

**Lower bound, held here.** `witness/witness_k2x13k2x6_n31_semireg10f1.txt` is a colouring of K_31 avoiding both forbidden graphs, found
2026-09-10 as a CaDiCaL model of the plain two-colour formula with a prescribed automorphism (3 cycles of length 10 plus one fixed point;
`ramsey/scripts/lemma/semireg_witness.py 31 K2x13,K2x6 --m 10 --fixed 1`), checked by `tools/check_any.py <witness> K2x13,K2x6` -> VALID
and by an independent codegree recount. Hence **R(K_{2,13}, K_{2,6}) >= 32**; with the counting bound, 32 <= R <= 34.

Priority note: the full text of Lortz-Mengersen 2003 has not been read; an earlier construction cannot be excluded.
