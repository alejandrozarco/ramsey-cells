# K(2,15) / K(2,5): lower bound 33

Unconfirmed, not peer reviewed. Nothing here is a claim.

Forbidden: **K_{2,15} in colour 1, K_{2,5} in colour 2**. Outside the survey's Table IVc (6 <= n <= 11). Previously recorded
lower bound: 28 (Van Overberghe's K_{2,11} construction by monotonicity); published upper bound: Lortz-Mengersen 4n - 2s - 3 = 37;
our counting lemma gives <= 35.

**Lower bound, held here.** `witness/witness_k2x15k2x5_n32_semireg16.txt` is a colouring of K_32 avoiding both forbidden graphs, found
2026-09-10 as a CaDiCaL model of the plain two-colour formula with a prescribed automorphism (2 cycles of length 16;
`ramsey/scripts/lemma/semireg_witness.py 32 K2x15,K2x5 --m 16`), checked by `tools/check_any.py <witness> K2x15,K2x5` -> VALID and by an
independent codegree recount. Hence **R(K_{2,15}, K_{2,5}) >= 33**; with the counting bound, 33 <= R <= 35.

Priority note: the full text of Lortz-Mengersen 2003 has not been read; an earlier construction cannot be excluded.
