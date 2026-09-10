# K(2,14) / K(2,9) at n = 43

Unconfirmed, not peer reviewed. Nothing here is a claim.

Forbidden: **K_{2,14} in colour 1, K_{2,9} in colour 2**. This cell lies outside the range of the survey's Table IVc
(DS1 rev #18 tabulates 6 <= n <= 11); the only published bounds are the general ones.

**Upper bound, published.** Lortz-Mengersen's general bound R(K_{2,n-s}, K_{2,n}) <= 4n - 2s - 3 (JGT 43 (2003); DS1.18
item 3.3.2(j)) with n = 14, s = 5 gives <= 43. Our elementary counting lemma (scripts/lemma/counting_bound.py) reproduces
the same value.

**Lower bound, held here.** `witness/witness_k2x14k2x9_n42_semireg21.txt` is a colouring of K_42 avoiding both forbidden
graphs: colour 1 is 23-regular with at most 13 common neighbours on any pair, colour 2 is 18-regular with at most 8; its
automorphism group is the prescribed rotation of order 21 (two orbits of 21 vertices). The previously recorded lower
bound was 37, from the strongly regular graph SRG(36,14,4,6). Found on 2026-09-10 as a CaDiCaL model of the plain
two-colour formula with a prescribed fixed-point-free automorphism of order 21
(`ramsey/scripts/lemma/semireg_witness.py 42 K2x14,K2x9 --m 21`, 99 s), checked by
`tools/check_any.py <witness> K2x14,K2x9` -> VALID and by an independent codegree recount.

Together **R(K_{2,14}, K_{2,9}) = 43**, resting on a published theorem and a machine-checkable colouring.

Priority note: the survey does not tabulate this cell and Van Overberghe's circulant repository stops at K_{2,11}; the
full text of Lortz-Mengersen 2003 (equality cases via Hadamard matrices / strongly regular graphs) has not been read, so
an earlier construction cannot be excluded.
