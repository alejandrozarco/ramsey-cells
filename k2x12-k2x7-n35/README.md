# K(2,12) / K(2,7) at n = 35

Unconfirmed, not peer reviewed. Nothing here is a claim.

Forbidden: **K_{2,12} in colour 1, K_{2,7} in colour 2**. This cell lies outside the range of the survey's Table IVc
(DS1 rev #18 tabulates 6 <= n <= 11); the only published bounds are the general ones.

**Upper bound, published.** Lortz-Mengersen's general bound R(K_{2,n-s}, K_{2,n}) <= 4n - 2s - 3 (JGT 43 (2003); DS1.18
item 3.3.2(j)) with n = 12, s = 5 gives <= 35. Our elementary counting lemma (LEMMAS_draft.md Lemma 1.1 with general
parameters plus the deficit budget; scripts/lemma/counting_bound.py) reproduces the same value.

**Lower bound, held here.** The colouring(s) of K_34 in `witness/` avoid both forbidden graphs; the previously
recorded lower bound was 33 (Van Overberghe's K_{2,11} construction by monotonicity). Found on 2026-09-10 as CaDiCaL models of the plain two-colour formula with a prescribed
fixed-point-free automorphism (`ramsey/scripts/lemma/semireg_witness.py`, lane 1 of the untabulated-rows scan), checked by
`tools/check_any.py <witness> K2x12,K2x7` -> VALID (the arbiter shares no code with the encoder) and by an independent
codegree recount.

Together **R(K_{2,12}, K_{2,7}) = 35**, resting on a published theorem and a machine-checkable colouring.

Priority note: the survey does not tabulate this cell and Van Overberghe's circulant repository stops at K_{2,11}; the
full text of Lortz-Mengersen 2003 (equality cases via Hadamard matrices / strongly regular graphs) has not been read,
so an earlier construction cannot be excluded.
