# K(2,11) / K(2,5) at n = 28

Unconfirmed, not peer reviewed. Nothing here is a claim.

Forbidden: **K_{2,11} in colour 1, K_{2,5} in colour 2**. DS1 rev #18 Table IVc (row n = 11, column
m = 5) prints `>= 28` with source [VO]; the survey's general bound 3.3.2(j) gives <= 29. So the cell
was open at 28-29.

**Lower bound, held here.** `witness/witness_k211k25_n27.txt` is a colouring of K_27 with no
K_{2,11} in colour 1 and no K_{2,5} in colour 2: colour 1 is 16-regular with at most 10 common
neighbours on any pair, colour 2 is 10-regular with at most 4. It was found on 2026-09-10 as a
CaDiCaL model of the plain two-colour formula with a prescribed fixed-point-free automorphism of
order 9 (three orbits of nine vertices; `ramsey/scripts/lemma/semireg_witness.py 27 K2x11,K2x5 --m 9`,
23 s). Checked by `tools/check_any.py witness/witness_k211k25_n27.txt K2x11,K2x5` -> VALID (the
arbiter shares no code with the encoder). Circulant colourings of K_27 do not exist for this cell
(the same search with a 27-cycle is UNSAT in 3 s). So R >= 28 independently of [VO].

**Upper bound, by counting, not machine-checked.** `counting/PROOF_NOTE.md` argues R <= 28: at n = 28
the three pair-counting identities plus the per-vertex deficit budget force every colour-2 degree
into {10, 11}, and the budget is negative there, so no good colouring of K_28 exists.
`counting/counting_bound.py 28 4 10` reproduces the arithmetic; the same script reproduces the known
values 29, 31, 33 of the neighbouring cells and our SAT-based R(K_{2,11}, K_{2,4}) = 26. The argument
was corroborated blind by a second reader (GPT-6, 2026-09-09) and has NOT been checked by a human
referee.

Together, if the counting note holds, **R(K_{2,11}, K_{2,5}) = 28**.
