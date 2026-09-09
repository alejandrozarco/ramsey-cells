# R(K_{2,11}, K_{2,5}) <= 28 by counting (2026-09-09; UNCONFIRMED, not peer reviewed; nothing here is a claim)

Source: Astra (GPT-6 via codex exec) round 8, runs/astra_round8_2026-09-09.md, section A; re-derived by hand and by
scripts/lemma/counting_bound.py (which also reproduces the known upper bounds 29 for K2x10,K2x6, 31 for K2x10,K2x7,
26 for K2x11,K2x4 (our SAT result of 2026-09-06) and 33 for K2x11,K2x7 (DS1 3.3.2(j))).

Setting. Red/blue colouring of K_N, N = 28, with no red K_{2,11} (red codegree <= r = 10) and no blue K_{2,5}
(blue codegree <= b = 4). For a vertex v let d = its blue degree, S = N_blue(v), T = the other s = 27 - d vertices,
x = e_blue(S, T).

Lemma 1.1 (general). (1.1) d(s - r) <= x <= b s. (1.2) for s >= r+1: d C(s-r,2) + s C(s-r-1,2) <= b C(s,2).
(1.3) for d >= b+1: d C(d-b-1,2) + s C(d-b,2) <= r C(d,2).
Proofs: (1.1) each u in S has at most r red neighbours in T (they are common red neighbours of u, v), hence at least
s - r blue ones; each w in T has at most b blue neighbours in S (common blue neighbours of v, w). (1.2) count blue
common neighbours of the pairs inside T by the common neighbour: u in S contributes C(deg_T(u),2) >= C(s-r,2); w in T
has at most r red neighbours inside T (common red with v), hence >= s-1-r blue ones, contributing C(s-r-1,2); v
contributes nothing; the cap is b per pair. (1.3) is the colour-reversed count on pairs inside S (u in S has at most
b blue neighbours inside S, w in T at most b blue neighbours in S; cap r per pair).

Step 1 (degree window). With d = 27 - s, twice (LHS - RHS) of (1.2) is 21 s^2 - 541 s + 2970, which is 36 > 0 at
s = 18 and increasing for s >= 13: so d <= 9 is impossible. Twice (LHS - RHS) of (1.3) is 15 d^2 - 223 d + 540,
which is 24 > 0 at d = 12 and increasing for d >= 8: so d >= 12 is impossible. Hence every vertex has blue degree
10 or 11. (Checked numerically: (1.2) at s=18 reads 630 <= 612, false; (1.3) at d=12 reads 672 <= 660, false.)

Step 2 (contradiction). For d = 10: s = 17 and (1.1) reads 70 <= x <= 68. For d = 11: s = 16 and (1.1) reads
66 <= x <= 64. Both are impossible. Equivalently the deficit budget Lambda(d) = d(r - s) + b s = (d - 9)(d - 12)
equals -2 at both degrees, while it is a sum of nonnegative deficits (LEMMAS Lemma 2.2, general form).

Conclusion. No good colouring of K_28 exists: R(K_{2,11}, K_{2,5}) <= 28. DS1.18 (Table IVc, row 11, column 5)
gives R >= 28 [VO = Van Overberghe; GoeVO 2022]; the general bound 3.3.2(j) of Lortz-Mengersen gives only <= 29.
Together: R(K_{2,11}, K_{2,5}) = 28, if the lower-bound construction is confirmed (a good colouring of K_27; not in
our incumbent set runs/reference_graphs/vo_incumbents/, to be fetched from Van Overberghe's repository or
reconstructed).

Status: hand-checked by the owner-side agent (twice) and by counting_bound.py; needs a human reader and the K_27
witness before any statement. Press search 2026-09-09: nothing on this cell beyond DS1.
