#!/usr/bin/env python3
"""Elementary counting bound for two-colour codegree cells R(K_{2,r+1}, K_{2,b+1}) at N vertices (red codegree <= r,
blue codegree <= b, d = blue degree of a vertex v, S = N(v), T = the other s = N-1-d vertices, x = e(S,T)).
Three inequalities, each a double count (LEMMAS_draft.md Lemma 1.1 with general parameters; Astra round 8):
  (1.1)  d(s - r) <= x <= b s          [u in S has >= s-r blue nbrs in T; w in T has <= b blue nbrs in S]
  (1.2)  d C(s-r,2) + s C(s-r-1,2) <= b C(s,2)   for s >= r+1   [blue common nbrs of pairs inside T]
  (1.3)  d C(d-b-1,2) + s C(d-b,2) <= r C(d,2)   for d >= b+1   [red common nbrs of pairs inside S]
and the deficit budget Lambda(d) = d(r-s) + b s = sum of nonnegative deficits (LEMMAS Lemma 2.2, general form).
If every degree d in 0..N-1 violates (1.2) or (1.3), or has Lambda(d) < 0 (equivalently violates (1.1)), then no
vertex can exist in a good colouring of K_N: R(K_{2,r+1}, K_{2,b+1}) <= N.
usage: counting_bound.py N b r      (e.g. 28 4 10 for K2x11,K2x5 at N=28)"""
import sys
from math import comb
N, b, r = (int(x) for x in sys.argv[1:4])
rows = []; feasible = []
for d in range(N):
    s = N - 1 - d
    v12 = s >= r + 1 and d * comb(s - r, 2) + s * comb(s - r - 1, 2) > b * comb(s, 2)
    v13 = d >= b + 1 and d * comb(d - b - 1, 2) + s * comb(d - b, 2) > r * comb(d, 2)
    lam = d * (r - s) + b * s; v11 = d * (s - r) > b * s
    status = 'excluded by (1.2)' if v12 else 'excluded by (1.3)' if v13 else ('budget < 0, (1.1) violated' if lam < 0 else 'FEASIBLE')
    rows.append((d, s, lam, status))
    if status == 'FEASIBLE': feasible.append(d)
print(f"R(K_2x{r+1}, K_2x{b+1}) at N={N}: red codegree <= {r}, blue codegree <= {b}")
for d, s, lam, st in rows:
    if st == 'FEASIBLE' or (0 < d < N - 1 and rows[d - 1][3] != st or d + 1 < N and rows[d + 1][3] != st): print(f"  d={d:2d} s={s:2d} Lambda={lam:4d}  {st}")
print("VERDICT:", (f"no good colouring of K_{N}: every blue degree is excluded -> R <= {N}" if not feasible else f"feasible degrees {feasible} (budgets {[rows[d][2] for d in feasible]}): counting alone does not decide"))
