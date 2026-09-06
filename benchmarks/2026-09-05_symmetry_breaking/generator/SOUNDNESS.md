# Soundness of the gen_variant.py constraints (two-colour K_{2,t1} vs K_{2,t2} cells)

Notation: n vertices, m = n-1, colour 1 = "red", d_v = red degree of v, b_v = m - d_v = blue degree.
k1 = t1-1 and k2 = t2-1 are the codegree bounds: every pair has at most k1 common red neighbours
and at most k2 common blue neighbours. P = C(n,2). The base encoding (gen_ramsey.build without
vertex-lex) is the deposited codegree encoding; nothing below changes it, everything is appended.

A refutation of base AND extra is a refutation of base whenever every red/blue colouring of K_n that
satisfies base can be relabelled (vertex permutation) into one that satisfies base AND extra. Base is
invariant under relabelling, so it suffices that the extra constraints hold for some relabelling.

## D: degree unaries
o[v][k] <-> (d_v >= k), a bidirectional sequential counter over the m red-edge variables at v.
Definitional (both directions encoded), so it adds no constraint on the colouring.

## O: degree ordering, d_1 >= d_2 >= ... >= d_n
Any colouring can be relabelled so red degrees are non-increasing. Encoded as o[v+1][k] -> o[v][k].

## L: conditional vertex-lex
For each adjacent transposition s = (v v+1): (d_v = d_{v+1}) -> valseq(x) <=lex valseq(x o s), the
same lex-leader clause set as the deposited --vertex-lex, with the extra premise literal ~eq_v.
eq_v is forced true when the degrees are equal (clause eq_v OR diff_v,1 OR ... OR diff_v,m, where
diff_v,k -> o[v][k] and diff_v,k -> ~o[v+1][k]); when degrees differ eq_v may be false, which
switches the lex clauses off.
Proof of O+L together: fix a colouring; the set S of its relabellings with non-increasing degrees
is non-empty; choose x in S with lex-minimal value sequence. If d_v = d_{v+1} in x then x o s is
also in S (swapping equal-degree vertices keeps the sequence non-increasing), hence
valseq(x) <=lex valseq(x o s). So x satisfies every conditional lex constraint, with eq_v set
truthfully. Note that O alone and the deposited unconditional lex are NOT combined; unconditional
lex plus ordering would be unsound.

## I: implied bounds (theorems about every colouring satisfying base; adding a theorem is sound)
Two counting identities: sum over pairs of the red codegree = sum_v C(d_v,2) <= k1*P, and likewise
sum_v C(b_v,2) <= k2*P.
1. Red-edge window. f(x) = x(x-1)/2 is convex on the reals and equals C(d,2) at integers, so by
   Jensen sum_v f(d_v) >= n f(2E/n) where E is the number of red edges. Hence E <= E_hi, the largest
   E with n f(2E/n) <= k1 P; symmetrically E >= E_lo from the blue sum with P - E blue edges.
   n=22, k1=7, k2=4: 125 <= E <= 138. Encoded with pysat CardEnc (seqcounter) over the 231 red vars.
2. d_1 >= ceil(2 E_lo / n) and d_n <= floor(2 E_hi / n): the maximum is at least the mean and the
   minimum at most the mean. n=22: d_1 >= 12, d_n <= 12.
3. Pair bound with the maximum-degree vertex. For u != 1, N_red(u) splits into N_red(u) ∩ N_red(1)
   (at most k1 vertices) and N_red(u) \ N_red(1), a subset of V \ N_red(1) minus u, so at most
   n - d_1 vertices. Hence d_u <= k1 + n - d_1. Encoded per k: o[1][k] -> ~o[u][k1+n-k+1].
   Feasibility of d_1 = D: all others have d_u <= min(D, k1+n-D), so their blue degrees are at least
   m - min(D, k1+n-D) and the blue sum is at least (n-1) C(m - min(D,k1+n-D), 2) + C(m-D, 2); if
   that exceeds k2 P, D is impossible. n=22: D=18 gives 21*C(10,2)+C(3,2) = 948 > 924, so d_1 <= 17.
4. The same with blue and the minimum-degree vertex n: b_u <= k2 + n - b_n, i.e.
   d_u >= 2m - k2 - n - d_n for u != n. Encoded per k: ~o[n][k] -> o[u][2m-k2-n-(k-1)].
   Feasibility of d_n = D: others have d_u >= max(D, 2m-k2-n-D), red sum at least
   (n-1) C(max(...), 2) + C(D,2) <= k1 P. n=22: D=3 gives 21*C(13,2)+C(3,2) = 1641 > 1617, so d_n >= 4.

## Empirical check
test_variants.py: on eleven small (cell, n) cases with both SAT and UNSAT status, base, lex, DO, DOL
and DOLI agree, and every model decodes to a valid colouring. This is a bug check, not a proof; the
proof is the argument above.

## Mixed formulas per cube (the "regular split")
Under O the sorted degree sequence is a relabelling invariant of the set S used in the D+O+L proof:
every relabelling in S has the same sequence. So a cube made only of literals o[v][k] (statements
"d_v >= k" about the sorted sequence) is preserved by every relabelling in S, and for such a cube it
is sound to refute base AND D AND O AND cube under the stronger formula that also has L: if a colouring
satisfied DO AND cube, its lex-min sorted relabelling would satisfy DOL AND cube. Cubes that contain
edge literals or internal counter literals (prefix counts in label order) are NOT invariant and must
be refuted under the same formula as their parent.
Top cover used: C1 = {d_1 >= 14}, C2 = {d_1 <= 13, d_22 <= 10}, R = {d_1 <= 13, d_22 >= 11}; under O
these three cover every assignment. R is refined into the 276 non-increasing sequences over {11,12,13}
(all of them, without the counting filter, so the cover needs only the counter semantics), each a cube
of o-literals, refuted under DOL. The cover certificate is the refutation of the negation of all cubes
under DO.

## Clarifications after an external audit (MiniMax M3 via OpenRouter, 2026-09-06)
- Lex order. The lex-leader argument works for ANY fixed total order on the assignment vector, provided
  every transposition constraint uses the same order (the lex-min element of S is taken in that order).
  `lexorder=rev` is the reversed edge order; mixing orders across transpositions would be unsound.
- Gating direction. A lex clause carries the literals ~eq_v (and ~eq_{v+1} for distance-2, ~same_u for
  N), so it is enforced only when those eq variables are TRUE, i.e. when the degrees are equal (and,
  for N, the two vertices lie in the same block). An eq variable is forced true when the degrees are
  equal and may be set true spuriously when they differ; a spurious setting only removes models inside
  that branch, and the truthful assignment (eq false when unequal) is always available, so satisfiability
  of the base is preserved. Distance-2: the transposition (v v+2) is enforced only when d_v = d_{v+1} =
  d_{v+2}, so x o (v v+2) stays in S.
- N replaces O. generate() applies N instead of O (never both); N's soundness is the existence of a
  relabelling with a max-degree vertex first, its red neighbours next, both blocks degree-sorted, ties
  lex-min. A labelling that violates N (e.g. C_6 with N_red(1) = {2,6}) is not a counterexample; its
  relabelling satisfies N.
- fix_d1 is a case split, not a constraint: the cubes d_1 = D for D in [d1_lo, Dmax] (with the implied
  units in the formula) cover every colouring, since d_1 is the maximum degree and the bounds are
  theorems; each cube is refuted separately (test_variants.py checks the union against base).
The audit's "UNSOUND" verdicts for N, distance-2 and the regular split were each traced to one of the
misreadings above; no constraint was found unsound.

## Correction to "mixed formulas per cube" (after the GPT-6 Astra review, 2026-09-06)
The label-invariance condition above is sufficient but not necessary. The certified statement is the
unsatisfiability of ONE target formula F* (here DOL), whose relabelling theorem is proved once. Assembly:
  (for every leaf i: UNSAT(F_i AND Q_i))  and  UNSAT(H AND AND_i NOT Q_i)  and  (F* implies H and every F_i)
  ==> UNSAT(F*).
Proof: a model A of F* satisfies H, so by the cover it satisfies some cube Q_i; it also satisfies F_i, so
F_i AND Q_i would be satisfiable. Hence leaves may be refuted under DO or under DOL in any mixture (F* =
DOL, F_i in {DO, DOL}, H = DO), whatever literals the cubes contain, as long as the variable identities
agree (D is generated first in both, so they do). What must NOT be mixed is the direction: a leaf refuted
under a formula that F* does not imply proves nothing. Consequence: the retired DO tree's verified leaves
remain usable together with DOL refutations of its unsolved cubes.
Also noted by the review: (i) the semantic relabelling argument is not a per-clause PR/SR certificate,
because the counter internals (both the degree counters and the codegree Sinz registers) are not
syntactically invariant under vertex transpositions; (ii) the public Comparator statement certifies
UNSAT of the CNF, and the bridge to "no colouring" is the encoder-soundness development, so a formal
relabelling lemma (their route C, 15-35 person-days) would extend that development, not the Comparator
statement; (iii) the colour-swap break S is only a symmetry for identical forbidden graphs (the generator
asserts this).

## Formal counterpart (2026-09-06, lean-sb / sbsound)
The relabelling argument for D+O+L is now a Lean 4 theorem, building with only propext,
Classical.choice and Quot.sound: `SB.dol_encode_sound` (Sbsound/SBDegreeClauses.lean) and its
two-colour instantiation `SB.Portfolio.dol_sound_K2x8_K2x5` state that from any colouring avoiding the
patterns there is a colouring avoiding them whose codegree counters are truthful and which admits an
assignment satisfying every DOL clause (degree counters, ordering, gate, gated lex on colour 0), agreeing
with it on the edge variables. Modules: SBDegree (semantic leader via exists_sb_leader), BiCounter
(counter gadget), SBDegreeVars (variables, neighbour inputs, count = degree), SBDegreeClauses (clause
families and canonical assignment). What remains informal for a DOL closure: the byte-level identity of
the printed CNF with these clause families (the printer in lrat-catcher, to be extended and checked by
hash), and the per-cube assembly (leaves under DO or DOL, cover under DO), argued above.
