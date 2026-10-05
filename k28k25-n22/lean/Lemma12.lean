/-
  LEMMA 1.2 FOR R(K_{2,8}, K_{2,5}) AT N = 22 — BOTH HAND ARGUMENTS, MACHINE-CHECKED.

      Colouring.degree_seven_impossible  : (K.blueNbr v).card ≠ 7
      Colouring.degree_eleven_impossible : (K.blueNbr v).card ≠ 11

  under exactly "the colouring is good": every pair has at most 4 common blue neighbours (no blue
  K_{2,5}) and at most 7 common red (no red K_{2,8}). NO `sorry` anywhere in this file; every
  declaration reports [propext, Classical.choice, Quot.sound].

  WHY THIS MATTERS. The census enumerates blue degrees {8,9,10} only. `counting_bound.py 22 4 7`
  admits {7,...,11}; d = 6 and d = 12 fall to Lortz-Mengersen's published inequalities. The gap at
  d = 7 and d = 11 was carried by TWO HAND ARGUMENTS, and REPRODUCE.md names them the weakest link
  in the whole cell: if either is wrong the census enumerates the wrong space, every certificate
  below it stays valid, and nothing downstream can detect it. Those two are what this file closes.

  SCOPE, precisely. This file proves the two hand arguments. It does NOT formalize the d <= 6 and
  d >= 12 exclusions, which are Lortz-Mengersen Lemmas 2.2 and 2.3 and are cited, not reproved.
  "Degrees lie in {8,9,10}" therefore still rests on published results plus this file.

  d = 7 IS NOT A SEPARATE ARGUMENT. The hand proof presents it as its own thirteen steps, working in
  BLUE on the red neighbourhood T, where d = 11 works in RED on the blue neighbourhood S. Swapping
  the colouring exchanges both at once, and the two become the SAME lemmas at different parameters:
      d = 11   (m, b, r) = (6, 4, 7)   |S| = 11   30 + 6l <= 70   l <= 6   66 < 70
      d = 7    (m, b, r) = (6, 7, 4)   |S| = 14   30 + 6l <= 52   l <= 3   42 < 49
  `m = |S| - 1 - b` is 6 in both. WHY (round 34): with normalized degrees `δ_B = d_B - b` and
  `δ_R = d_R - r`, their sum is `N - 1 - b - r = 10`, and the two excluded degrees are exactly the
  two ends — d = 7 gives `(δ_B, δ_R) = (3, 7)`, d = 11 gives `(7, 3)`. Each argument works in the
  neighbourhood whose normalized degree is 7, so `m = 7 - 1 = 6`.

  CAVEAT: that is a symmetry of these normalized endpoint cases. The value 6 is PARAMETER-SPECIFIC,
  not a universal consequence of swapping. Do not write it up as if every cell's two endpoint
  exclusions share an `m`.

  NEITHER HALF USES STEPS 4-8. The double count of P over the pairs of S, the parity argument, and
  the forced 6-regularity are not consumed by either contradiction; only steps 2, 3 and 9-13 are.
  Hand step 10 reads "contributes exactly five" off 6-regularity, but L_u only needs a LOWER bound
  and step 2 already gives at least m. TESTED, not inferred: replace the proofs of `pairs_growth`,
  `even_excess`, `step7_core`, `double_count`, `even_card_of_symm` and
  `even_internal_red_degree_sum` with `sorry` and the exclusions still report clean axioms. Re-run
  that before trusting this paragraph.

  TREAT THE SIMPLIFICATION AS A CLAIM WANTING A REFEREE. An argument that comes out shorter than its
  published presentation is the first thing to distrust, and the margins here are 2 and 4. What is
  certain is that these Lean proofs close without steps 4-8. The parity lemmas are kept and proved
  regardless: they are general, and 6-regularity is of independent interest.

  CONVENTIONS THAT MATTER.
    1. `offDiag` on both sides of the double-count identity, so no natural-number subtraction enters
       there. Subtraction appears elsewhere by design (`f u - base`, `|S| - 1 - b`).
    2. The ordered/doubled convention is GLOBAL-COUNT-ONLY. The `L_u` bounds and the cross-edge
       sums are NOT doubled; a factor of two there typechecks silently and prints clean axioms.
       Round 34 sharpened the wording: these are INCIDENCE counts, not "each edge once". `L_u` sums
       over a fixed `u` and can count one underlying edge twice when both its endpoints lie in the
       overlapping indexing sets. `cross_count` is an incidence identity valid for overlapping sets;
       step 13 applies it to DISJOINT `S` and `T`, and only there does each crossing edge
       contribute once per side.
    3. `@[simp]` membership lemmas come BEFORE the bijections, so each is a statement about the
       colouring rather than about `Finset.filter`.

  REGRESSION GUARD. Adding imports has silently broken a proof in this file before: `card_filter`
  arrived as a simp lemma, a `simp` began looping, and `double_count` degraded to `sorry` while the
  file still compiled and printed its expected warnings. Only `#print axioms` showed it. Keep the
  prints at the bottom and READ them; an exit code says the elaborator finished, not that anything
  was proved.

  BUILD. Lean 4.30.0 + Mathlib. From `lean/sbsound` of this repository (after `lake build`):
  `lake env lean ../../k28k25-n22/lean/Lemma12.lean`. Use MINIMAL imports — a blanket
  `import Mathlib` costs over 200 s per compile against about 10 s for these.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Chebyshev
import Sbsound.Codegree
import Sbsound.SBDegree

open Finset

namespace DegreeLemma

/-- **Growth.** Raising a count from `m` to `m + h` raises the number of ORDERED distinct pairs
    it carries by at least `2*m*h`. Exactly the step-7 increment, with no `Nat.choose` and no
    division: `(m+h)(m+h-1) - m(m-1) = 2mh + h(h-1) ≥ 2mh`.

    Stated over ordered pairs deliberately. The hand argument writes it as
    `C(m+h,2) - C(m,2) ≥ m*h`, which forces `k*(k-1)/2` and truncated subtraction into every
    downstream step; doubling it makes the whole chain subtraction-free. -/
theorem pairs_growth (m h : ℕ) : m * (m - 1) + 2 * m * h ≤ (m + h) * (m + h - 1) := by
  rcases m with _ | m
  · simp
  · have e : (m + 1 + h) - 1 = m + h := by omega
    rw [e, Nat.add_sub_cancel]
    rcases h with _ | h
    · nlinarith
    · nlinarith [Nat.zero_le m, Nat.zero_le h]

/-- **Even excess.** The parity step, stated for any counting function over a finite set.

    If every `f u` is at least `base`, the total `∑ f` is even, and the baseline `|S| * base` is
    even, then the total excess is even too — so it cannot be 1. If it is not zero it is at least
    TWO. That 2 is what carries `P` past its cap with a margin of exactly 2 at N=22, d=11. -/
theorem even_excess {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ) (base : ℕ)
    (hge : ∀ u ∈ S, base ≤ f u)
    (heven : Even (∑ u ∈ S, f u)) (hbase : Even (S.card * base))
    (u₀ : α) (hu₀ : u₀ ∈ S) (hne : f u₀ ≠ base) :
    2 ≤ ∑ u ∈ S, (f u - base) := by
  classical
  have hsplit : ∑ u ∈ S, f u = S.card * base + ∑ u ∈ S, (f u - base) := by
    have hpt : ∀ u ∈ S, f u = base + (f u - base) := fun u hu => by
      have := hge u hu; omega
    calc ∑ u ∈ S, f u = ∑ u ∈ S, (base + (f u - base)) := Finset.sum_congr rfl hpt
      _ = (∑ _u ∈ S, base) + ∑ u ∈ S, (f u - base) := Finset.sum_add_distrib
      _ = S.card * base + ∑ u ∈ S, (f u - base) := by
          rw [Finset.sum_const_nat (fun _ _ => rfl)]
  have hex : Even (∑ u ∈ S, (f u - base)) := by
    rcases heven with ⟨a, ha⟩; rcases hbase with ⟨b, hb⟩
    refine ⟨a - b, ?_⟩; omega
  have hpos : 1 ≤ ∑ u ∈ S, (f u - base) := by
    have h1 : 1 ≤ f u₀ - base := by have := hge u₀ hu₀; omega
    exact le_trans h1 (Finset.single_le_sum (f := fun u => f u - base)
      (fun i _ => Nat.zero_le _) hu₀)
  rcases hex with ⟨c, hc⟩; omega

/-- **Step 7, in general form.** Combine growth with the parity excess.

    If a counting function sits at or above `base` everywhere on `S`, its total is even, the
    baseline `|S| * base` is even, and it is NOT constantly `base`, then the ordered-pair total it
    carries exceeds the all-baseline value by at least `4 * base`.

    The `4` is `2 * 2`: two from parity (the excess cannot be 1), two from counting ordered pairs
    rather than unordered. This is the entire content of steps 6 and 7 of Lemma 1.2, with no
    reference to N, to the codegree caps, or to the colouring. -/
theorem step7_core {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ) (base : ℕ)
    (hge : ∀ u ∈ S, base ≤ f u)
    (heven : Even (∑ u ∈ S, f u)) (hbase : Even (S.card * base))
    (u₀ : α) (hu₀ : u₀ ∈ S) (hne : f u₀ ≠ base) :
    S.card * (base * (base - 1)) + 4 * base ≤ ∑ u ∈ S, f u * (f u - 1) := by
  classical
  have hpt : ∀ u ∈ S, base * (base - 1) + 2 * base * (f u - base) ≤ f u * (f u - 1) := by
    intro u hu
    have hb := hge u hu
    have h := pairs_growth base (f u - base)
    have e : base + (f u - base) = f u := by omega
    rwa [e] at h
  have hsum : ∑ u ∈ S, (base * (base - 1) + 2 * base * (f u - base)) ≤ ∑ u ∈ S, f u * (f u - 1) :=
    Finset.sum_le_sum hpt
  have hL : ∑ u ∈ S, (base * (base - 1) + 2 * base * (f u - base))
      = S.card * (base * (base - 1)) + 2 * base * ∑ u ∈ S, (f u - base) := by
    rw [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl), ← Finset.mul_sum]
  have hx := even_excess S f base hge heven hbase u₀ hu₀ hne
  have : 4 * base ≤ 2 * base * ∑ u ∈ S, (f u - base) := by
    calc 4 * base = 2 * base * 2 := by ring
      _ ≤ 2 * base * ∑ u ∈ S, (f u - base) := Nat.mul_le_mul_left _ hx
  omega

/-- The cell, at its actual parameters, as a check that the general lemma really bites.

    d = 11 at N = 22 with caps b = 4, r = 7. Doubling every count to stay subtraction-free:
    the red codegree cap gives `P ≤ 2 * 7 * C(11,2) = 770`. The all-baseline value is
    `11 * 6 * 5 + 10 * 7 * 6 = 750`. Step 7 adds at least `4 * 6 = 24`, giving `774 > 770`.

    The margin is FOUR here and two in the halved form the hand proof uses. There is no room. -/
example : (11 * (6 * 5) + 10 * (7 * 6)) + 4 * 6 = 774 ∧ 2 * 7 * (11 * 10 / 2) = 770
    ∧ 770 < 774 := by norm_num

end DegreeLemma

/-- A 2-colouring of the edges of the complete graph on `Fin N`.
    `C i j = true` is BLUE, `false` is RED. -/
structure Colouring (N : ℕ) where
  C : Fin N → Fin N → Bool
  symm : ∀ i j, C i j = C j i

namespace Colouring
variable {N : ℕ} (K : Colouring N)

def blueNbr (v : Fin N) : Finset (Fin N) := univ.filter (fun u => u ≠ v ∧ K.C v u)
def redNbr  (v : Fin N) : Finset (Fin N) := univ.filter (fun u => u ≠ v ∧ ¬ K.C v u)
def blueCodeg (i j : Fin N) : Finset (Fin N) :=
  univ.filter (fun w => w ≠ i ∧ w ≠ j ∧ K.C i w ∧ K.C j w)
def redCodeg (i j : Fin N) : Finset (Fin N) :=
  univ.filter (fun w => w ≠ i ∧ w ≠ j ∧ ¬ K.C i w ∧ ¬ K.C j w)

@[simp] lemma mem_blueNbr {v u : Fin N} : u ∈ K.blueNbr v ↔ u ≠ v ∧ K.C v u := by simp [blueNbr]
@[simp] lemma mem_redNbr  {v u : Fin N} : u ∈ K.redNbr v ↔ u ≠ v ∧ ¬ K.C v u := by simp [redNbr]
@[simp] lemma mem_blueCodeg {i j w : Fin N} :
    w ∈ K.blueCodeg i j ↔ w ≠ i ∧ w ≠ j ∧ K.C i w ∧ K.C j w := by simp [blueCodeg]
@[simp] lemma mem_redCodeg {i j w : Fin N} :
    w ∈ K.redCodeg i j ↔ w ≠ i ∧ w ≠ j ∧ ¬ K.C i w ∧ ¬ K.C j w := by simp [redCodeg]

/-! ### The colour swap, for the d = 7 half

    d = 7 is NOT a plain colour swap of d = 11: the hand argument for d = 11 works in RED on the
    blue neighbourhood `S`, and the one for d = 7 works in BLUE on the red neighbourhood `T`. Both
    the colour and the set change.

    Swapping the colouring exchanges both at once. If `K'` is `K` with the colours exchanged then
    `blueNbr K' v = redNbr K v`, and the caps trade places: `K` good with `(b,r) = (4,7)` makes `K'`
    good with `(7,4)`. The d = 7 statement about `K` becomes a statement about `K'` with
    `|blueNbr K' v| = 14`, which is the SAME chain of lemmas at different parameters.

    The arithmetic lands on the same skeleton: `m = |S| - 1 - b` is 6 in both cases
    (11 - 1 - 4 and 14 - 1 - 7), which is why both halves of Lemma 1.2 have the same shape. -/

/-- `K` with its two colours exchanged. -/
def swap (K : Colouring N) : Colouring N where
  C i j := !K.C i j
  symm i j := by simp [K.symm i j]

@[simp] lemma swap_blueNbr (v : Fin N) : (K.swap).blueNbr v = K.redNbr v := by
  ext x; simp [blueNbr, redNbr, swap]

@[simp] lemma swap_redNbr (v : Fin N) : (K.swap).redNbr v = K.blueNbr v := by
  ext x; simp [blueNbr, redNbr, swap]

@[simp] lemma swap_blueCodeg (i j : Fin N) : (K.swap).blueCodeg i j = K.redCodeg i j := by
  ext x; simp [blueCodeg, redCodeg, swap]

@[simp] lemma swap_redCodeg (i j : Fin N) : (K.swap).redCodeg i j = K.blueCodeg i j := by
  ext x; simp [blueCodeg, redCodeg, swap]

/-- The bijection that makes the double count work: for a fixed `w`, the ordered distinct pairs of
    `S` that `w` is jointly red-adjacent to are exactly the pairs of `S.offDiag` having `w` in their
    red codegree. Symmetry of the colouring is the only non-formal ingredient. -/
lemma key (v w : Fin N) :
    (K.redNbr w ∩ K.blueNbr v).offDiag
      = (K.blueNbr v).offDiag.filter (fun p => w ∈ K.redCodeg p.1 p.2) := by
  ext p
  simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_inter, mem_redNbr, mem_blueNbr,
             mem_redCodeg]
  constructor
  · rintro ⟨⟨⟨h1w, h1c⟩, h1S⟩, ⟨⟨h2w, h2c⟩, h2S⟩, hne⟩
    exact ⟨⟨h1S, h2S, hne⟩, Ne.symm h1w, Ne.symm h2w,
           by rwa [K.symm p.1 w], by rwa [K.symm p.2 w]⟩
  · rintro ⟨⟨h1S, h2S, hne⟩, hw1, hw2, hc1, hc2⟩
    exact ⟨⟨⟨Ne.symm hw1, by rwa [K.symm w p.1]⟩, h1S⟩,
           ⟨⟨Ne.symm hw2, by rwa [K.symm w p.2]⟩, h2S⟩, hne⟩

/-- THE CRUX. Both sides count the triples (w, i, j) with i ≠ j in S and w red-adjacent to both.
    `offDiag` on both sides so no natural-number subtraction ever appears. -/
theorem double_count (v : Fin N) :
    ∑ w : Fin N, ((K.redNbr w ∩ K.blueNbr v).offDiag).card
  = ∑ p ∈ (K.blueNbr v).offDiag, (K.redCodeg p.1 p.2).card := by
  classical
  simp_rw [K.key v, Finset.card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun p _ => by simp only [redCodeg, Finset.card_filter, Finset.mem_filter, Finset.mem_univ,
        true_and])

/-- Step 2, the partition. Deleting `u` from `S` splits the rest by the colour of the edge to `u`:
    the blue part is exactly the common blue neighbourhood of `v` and `u`, the red part is what
    `u` sees red inside `S`. Symmetry is again the only non-formal ingredient. -/
lemma erase_eq_union (v u : Fin N) :
    (K.blueNbr v).erase u = K.blueCodeg v u ∪ (K.redNbr u ∩ K.blueNbr v) := by
  ext x
  simp only [Finset.mem_erase, mem_blueNbr, mem_blueCodeg, Finset.mem_union, Finset.mem_inter,
             mem_redNbr]
  constructor
  · rintro ⟨hxu, hxv, hbv⟩
    by_cases h : K.C u x
    · exact Or.inl ⟨hxv, hxu, hbv, h⟩
    · exact Or.inr ⟨⟨hxu, h⟩, hxv, hbv⟩
  · rintro (⟨hxv, hxu, hbv, _⟩ | ⟨⟨hxu, _⟩, hxv, hbv⟩) <;> exact ⟨hxu, hxv, hbv⟩

lemma disj (v u : Fin N) : Disjoint (K.blueCodeg v u) (K.redNbr u ∩ K.blueNbr v) := by
  rw [Finset.disjoint_left]
  rintro x hx hx'
  simp only [mem_blueCodeg] at hx
  simp only [Finset.mem_inter, mem_redNbr] at hx'
  exact hx'.1.2 hx.2.2.2

/-- **Step 2.** Every `u` in `S` has at least `|S| - 1 - b` red neighbours inside `S`.
    At N=22, d=11, b=4 this is the "at least 6" the 6-regularity argument rests on. -/
theorem step2 (b : ℕ) (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ b)
    (v u : Fin N) (hu : u ∈ K.blueNbr v) :
    (K.blueNbr v).card - 1 - b ≤ ((K.redNbr u) ∩ (K.blueNbr v)).card := by
  have hne : v ≠ u := by simp only [mem_blueNbr] at hu; exact (Ne.symm hu.1)
  have hcard : (K.blueNbr v).card - 1
      = (K.blueCodeg v u).card + ((K.redNbr u) ∩ (K.blueNbr v)).card := by
    rw [← Finset.card_erase_of_mem hu, K.erase_eq_union v u,
        Finset.card_union_of_disjoint (K.disj v u)]
  have hcap := hb v u hne
  omega

/-- A finite set of ordered pairs that is closed under swapping and has no diagonal element has
    even cardinality: it is the disjoint union of its `<` half and its `>` half, and swapping is a
    bijection between them. This is the handshake lemma in the form the parity step needs. -/
lemma even_card_of_symm (E : Finset (Fin N × Fin N))
    (hsym : ∀ p ∈ E, (p.2, p.1) ∈ E) (hne : ∀ p ∈ E, p.1 ≠ p.2) :
    Even E.card := by
  classical
  have hsplit : E = E.filter (fun p => p.1 < p.2) ∪ E.filter (fun p => p.2 < p.1) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      rcases lt_or_gt_of_ne (hne p hp) with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hdisj : Disjoint (E.filter (fun p => p.1 < p.2)) (E.filter (fun p => p.2 < p.1)) := by
    rw [Finset.disjoint_left]
    rintro p hp hp'
    simp only [Finset.mem_filter] at hp hp'
    exact absurd (hp.2.trans hp'.2) (lt_irrefl _)
  have hbij : (E.filter (fun p => p.1 < p.2)).card = (E.filter (fun p => p.2 < p.1)).card := by
    have himg : E.filter (fun p => p.2 < p.1)
        = (E.filter (fun p => p.1 < p.2)).image Prod.swap := by
      ext p
      simp only [Finset.mem_image, Finset.mem_filter, Prod.exists, Prod.swap_prod_mk]
      constructor
      · rintro ⟨hp, hlt⟩
        exact ⟨p.2, p.1, ⟨hsym p hp, hlt⟩, rfl⟩
      · rintro ⟨a, b, ⟨hab, hlt⟩, rfl⟩
        exact ⟨hsym (a, b) hab, hlt⟩
    rw [himg, Finset.card_image_of_injective _ Prod.swap_injective]
  rw [hsplit, Finset.card_union_of_disjoint hdisj, ← hbij]
  exact ⟨_, rfl⟩

/-- The internal red degree sum over any vertex set is even. This is what makes "the baseline is
    even, so any excess is at least two" legitimate -- the step the whole 6-regularity conclusion,
    and hence the d=11 exclusion, is balanced on. -/
theorem even_internal_red_degree_sum (S : Finset (Fin N)) :
    Even (∑ u ∈ S, ((K.redNbr u) ∩ S).card) := by
  classical
  -- The bridge from the degree sum to the edge set. Both count the ordered red pairs inside S;
  -- this is the same fibrewise argument as `double_count` and is NOT where the mathematics is.
  -- Left explicit rather than hidden: see `#print axioms` below, which reports sorryAx for the
  -- theorem that uses it and NOT for `even_card_of_symm`, which is complete.
  have hbu : S.offDiag.filter (fun p => ¬ K.C p.1 p.2)
      = S.biUnion (fun u => ((K.redNbr u ∩ S).image (fun x => (u, x)))) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_biUnion, Finset.mem_image,
               Finset.mem_inter, mem_redNbr]
    constructor
    · rintro ⟨⟨h1, h2, hne⟩, hc⟩
      exact ⟨p.1, h1, p.2, ⟨⟨Ne.symm hne, hc⟩, h2⟩, rfl⟩
    · rintro ⟨u, hu, x, ⟨⟨hxu, hcx⟩, hxS⟩, rfl⟩
      exact ⟨⟨hu, hxS, Ne.symm hxu⟩, hcx⟩
  have hdisj : ∀ u ∈ S, ∀ w ∈ S, u ≠ w →
      Disjoint ((K.redNbr u ∩ S).image (fun x => (u, x)))
               ((K.redNbr w ∩ S).image (fun x => (w, x))) := by
    intro u _ w _ huw
    rw [Finset.disjoint_left]
    rintro p hp hp'
    simp only [Finset.mem_image] at hp hp'
    obtain ⟨a, _, rfl⟩ := hp
    obtain ⟨b, _, hb⟩ := hp'
    exact huw (congrArg Prod.fst hb).symm
  have : ∑ u ∈ S, ((K.redNbr u) ∩ S).card
       = (S.offDiag.filter (fun p => ¬ K.C p.1 p.2)).card := by
    rw [hbu, Finset.card_biUnion hdisj]
    exact Finset.sum_congr rfl (fun u _ =>
      (Finset.card_image_of_injective _ (fun a b h => by simpa using h)).symm)
  rw [this]
  refine even_card_of_symm _ ?_ ?_
  · rintro p hp
    simp only [Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
    exact ⟨⟨hp.1.2.1, hp.1.1, (Ne.symm hp.1.2.2)⟩, by rw [K.symm p.2 p.1]; exact hp.2⟩
  · rintro p hp; simp only [Finset.mem_filter, Finset.mem_offDiag] at hp; exact hp.1.2.2

/-- `S` and `T` are disjoint: a vertex is blue- or red-adjacent to the root, never both. -/
lemma blue_red_disjoint (v : Fin N) : Disjoint (K.blueNbr v) (K.redNbr v) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [mem_blueNbr] at hx
  simp only [mem_redNbr] at hx'
  exact hx'.2 hx.2

/-- Step 3, the partition. For `w` outside `S`, the blue part of `S` seen from `w` is exactly the
    common blue neighbourhood of `v` and `w`; the rest of `S` is red to `w`.

    Note `hw : w ∈ K.redNbr v` carries `w ≠ v` as well as `w ∉ S`. Both are needed: `w ∉ S` is what
    stops a vertex being deleted (the difference from step 2), and `w ≠ v` matters because the root
    has NO red neighbours inside `S` at all, so admitting it would make the bound false. -/
lemma S_eq_union (v w : Fin N) (hw : w ∈ K.redNbr v) :
    K.blueNbr v = K.blueCodeg v w ∪ (K.redNbr w ∩ K.blueNbr v) := by
  ext x
  simp only [mem_blueNbr, mem_blueCodeg, Finset.mem_union, Finset.mem_inter, mem_redNbr]
  constructor
  · rintro ⟨hxv, hbv⟩
    have hxw : x ≠ w := by
      rintro rfl
      simp only [mem_redNbr] at hw
      exact hw.2 hbv
    by_cases h : K.C w x
    · exact Or.inl ⟨hxv, hxw, hbv, h⟩
    · exact Or.inr ⟨⟨hxw, h⟩, hxv, hbv⟩
  · rintro (⟨hxv, _, hbv, _⟩ | ⟨_, hxv, hbv⟩) <;> exact ⟨hxv, hbv⟩

lemma S_disj (v w : Fin N) : Disjoint (K.blueCodeg v w) (K.redNbr w ∩ K.blueNbr v) := by
  rw [Finset.disjoint_left]
  rintro x hx hx'
  simp only [mem_blueCodeg] at hx
  simp only [Finset.mem_inter, mem_redNbr] at hx'
  exact hx'.1.2 hx.2.2.2

/-- **Step 3.** Every `w` in `T` has at least `|S| - b` red neighbours inside `S`.
    At N=22, d=11, b=4 this is the "at least seven" the cross-edge count needs. One MORE than
    step 2 gives inside `S`, because no vertex is deleted. -/
theorem step3 (b : ℕ) (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ b)
    (v w : Fin N) (hw : w ∈ K.redNbr v) :
    (K.blueNbr v).card - b ≤ ((K.redNbr w) ∩ (K.blueNbr v)).card := by
  have hne : v ≠ w := by
    simp only [mem_redNbr] at hw; exact (Ne.symm hw.1)
  have hcard : (K.blueNbr v).card
      = (K.blueCodeg v w).card + ((K.redNbr w) ∩ (K.blueNbr v)).card := by
    conv_lhs => rw [K.S_eq_union v w hw]
    rw [Finset.card_union_of_disjoint (K.S_disj v w)]
  have hcap := hb v w hne
  omega

/-- Red adjacency is symmetric as a membership statement. Needed because `redNbr` is defined from
    the colouring's first argument, so `w ∈ redNbr u` and `u ∈ redNbr w` are different expressions
    that happen to agree. -/
lemma red_mem_symm (u w : Fin N) : w ∈ K.redNbr u ↔ u ∈ K.redNbr w := by
  simp only [mem_redNbr]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h1, by rw [K.symm w u]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h1, by rw [K.symm u w]; exact h2⟩

/-- **The cross-edge identity** (round 33 named this as missing). Counting the red edges between
    two vertex sets from the `A` side and from the `B` side gives the same number.

    This is step 13's engine: summing step 12 over `S` bounds the red `S`-`T` edges ABOVE, summing
    step 3 over `T` bounds them BELOW, and at N=22, d=11 those are 66 and 70. Note both sides count
    each edge ONCE -- this identity is not doubled, unlike the `offDiag` counts. -/
theorem cross_count (A B : Finset (Fin N)) :
    ∑ u ∈ A, ((K.redNbr u) ∩ B).card = ∑ w ∈ B, ((K.redNbr w) ∩ A).card := by
  classical
  have ind : ∀ (X : Finset (Fin N)) (u : Fin N),
      ((K.redNbr u) ∩ X).card = ∑ x ∈ X, (if x ∈ K.redNbr u then 1 else 0) := by
    intro X u
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
  simp_rw [ind B, ind A]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun u _ => ?_))
  exact if_congr (K.red_mem_symm u w) rfl rfl

/-- The red codegree IS the intersection of the two red neighbourhoods. Obvious, but it is what
    lets the fixed-vertex identity below reuse `cross_count` instead of needing its own proof. -/
lemma redCodeg_eq_inter (i j : Fin N) : K.redCodeg i j = K.redNbr i ∩ K.redNbr j := by
  ext w
  simp only [mem_redCodeg, Finset.mem_inter, mem_redNbr]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨h1, h3, h2, h4⟩

/-- **The fixed-vertex incidence identity** — round 33's other named gap, and it turns out to be a
    COROLLARY of `cross_count` rather than new work.

    `L_u`, the sum of `u`'s red codegrees over a set `X`, counted the other way: each red neighbour
    `z` of `u` contributes the vertices of `X` it is red to. Hand steps 9-11 are exactly this with
    `X = S \ {u}`, split into `z` inside `S` and `z` inside `T`. -/
theorem L_identity (u : Fin N) (X : Finset (Fin N)) :
    ∑ x ∈ X, (K.redCodeg u x).card = ∑ z ∈ K.redNbr u, ((K.redNbr z) ∩ X).card := by
  have h : ∀ x, (K.redCodeg u x).card = ((K.redNbr x) ∩ (K.redNbr u)).card := by
    intro x; rw [K.redCodeg_eq_inter, Finset.inter_comm]
  simp_rw [h]
  exact K.cross_count X (K.redNbr u)

/-- The vertex set splits as `{v} ⊔ S ⊔ T`. Needed to know `|T| = 10` once `|S| = 11` at N = 22;
    the hand proof states that in passing and it is not free here. -/
lemma card_partition (v : Fin N) : (K.blueNbr v).card + (K.redNbr v).card + 1 = N := by
  classical
  have hu : K.blueNbr v ∪ K.redNbr v = Finset.univ.erase v := by
    ext x
    simp only [Finset.mem_union, mem_blueNbr, mem_redNbr, Finset.mem_erase, Finset.mem_univ,
               and_true]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hc : K.C v x
      · exact Or.inl ⟨h, hc⟩
      · exact Or.inr ⟨h, hc⟩
  have hcard := Finset.card_union_of_disjoint (K.blue_red_disjoint v)
  rw [hu, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin] at hcard
  have : 0 < N := Fin.pos v
  omega

/-- For `u ∈ S`, the root is NOT a red neighbour of `u` (the edge `vu` is blue), so `u`'s red
    neighbourhood lies entirely in `S ∪ T` and splits cleanly. -/
lemma redNbr_split (v u : Fin N) (hu : u ∈ K.blueNbr v) :
    K.redNbr u = (K.redNbr u ∩ K.blueNbr v) ∪ (K.redNbr u ∩ K.redNbr v) := by
  ext z
  simp only [Finset.mem_union, Finset.mem_inter, mem_blueNbr, mem_redNbr]
  constructor
  · rintro ⟨hzu, hc⟩
    have hzv : z ≠ v := by
      rintro rfl
      simp only [mem_blueNbr] at hu
      rw [K.symm u z] at hc; exact hc hu.2
    by_cases h : K.C v z
    · exact Or.inl ⟨⟨hzu, hc⟩, hzv, h⟩
    · exact Or.inr ⟨⟨hzu, hc⟩, hzv, h⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

lemma redNbr_split_disj (v u : Fin N) :
    Disjoint (K.redNbr u ∩ K.blueNbr v) (K.redNbr u ∩ K.redNbr v) := by
  rw [Finset.disjoint_left]
  rintro x hx hx'
  simp only [Finset.mem_inter, mem_blueNbr] at hx
  simp only [Finset.mem_inter, mem_redNbr] at hx'
  exact hx'.2.2 hx.2.2

/-- Deleting `u` from `S` costs a red neighbour of `u` exactly one, because `u` is one of its own
    red neighbours' red neighbours. This is where `red_mem_symm` earns its place. -/
lemma card_inter_erase (u z : Fin N) (hz : z ∈ K.redNbr u) (S : Finset (Fin N)) (hu : u ∈ S) :
    ((K.redNbr z) ∩ S).card = ((K.redNbr z) ∩ (S.erase u)).card + 1 := by
  classical
  have huz : u ∈ K.redNbr z := (K.red_mem_symm u z).mp hz
  have : (K.redNbr z) ∩ S = insert u ((K.redNbr z) ∩ (S.erase u)) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hxu : x = u
      · exact Or.inl hxu
      · exact Or.inr ⟨h1, hxu, h2⟩
    · rintro (rfl | ⟨h1, _, h2⟩)
      · exact ⟨huz, hu⟩
      · exact ⟨h1, h2⟩
  rw [this, Finset.card_insert_of_notMem (by simp)]

/-- **Step 12, in general form.** Write `|S| = m + 1 + b`, so `m = |S| - 1 - b` is the internal
    bound step 2 gives. Then for every `u` in `S`,

        m*(m-1) + m*l  ≤  r*(m+b),   where l = |N_R(u) ∩ T|.

    `L_u` is capped at `r*(|S|-1) = r*(m+b)`. Counted by `u`'s red neighbours: each one inside `S`
    sees at least `m` of `S`, so at least `m-1` after deleting `u`; each one inside `T` sees at
    least `m+1`, so at least `m`. With at least `m` red neighbours inside `S`, the lower bound is
    `m*(m-1) + m*l`.

    Both halves of Lemma 1.2 are this lemma. d = 11 is `(m,b,r) = (6,4,7)`: `30 + 6l ≤ 70`, `l ≤ 6`.
    d = 7, via the colour swap, is `(m,b,r) = (6,7,4)`: `30 + 6l ≤ 52`, `l ≤ 3`. That `m = 6` in
    both is why the two halves look alike.

    The counts here are of EDGES, once each — not doubled like the `offDiag` sums. -/
theorem step12 (b r m : ℕ)
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ b)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ r)
    (v : Fin N) (hS : (K.blueNbr v).card = m + 1 + b)
    (u : Fin N) (hu : u ∈ K.blueNbr v) :
    m * (m - 1) + m * ((K.redNbr u) ∩ K.redNbr v).card ≤ r * (m + b) := by
  classical
  have hX : ((K.blueNbr v).erase u).card = m + b := by
    rw [Finset.card_erase_of_mem hu, hS]; omega
  have hupper : ∑ x ∈ (K.blueNbr v).erase u, (K.redCodeg u x).card ≤ r * (m + b) := by
    calc ∑ x ∈ (K.blueNbr v).erase u, (K.redCodeg u x).card
        ≤ ∑ _x ∈ (K.blueNbr v).erase u, r :=
          Finset.sum_le_sum (fun x hx => hr u x (Ne.symm (Finset.mem_erase.mp hx).1))
      _ = (m + b) * r := by rw [Finset.sum_const_nat (fun _ _ => rfl), hX]
      _ = r * (m + b) := Nat.mul_comm _ _
  have hsplit : ∑ z ∈ K.redNbr u, ((K.redNbr z) ∩ (K.blueNbr v).erase u).card
      = ∑ z ∈ (K.redNbr u ∩ K.blueNbr v), ((K.redNbr z) ∩ (K.blueNbr v).erase u).card
      + ∑ z ∈ (K.redNbr u ∩ K.redNbr v), ((K.redNbr z) ∩ (K.blueNbr v).erase u).card := by
    conv_lhs => rw [K.redNbr_split v u hu]
    exact Finset.sum_union (K.redNbr_split_disj v u)
  have hin : ∀ z ∈ K.redNbr u ∩ K.blueNbr v,
      m - 1 ≤ ((K.redNbr z) ∩ (K.blueNbr v).erase u).card := by
    intro z hz
    have h2 := K.step2 b hb v z (Finset.mem_inter.mp hz).2
    have he := K.card_inter_erase u z (Finset.mem_inter.mp hz).1 (K.blueNbr v) hu
    rw [hS] at h2; omega
  have hout : ∀ z ∈ K.redNbr u ∩ K.redNbr v,
      m ≤ ((K.redNbr z) ∩ (K.blueNbr v).erase u).card := by
    intro z hz
    have h3 := K.step3 b hb v z (Finset.mem_inter.mp hz).2
    have he := K.card_inter_erase u z (Finset.mem_inter.mp hz).1 (K.blueNbr v) hu
    rw [hS] at h3; omega
  have hm : m ≤ (K.redNbr u ∩ K.blueNbr v).card := by
    have h := K.step2 b hb v u hu; rw [hS] at h; omega
  calc m * (m - 1) + m * ((K.redNbr u) ∩ K.redNbr v).card
      ≤ ∑ z ∈ (K.redNbr u ∩ K.blueNbr v), ((K.redNbr z) ∩ (K.blueNbr v).erase u).card
        + ∑ z ∈ (K.redNbr u ∩ K.redNbr v), ((K.redNbr z) ∩ (K.blueNbr v).erase u).card := by
        refine Nat.add_le_add ?_ ?_
        · calc m * (m - 1) ≤ (K.redNbr u ∩ K.blueNbr v).card * (m - 1) :=
                Nat.mul_le_mul_right _ hm
            _ = ∑ _z ∈ (K.redNbr u ∩ K.blueNbr v), (m - 1) := by
                rw [Finset.sum_const_nat (fun _ _ => rfl)]
            _ ≤ _ := Finset.sum_le_sum hin
        · calc m * ((K.redNbr u) ∩ K.redNbr v).card
              = ∑ _z ∈ (K.redNbr u ∩ K.redNbr v), m := by
                rw [Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
            _ ≤ _ := Finset.sum_le_sum hout
    _ = ∑ z ∈ K.redNbr u, ((K.redNbr z) ∩ (K.blueNbr v).erase u).card := hsplit.symm
    _ = ∑ x ∈ (K.blueNbr v).erase u, (K.redCodeg u x).card :=
        (K.L_identity u ((K.blueNbr v).erase u)).symm
    _ ≤ r * (m + b) := hupper

/-- **Step 13, in general form.** Summing step 12's per-vertex cap `L` over `S` bounds the red
    `S`-`T` edges above by `|S| * L`; summing `step3` over `T` bounds them below by `|T| * (|S|-b)`;
    `cross_count` says the two are the same number. If the lower beats the upper, contradiction.

    d = 11: `11*6 = 66 < 70 = 10*7`.  d = 7 swapped: `14*3 = 42 < 49 = 7*7`.
    Each edge is counted ONCE on both sides — these sums are not doubled. -/
theorem step13 (b m t L : ℕ)
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ b)
    (v : Fin N) (hS : (K.blueNbr v).card = m + 1 + b) (hT : (K.redNbr v).card = t)
    (h12 : ∀ u ∈ K.blueNbr v, ((K.redNbr u) ∩ K.redNbr v).card ≤ L)
    (hgap : (m + 1 + b) * L < t * (m + 1)) : False := by
  classical
  have hup : ∑ u ∈ K.blueNbr v, ((K.redNbr u) ∩ K.redNbr v).card ≤ (m + 1 + b) * L := by
    calc ∑ u ∈ K.blueNbr v, ((K.redNbr u) ∩ K.redNbr v).card
        ≤ ∑ _u ∈ K.blueNbr v, L := Finset.sum_le_sum h12
      _ = (m + 1 + b) * L := by rw [Finset.sum_const_nat (fun _ _ => rfl), hS]
  have hlow : t * (m + 1) ≤ ∑ w ∈ K.redNbr v, ((K.redNbr w) ∩ K.blueNbr v).card := by
    calc t * (m + 1) = ∑ _w ∈ K.redNbr v, (m + 1) := by
          rw [Finset.sum_const_nat (fun _ _ => rfl), hT]
      _ ≤ ∑ w ∈ K.redNbr v, ((K.redNbr w) ∩ K.blueNbr v).card := by
          refine Finset.sum_le_sum (fun w hw => ?_)
          have h3 := K.step3 b hb v w hw
          rw [hS] at h3; omega
  have heq := K.cross_count (K.blueNbr v) (K.redNbr v)
  omega

/-- **THE d = 11 EXCLUSION.** No vertex of a good colouring of K_22 has blue degree 11.

    `hb` and `hr` are exactly "the colouring is good": no blue K_{2,5} caps every pair at 4 common
    blue neighbours, no red K_{2,8} caps them at 7 common red. Nothing else is assumed — in
    particular NOT that degrees already lie in {8,9,10}, which is what this helps establish. -/
theorem degree_eleven_impossible
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ 4)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ 7)
    (hN : N = 22) (v : Fin N) : (K.blueNbr v).card ≠ 11 := by
  intro hS
  have hpart := K.card_partition v
  have hT : (K.redNbr v).card = 10 := by omega
  have hS' : (K.blueNbr v).card = 6 + 1 + 4 := by omega
  refine K.step13 4 6 10 6 hb v hS' hT (fun u hu => ?_) (by norm_num)
  have := K.step12 4 7 6 hb hr v hS' u hu
  omega

/-- **THE d = 7 EXCLUSION**, obtained from the SAME lemmas by swapping the colours.

    Under the swap the blue neighbourhood becomes the red one, so `|blueNbr K' v| = 14`, and the
    caps trade places: `(b,r) = (4,7)` for `K` becomes `(7,4)` for `K'`. Step 12 then reads
    `30 + 6l ≤ 4*13 = 52`, so `l ≤ 3` — the hand argument's `k ≤ 3` — and step 13 closes on
    `14*3 = 42 < 49 = 7*7`.

    The hand proof presents d = 7 as a separate thirteen-step argument working in BLUE on `T`.
    It is the d = 11 argument at different parameters. -/
theorem degree_seven_impossible
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ 4)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ 7)
    (hN : N = 22) (v : Fin N) : (K.blueNbr v).card ≠ 7 := by
  intro hS
  have hpart := K.card_partition v
  have hT : (K.redNbr v).card = 14 := by omega
  -- transport to the swapped colouring: its blue neighbourhood is K's red one
  have hb' : ∀ i j, i ≠ j → ((K.swap).blueCodeg i j).card ≤ 7 := by
    intro i j hij; rw [swap_blueCodeg]; exact hr i j hij
  have hr' : ∀ i j, i ≠ j → ((K.swap).redCodeg i j).card ≤ 4 := by
    intro i j hij; rw [swap_redCodeg]; exact hb i j hij
  have hS' : ((K.swap).blueNbr v).card = 6 + 1 + 7 := by rw [swap_blueNbr]; omega
  have hT' : ((K.swap).redNbr v).card = 7 := by rw [swap_redNbr]; omega
  refine (K.swap).step13 7 6 7 3 hb' v hS' hT' (fun u hu => ?_) (by norm_num)
  have := (K.swap).step12 7 4 6 hb' hr' v hS' u hu
  omega

end Colouring

#print axioms DegreeLemma.pairs_growth
#print axioms DegreeLemma.even_excess
#print axioms DegreeLemma.step7_core
#print axioms Colouring.key
#print axioms Colouring.double_count
#print axioms Colouring.step2
#print axioms Colouring.step3
#print axioms Colouring.cross_count
#print axioms Colouring.L_identity
#print axioms Colouring.card_partition
#print axioms Colouring.step12
#print axioms Colouring.step13
#print axioms Colouring.degree_eleven_impossible
#print axioms Colouring.degree_seven_impossible
#print axioms Colouring.even_card_of_symm
#print axioms Colouring.even_internal_red_degree_sum

#print axioms Colouring.swap_blueNbr
#print axioms Colouring.swap_blueCodeg


/-! ## Bridge to the verified encoder-soundness portfolio (`Sbsound/`) -/

namespace Colouring
open SB Finset

variable {N : ℕ}

/-- Reading it as an edge colouring: blue = 1, red = 0. -/
def toE (K : Colouring N) : EColouring N 2 :=
  fun e => if K.C (ofLex e.val).1 (ofLex e.val).2 then 1 else 0

/-- Blue adjacency in the edge colouring is just `K.C`, in either order. -/
lemma colourRel_toE_one (K : Colouring N) {i j : Fin N} (hij : i ≠ j) :
    colourRel (toE K) 1 i j ↔ K.C i j := by
  constructor
  · rintro ⟨h, he⟩
    simp only [toE, mkEdge] at he
    by_cases hlt : i < j
    · simp [hlt] at he; simpa [hlt] using he
    · have : j < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij)
      simp [hlt, this] at he
      rw [K.symm i j]; simpa [hlt, this] using he
  · intro hc
    refine ⟨hij, ?_⟩
    simp only [toE, mkEdge]
    by_cases hlt : i < j
    · simp [hlt, hc]
    · have : j < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij)
      simp [hlt, this]
      rw [← K.symm i j]; simpa using hc

/-- **Codegree correspondence.** SB's common-neighbourhood of the pair `{i,j}` is exactly the
    `Lemma12` blue codegree set. This is what turns `NoKst _ 1 2 t` — no blue `K_{2,t}` — into the
    cap `blueCodeg ≤ t-1` that every proof in `Lemma12.lean` assumes. -/
lemma commonNbrs_toE_pair (K : Colouring N) (i j : Fin N) :
    commonNbrs (toE K) 1 {i, j} = K.blueCodeg i j := by
  ext w
  simp only [commonNbrs, blueCodeg, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
             not_or, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨⟨hwi, hwj⟩, hi, hj⟩
    exact ⟨hwi, hwj, (colourRel_toE_one K (Ne.symm hwi)).mp hi,
           (colourRel_toE_one K (Ne.symm hwj)).mp hj⟩
  · rintro ⟨hwi, hwj, hci, hcj⟩
    exact ⟨⟨hwi, hwj⟩, (colourRel_toE_one K (Ne.symm hwi)).mpr hci,
           (colourRel_toE_one K (Ne.symm hwj)).mpr hcj⟩

/-- **Degree correspondence.** -/
lemma deg_toE_one (K : Colouring N) (v : Fin N) :
    deg (toE K) 1 v = (K.blueNbr v).card := by
  unfold deg blueNbr
  congr 1
  ext w
  simp only [mem_filter, mem_univ, true_and, colourGraph_adj]
  constructor
  · rintro ⟨hne, he⟩
    exact ⟨Ne.symm hne, (colourRel_toE_one K hne).mp ⟨hne, he⟩⟩
  · rintro ⟨hwv, hc⟩
    exact (colourRel_toE_one K (Ne.symm hwv)).mpr hc

#print axioms Colouring.colourRel_toE_one
#print axioms Colouring.commonNbrs_toE_pair
#print axioms Colouring.deg_toE_one

/-- Red adjacency: the other colour. -/
lemma colourRel_toE_zero (K : Colouring N) {i j : Fin N} (hij : i ≠ j) :
    colourRel (toE K) 0 i j ↔ ¬ K.C i j := by
  constructor
  · rintro ⟨h, he⟩ hc
    have := (colourRel_toE_one K hij).mpr hc
    obtain ⟨h1, he1⟩ := this
    rw [he1] at he; exact absurd he (by decide)
  · intro hc
    refine ⟨hij, ?_⟩
    simp only [toE, mkEdge]
    by_cases hlt : i < j
    · simp [hlt]; simpa [hlt] using hc
    · have hji : j < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij)
      simp [hlt, hji]; rw [← K.symm i j]; simpa using hc

lemma commonNbrs_toE_pair_red (K : Colouring N) (i j : Fin N) :
    commonNbrs (toE K) 0 {i, j} = K.redCodeg i j := by
  ext w
  simp only [commonNbrs, redCodeg, mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
             not_or, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨⟨hwi, hwj⟩, hi, hj⟩
    exact ⟨hwi, hwj, (colourRel_toE_zero K (Ne.symm hwi)).mp hi,
           (colourRel_toE_zero K (Ne.symm hwj)).mp hj⟩
  · rintro ⟨hwi, hwj, hci, hcj⟩
    exact ⟨⟨hwi, hwj⟩, (colourRel_toE_zero K (Ne.symm hwi)).mpr hci,
           (colourRel_toE_zero K (Ne.symm hwj)).mpr hcj⟩

/-- A `NoKst` hypothesis in SB's language IS the codegree cap this file's proofs assume. -/
lemma cap_of_NoKst_blue (K : Colouring N) (t : ℕ) (h : NoKst (toE K) 1 2 t)
    {i j : Fin N} (hij : i ≠ j) : (K.blueCodeg i j).card ≤ t - 1 := by
  have hs := (codegree_iff (toE K) 1 2 t).mp h {i, j}
    (mem_powersetCard.mpr ⟨subset_univ _, Finset.card_pair hij⟩)
  rw [commonNbrs_toE_pair] at hs; omega

lemma cap_of_NoKst_red (K : Colouring N) (t : ℕ) (h : NoKst (toE K) 0 2 t)
    {i j : Fin N} (hij : i ≠ j) : (K.redCodeg i j).card ≤ t - 1 := by
  have hs := (codegree_iff (toE K) 0 2 t).mp h {i, j}
    (mem_powersetCard.mpr ⟨subset_univ _, Finset.card_pair hij⟩)
  rw [commonNbrs_toE_pair_red] at hs; omega

/-- **THE DEGREE LEMMA, IN THE VERIFIED PORTFOLIO'S LANGUAGE.**

    For any colouring of K22 containing no blue `K_{2,5}` and no red `K_{2,8}` -- stated with SB's
    `NoKst`, the same predicate `Sbsound/Portfolio.lean` proves the encoder sound against -- no
    vertex has blue degree 7 or 11.

    This is what connects the two halves. `Lemma12` proved the narrowing over its own `Colouring`
    structure; `Sbsound` proves the encoding sound over `EColouring`. Until now nothing said they
    were about the same objects. -/
theorem degrees_avoid_seven_and_eleven (K : Colouring N) (hN : N = 22)
    (hblue : NoKst (toE K) 1 2 5) (hred : NoKst (toE K) 0 2 8) (v : Fin N) :
    (K.blueNbr v).card ≠ 7 ∧ (K.blueNbr v).card ≠ 11 := by
  have hb : ∀ i j : Fin N, i ≠ j → (K.blueCodeg i j).card ≤ 4 :=
    fun i j hij => cap_of_NoKst_blue K 5 hblue hij
  have hr : ∀ i j : Fin N, i ≠ j → (K.redCodeg i j).card ≤ 7 :=
    fun i j hij => cap_of_NoKst_red K 8 hred hij
  exact ⟨K.degree_seven_impossible hb hr hN v, K.degree_eleven_impossible hb hr hN v⟩

#print axioms Colouring.cap_of_NoKst_blue
#print axioms Colouring.cap_of_NoKst_red
#print axioms Colouring.degrees_avoid_seven_and_eleven

/-! ## The counting inequality (1.3), in general

`counting_bound.py` implements three double counts. The third,

    d * C(d-b-1, 2) + s * C(d-b, 2)  ≤  r * C(d, 2)

is exactly what `step2`, `step3` and `double_count` already supply, and in doubled form it needs no
binomial coefficients. At N = 22, b = 4, r = 7 it excludes every blue degree from 12 up (at d = 12:
1008 > 924), and by the colour swap it excludes 6 and below. -/

variable (K : Colouring N)

lemma offDiag_card' {α : Type*} [DecidableEq α] (s : Finset α) :
    s.offDiag.card = s.card * (s.card - 1) := by
  rw [Finset.offDiag_card, Nat.mul_sub_one]

lemma univ_split (v : Fin N) :
    (Finset.univ : Finset (Fin N)) = insert v (K.blueNbr v ∪ K.redNbr v) := by
  ext x
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_union, mem_blueNbr,
             mem_redNbr]
  by_cases hxv : x = v
  · exact Or.inl hxv
  · by_cases hc : K.C v x
    · exact Or.inr (Or.inl ⟨hxv, hc⟩)
    · exact Or.inr (Or.inr ⟨hxv, hc⟩)

/-- **Counting inequality (1.3), doubled.** -/
theorem counting_13 (b r m : ℕ)
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ b)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ r)
    (v : Fin N) (hS : (K.blueNbr v).card = m + 1 + b) :
    (K.blueNbr v).card * (m * (m - 1)) + (K.redNbr v).card * ((m + 1) * m)
      ≤ r * ((K.blueNbr v).card * ((K.blueNbr v).card - 1)) := by
  classical
  have hup : ∑ p ∈ (K.blueNbr v).offDiag, (K.redCodeg p.1 p.2).card
      ≤ r * ((K.blueNbr v).card * ((K.blueNbr v).card - 1)) := by
    calc ∑ p ∈ (K.blueNbr v).offDiag, (K.redCodeg p.1 p.2).card
        ≤ ∑ _p ∈ (K.blueNbr v).offDiag, r :=
          Finset.sum_le_sum (fun p hp => hr p.1 p.2 (Finset.mem_offDiag.mp hp).2.2)
      _ = (K.blueNbr v).offDiag.card * r := by rw [Finset.sum_const_nat (fun _ _ => rfl)]
      _ = r * ((K.blueNbr v).card * ((K.blueNbr v).card - 1)) := by rw [offDiag_card']; ring
  have hvS : v ∉ K.blueNbr v ∪ K.redNbr v := by
    simp only [Finset.mem_union, mem_blueNbr, mem_redNbr]
    rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h rfl
  have hin : ∀ u ∈ K.blueNbr v,
      m * (m - 1) ≤ ((K.redNbr u) ∩ K.blueNbr v).offDiag.card := by
    intro u hu
    have h2 := K.step2 b hb v u hu
    rw [hS] at h2
    rw [offDiag_card']
    exact Nat.mul_le_mul (by omega) (by omega)
  have hout : ∀ w ∈ K.redNbr v,
      (m + 1) * m ≤ ((K.redNbr w) ∩ K.blueNbr v).offDiag.card := by
    intro w hw
    have h3 := K.step3 b hb v w hw
    rw [hS] at h3
    rw [offDiag_card']
    exact Nat.mul_le_mul (by omega) (by omega)
  have hlow : (K.blueNbr v).card * (m * (m - 1)) + (K.redNbr v).card * ((m + 1) * m)
      ≤ ∑ w : Fin N, ((K.redNbr w) ∩ K.blueNbr v).offDiag.card := by
    rw [show (Finset.univ : Finset (Fin N)) = insert v (K.blueNbr v ∪ K.redNbr v) from
          K.univ_split v,
        Finset.sum_insert hvS, Finset.sum_union (K.blue_red_disjoint v)]
    have c1 : (K.blueNbr v).card * (m * (m - 1))
        ≤ ∑ u ∈ K.blueNbr v, ((K.redNbr u) ∩ K.blueNbr v).offDiag.card := by
      calc (K.blueNbr v).card * (m * (m - 1))
          = ∑ _u ∈ K.blueNbr v, (m * (m - 1)) := by
            rw [Finset.sum_const_nat (fun _ _ => rfl)]
        _ ≤ _ := Finset.sum_le_sum hin
    have c2 : (K.redNbr v).card * ((m + 1) * m)
        ≤ ∑ w ∈ K.redNbr v, ((K.redNbr w) ∩ K.blueNbr v).offDiag.card := by
      calc (K.redNbr v).card * ((m + 1) * m)
          = ∑ _w ∈ K.redNbr v, ((m + 1) * m) := by
            rw [Finset.sum_const_nat (fun _ _ => rfl)]
        _ ≤ _ := Finset.sum_le_sum hout
    omega
  have hdc := K.double_count v
  omega

#print axioms Colouring.counting_13

/-- Blue degree at most 11, from the counting inequality alone. At N = 22 with caps (4,7) the
    inequality fails for every d from 12 up -- at d = 12 by 1008 against 924, widening after. -/
theorem degree_lt_twelve
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ 4)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ 7)
    (hN : N = 22) (v : Fin N) : (K.blueNbr v).card < 12 := by
  by_contra hge
  push_neg at hge
  have hpart := K.card_partition v
  have hd21 : (K.blueNbr v).card ≤ 21 := by omega
  have key := K.counting_13 4 7 ((K.blueNbr v).card - 5) hb hr v (by omega)
  have hT : (K.redNbr v).card = 21 - (K.blueNbr v).card := by omega
  rw [hT] at key
  set d := (K.blueNbr v).card with hd
  interval_cases d <;> norm_num at key

#print axioms Colouring.degree_lt_twelve

/-- Blue degree at least 7, by applying the same inequality to the swapped colouring. Under the
    swap the caps trade places to (7,4) and the blue neighbourhood becomes the red one, so a blue
    degree of d becomes a swapped blue degree of 21 - d; for d ≤ 6 that is 15 or more, where the
    inequality fails (at d = 6: 966 against 840). -/
theorem degree_gt_six
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ 4)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ 7)
    (hN : N = 22) (v : Fin N) : 6 < (K.blueNbr v).card := by
  by_contra hle
  push_neg at hle
  have hb' : ∀ i j : Fin N, i ≠ j → ((K.swap).blueCodeg i j).card ≤ 7 := by
    intro i j hij; rw [swap_blueCodeg]; exact hr i j hij
  have hr' : ∀ i j : Fin N, i ≠ j → ((K.swap).redCodeg i j).card ≤ 4 := by
    intro i j hij; rw [swap_redCodeg]; exact hb i j hij
  have hpart := K.card_partition v
  have hsb : ((K.swap).blueNbr v).card = (K.redNbr v).card := by rw [swap_blueNbr]
  have hsr : ((K.swap).redNbr v).card = (K.blueNbr v).card := by rw [swap_redNbr]
  have key := (K.swap).counting_13 7 4 (((K.swap).blueNbr v).card - 8) hb' hr' v (by omega)
  rw [hsb, hsr] at key
  have hT : (K.redNbr v).card = 21 - (K.blueNbr v).card := by omega
  rw [hT] at key
  set d := (K.blueNbr v).card with hd
  interval_cases d <;> norm_num at key

/-- **THE DEGREE LEMMA, COMPLETE.** Every vertex of a good colouring of K22 has blue degree
    8, 9 or 10 -- no step of it cited, all of it machine-checked here. -/
theorem degree_in_eight_nine_ten
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ 4)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ 7)
    (hN : N = 22) (v : Fin N) :
    (K.blueNbr v).card = 8 ∨ (K.blueNbr v).card = 9 ∨ (K.blueNbr v).card = 10 := by
  have h1 := K.degree_gt_six hb hr hN v
  have h2 := K.degree_lt_twelve hb hr hN v
  have h7 := K.degree_seven_impossible hb hr hN v
  have h11 := K.degree_eleven_impossible hb hr hN v
  omega

#print axioms Colouring.degree_gt_six
#print axioms Colouring.degree_in_eight_nine_ten

/-! ## Generalised double count, over an arbitrary vertex set

Round 35 identified this as the enabler for the class-size bounds `n8 ≤ 7` and `n10 ≤ 10`, which
the degree lemma does NOT give. `key` and `double_count` were stated for `Q = blueNbr v`, but
neither proof uses anything about that set beyond its being a `Finset`. -/

lemma key_gen (Q : Finset (Fin N)) (w : Fin N) :
    (K.redNbr w ∩ Q).offDiag = Q.offDiag.filter (fun p => w ∈ K.redCodeg p.1 p.2) := by
  ext p
  simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_inter, mem_redNbr, mem_redCodeg]
  constructor
  · rintro ⟨⟨⟨h1w, h1c⟩, h1Q⟩, ⟨⟨h2w, h2c⟩, h2Q⟩, hne⟩
    exact ⟨⟨h1Q, h2Q, hne⟩, Ne.symm h1w, Ne.symm h2w,
           by rwa [K.symm p.1 w], by rwa [K.symm p.2 w]⟩
  · rintro ⟨⟨h1Q, h2Q, hne⟩, hw1, hw2, hc1, hc2⟩
    exact ⟨⟨⟨Ne.symm hw1, by rwa [K.symm w p.1]⟩, h1Q⟩,
           ⟨⟨Ne.symm hw2, by rwa [K.symm w p.2]⟩, h2Q⟩, hne⟩

/-- **Double count over an arbitrary `Q`.** -/
theorem double_count_gen (Q : Finset (Fin N)) :
    ∑ w : Fin N, ((K.redNbr w ∩ Q).offDiag).card
  = ∑ p ∈ Q.offDiag, (K.redCodeg p.1 p.2).card := by
  classical
  simp_rw [K.key_gen Q, Finset.card_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun p _ => by
    simp only [redCodeg, Finset.card_filter, Finset.mem_filter, Finset.mem_univ, true_and])

#print axioms Colouring.double_count_gen

/-! ## Toward the class-size bounds `n8 ≤ 7` and `n10 ≤ 10`

The 44 histograms need these, and `degree_in_eight_nine_ten` does not give them (Astra round 35).
The route is a second-moment bound over an arbitrary vertex set, which splits into two pieces that
`double_count_gen` and `cross_count` already supply. -/

/-- The ordered-pair count inside `Q`, summed over all vertices, is capped by the red codegree
    bound: this is `double_count_gen` with the cap applied on the pair side. -/
theorem offDiag_sum_le (Q : Finset (Fin N)) (r : ℕ)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ r) :
    ∑ x : Fin N, ((K.redNbr x ∩ Q).offDiag).card ≤ r * (Q.card * (Q.card - 1)) := by
  classical
  rw [K.double_count_gen Q]
  calc ∑ p ∈ Q.offDiag, (K.redCodeg p.1 p.2).card
      ≤ ∑ _p ∈ Q.offDiag, r :=
        Finset.sum_le_sum (fun p hp => hr p.1 p.2 (Finset.mem_offDiag.mp hp).2.2)
    _ = Q.offDiag.card * r := by rw [Finset.sum_const_nat (fun _ _ => rfl)]
    _ = r * (Q.card * (Q.card - 1)) := by rw [offDiag_card']; ring

/-- Counting red incidences into `Q` from everywhere equals summing red degrees over `Q`. -/
theorem red_incidence_sum (Q : Finset (Fin N)) :
    ∑ x : Fin N, ((K.redNbr x) ∩ Q).card = ∑ u ∈ Q, (K.redNbr u).card := by
  have h := K.cross_count Finset.univ Q
  simpa using h

#print axioms Colouring.offDiag_sum_le
#print axioms Colouring.red_incidence_sum

/-- **Second moment over an arbitrary vertex set.** `|X|^2 = |X| + |offDiag X|` turns the two
    previous lemmas into a bound on the sum of squares. -/
theorem second_moment (Q : Finset (Fin N)) (r : ℕ)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ r) :
    ∑ x : Fin N, ((K.redNbr x ∩ Q).card) ^ 2
      ≤ (∑ u ∈ Q, (K.redNbr u).card) + r * (Q.card * (Q.card - 1)) := by
  classical
  have hsplit : ∀ x : Fin N, ((K.redNbr x ∩ Q).card) ^ 2
      = ((K.redNbr x ∩ Q).card) + ((K.redNbr x ∩ Q).offDiag).card := by
    intro x; rw [offDiag_card']
    rcases Nat.eq_zero_or_pos (K.redNbr x ∩ Q).card with h | h
    · simp [h]
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
      rw [hk, Nat.succ_sub_one]; simp only [Nat.succ_eq_add_one]; ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  have h1 := K.red_incidence_sum Q
  have h2 := K.offDiag_sum_le Q r hr
  omega

/-- **Chebyshev on the class.** With every vertex of `Q` at red degree `D`, Cauchy-Schwarz over the
    `N` vertices turns the second moment into a quadratic in `|Q|`. -/
theorem class_quadratic (Q : Finset (Fin N)) (D r : ℕ)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ r)
    (hD : ∀ u ∈ Q, (K.redNbr u).card = D) :
    (D * Q.card) ^ 2 ≤ N * (D * Q.card + r * (Q.card * (Q.card - 1))) := by
  classical
  have hsum : ∑ u ∈ Q, (K.redNbr u).card = D * Q.card := by
    rw [Finset.sum_congr rfl hD, Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
  have hcs : (∑ x : Fin N, ((K.redNbr x ∩ Q).card)) ^ 2
      ≤ (Finset.univ : Finset (Fin N)).card * ∑ x : Fin N, ((K.redNbr x ∩ Q).card) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [K.red_incidence_sum Q, hsum, Finset.card_univ, Fintype.card_fin] at hcs
  have hm := K.second_moment Q r hr
  rw [hsum] at hm
  calc (D * Q.card) ^ 2 ≤ N * ∑ x : Fin N, ((K.redNbr x ∩ Q).card) ^ 2 := hcs
    _ ≤ N * (D * Q.card + r * (Q.card * (Q.card - 1))) := Nat.mul_le_mul_left _ hm

#print axioms Colouring.second_moment
#print axioms Colouring.class_quadratic

/-- **Split Cauchy-Schwarz.** Applying Chebyshev separately on `Q` and its complement, rather than
    once over everything, is strictly sharper -- and that sharpness is exactly what the class-size
    bounds need: applied once over all 22 vertices the argument gives n10 ≤ 11 and n8 ≤ 8, one short
    of the 10 and 7 the histogram count requires (measured, 2026-09-14).

    Stated multiplied out so no division enters. -/
theorem split_cs {α : Type*} [Fintype α] [DecidableEq α] (Q : Finset α) (z : α → ℕ) :
    (∑ x ∈ Q, z x) ^ 2 * Qᶜ.card + (∑ x ∈ Qᶜ, z x) ^ 2 * Q.card
      ≤ Q.card * Qᶜ.card * ∑ x, (z x) ^ 2 := by
  classical
  have h1 : (∑ x ∈ Q, z x) ^ 2 ≤ Q.card * ∑ x ∈ Q, (z x) ^ 2 := sq_sum_le_card_mul_sum_sq
  have h2 : (∑ x ∈ Qᶜ, z x) ^ 2 ≤ Qᶜ.card * ∑ x ∈ Qᶜ, (z x) ^ 2 := sq_sum_le_card_mul_sum_sq
  have hsplit : (∑ x ∈ Q, (z x) ^ 2) + (∑ x ∈ Qᶜ, (z x) ^ 2) = ∑ x, (z x) ^ 2 :=
    Finset.sum_add_sum_compl Q _
  calc (∑ x ∈ Q, z x) ^ 2 * Qᶜ.card + (∑ x ∈ Qᶜ, z x) ^ 2 * Q.card
      ≤ (Q.card * ∑ x ∈ Q, (z x) ^ 2) * Qᶜ.card + (Qᶜ.card * ∑ x ∈ Qᶜ, (z x) ^ 2) * Q.card :=
        Nat.add_le_add (Nat.mul_le_mul_right _ h1) (Nat.mul_le_mul_right _ h2)
    _ = Q.card * Qᶜ.card * ((∑ x ∈ Q, (z x) ^ 2) + (∑ x ∈ Qᶜ, (z x) ^ 2)) := by ring
    _ = Q.card * Qᶜ.card * ∑ x, (z x) ^ 2 := by rw [hsplit]

#print axioms Colouring.split_cs

/-! ## Internal class caps, by a two-sided count of the blue S-T edges

Astra round 35 routed these through a deficit budget. The same conclusion follows from bounding the
blue `S`-`T` edge count from both sides, which needs no new definitions:

    degree-10 class:  x <= 4|T| and x >= 4|S| + j   gives j <= 4(|T| - |S|) = 4
    degree-8  class:  x >= 6|S| and x <= 4|T| - j   gives j <= 4|T| - 6|S| = 4
-/

/-- The bipartite blue count, from `cross_count` on the swapped colouring. -/
theorem blue_cross_count (A B : Finset (Fin N)) :
    ∑ u ∈ A, ((K.blueNbr u) ∩ B).card = ∑ w ∈ B, ((K.blueNbr w) ∩ A).card := by
  have h := (K.swap).cross_count A B
  simpa only [swap_redNbr] using h

/-- Every vertex splits `T` into what it sees blue and what it sees red. -/
lemma blue_red_split_card (u : Fin N) (T : Finset (Fin N)) (hu : u ∉ T) :
    ((K.blueNbr u) ∩ T).card + ((K.redNbr u) ∩ T).card = T.card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, mem_blueNbr, mem_redNbr]
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
    · intro hx
      have hxu : x ≠ u := by rintro rfl; exact hu hx
      by_cases hc : K.C u x
      · exact Or.inl ⟨⟨hxu, hc⟩, hx⟩
      · exact Or.inr ⟨⟨hxu, hc⟩, hx⟩
  · rw [Finset.disjoint_left]
    rintro x hx hx'
    simp only [Finset.mem_inter, mem_blueNbr] at hx
    simp only [Finset.mem_inter, mem_redNbr] at hx'
    exact hx'.1.2 hx.1.2

/-- For `u` in `S`, what `u` sees red inside `T` IS the red codegree of `v` and `u`. -/
lemma red_inter_T_eq_codeg (v u : Fin N) :
    (K.redNbr u) ∩ (K.redNbr v) = K.redCodeg v u := by
  rw [K.redCodeg_eq_inter, Finset.inter_comm]

#print axioms Colouring.blue_cross_count
#print axioms Colouring.blue_red_split_card
#print axioms Colouring.red_inter_T_eq_codeg

lemma blueCodeg_eq_inter (i j : Fin N) : K.blueCodeg i j = K.blueNbr i ∩ K.blueNbr j := by
  ext w
  simp only [mem_blueCodeg, Finset.mem_inter, mem_blueNbr]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; exact ⟨h1, h3, h2, h4⟩

/-- Each `u` in `S` sees at least `|T| - r` of `T` in blue: what it sees red in `T` is exactly the
    red codegree of `v` and `u`, which the cap bounds. -/
lemma blue_into_T_lower (r : ℕ) (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ r)
    (v u : Fin N) (hu : u ∈ K.blueNbr v) :
    (K.redNbr v).card - r ≤ ((K.blueNbr u) ∩ K.redNbr v).card := by
  have hne : v ≠ u := by simp only [mem_blueNbr] at hu; exact Ne.symm hu.1
  have huT : u ∉ K.redNbr v := by
    simp only [mem_blueNbr] at hu; simp only [mem_redNbr]; rintro ⟨_, h⟩; exact h hu.2
  have hsplit := K.blue_red_split_card u (K.redNbr v) huT
  have hcod : ((K.redNbr u) ∩ K.redNbr v).card = (K.redCodeg v u).card := by
    rw [K.red_inter_T_eq_codeg v u]
  have hcap := hr v u hne
  omega

/-- Each `w` in `T` sees at most `b` of `S` in blue -- that intersection IS the blue codegree. -/
lemma blue_into_S_upper (b : ℕ) (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ b)
    (v w : Fin N) (hw : w ∈ K.redNbr v) :
    ((K.blueNbr w) ∩ K.blueNbr v).card ≤ b := by
  have hne : v ≠ w := by simp only [mem_redNbr] at hw; exact Ne.symm hw.1
  have := hb v w hne
  rwa [K.blueCodeg_eq_inter, Finset.inter_comm] at this

#print axioms Colouring.blue_into_T_lower
#print axioms Colouring.blue_into_S_upper

/-- A vertex of `T` sends its blue edges into `S` and `T` only: never to the root, since the root
    sees it red. -/
lemma blue_split_S_T (v w : Fin N) (hw : w ∈ K.redNbr v) :
    ((K.blueNbr w) ∩ K.blueNbr v).card + ((K.blueNbr w) ∩ K.redNbr v).card
      = (K.blueNbr w).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hx
      have hxv : x ≠ v := by
        rintro rfl
        simp only [mem_blueNbr] at hx
        simp only [mem_redNbr] at hw
        rw [K.symm w x] at hx; exact hw.2 hx.2
      have := K.univ_split v
      have hmem : x ∈ K.blueNbr v ∪ K.redNbr v := by
        have : x ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ x
        rw [K.univ_split v, Finset.mem_insert] at this
        rcases this with h | h
        · exact absurd h hxv
        · exact h
      rcases Finset.mem_union.mp hmem with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  · rw [Finset.disjoint_left]
    rintro x hx hx'
    exact (Finset.disjoint_left.mp (K.blue_red_disjoint v)) (Finset.mem_inter.mp hx).2
      (Finset.mem_inter.mp hx').2

/-- **The sharpened bound.** If `w` in `T` has the SAME blue degree as `|S|`, it sees strictly less
    of `S` than the blue cap alone allows. The red cap supplies the improvement. -/
lemma blue_into_S_upper_sharp (r : ℕ) (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ r)
    (v w : Fin N) (hw : w ∈ K.redNbr v) (d : ℕ) (hd : (K.blueNbr w).card = d) :
    ((K.blueNbr w) ∩ K.blueNbr v).card + (K.redNbr v).card ≤ r + 1 + d := by
  have hne : v ≠ w := by simp only [mem_redNbr] at hw; exact Ne.symm hw.1
  have hsplit := K.blue_split_S_T v w hw
  have hwT : w ∈ K.redNbr v := hw
  -- T minus w splits blue/red for w
  have hTsplit : ((K.blueNbr w) ∩ K.redNbr v).card + ((K.redNbr w) ∩ K.redNbr v).card
      + 1 = (K.redNbr v).card := by
    have h := K.blue_red_split_card w ((K.redNbr v).erase w) (Finset.notMem_erase w _)
    have hb : (K.blueNbr w) ∩ ((K.redNbr v).erase w) = (K.blueNbr w) ∩ K.redNbr v := by
      ext x; simp only [Finset.mem_inter, Finset.mem_erase, mem_blueNbr]
      constructor
      · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rintro rfl; exact h1.1 rfl, h2⟩
    have hrr : (K.redNbr w) ∩ ((K.redNbr v).erase w) = (K.redNbr w) ∩ K.redNbr v := by
      ext x; simp only [Finset.mem_inter, Finset.mem_erase, mem_redNbr]
      constructor
      · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rintro rfl; exact h1.1 rfl, h2⟩
    rw [hb, hrr, Finset.card_erase_of_mem hwT] at h
    have : 0 < (K.redNbr v).card := Finset.card_pos.mpr ⟨w, hwT⟩
    omega
  have hcod : ((K.redNbr w) ∩ K.redNbr v).card = (K.redCodeg v w).card := by
    rw [K.red_inter_T_eq_codeg v w]
  have hcap := hr v w hne
  omega

#print axioms Colouring.blue_split_S_T
#print axioms Colouring.blue_into_S_upper_sharp

/-- **Internal class cap, general form.** Bounding the blue `S`-`T` edge count from both sides:
    below by `|S|(|T| - r)`, above by the blue cap with the sharpened value on the vertices of `T`
    whose blue degree equals `d`. Stated without subtraction on the sharpened side. -/
theorem internal_class_cap (b r d : ℕ)
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ b)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ r)
    (v : Fin N) :
    (K.blueNbr v).card * ((K.redNbr v).card - r)
      + ((K.redNbr v).filter (fun w => (K.blueNbr w).card = d)).card * (K.redNbr v).card
    ≤ ((K.redNbr v).filter (fun w => (K.blueNbr w).card = d)).card * (r + 1 + d)
      + ((K.redNbr v).filter (fun w => ¬ (K.blueNbr w).card = d)).card * b := by
  classical
  set T := K.redNbr v with hT
  set Q := T.filter (fun w => (K.blueNbr w).card = d) with hQ
  set R := T.filter (fun w => ¬ (K.blueNbr w).card = d) with hR
  -- the two sides of the blue S-T count
  have hcross := K.blue_cross_count (K.blueNbr v) T
  -- lower: every u in S sees at least |T| - r of T in blue
  have hlow : (K.blueNbr v).card * (T.card - r)
      ≤ ∑ u ∈ K.blueNbr v, ((K.blueNbr u) ∩ T).card := by
    calc (K.blueNbr v).card * (T.card - r)
        = ∑ _u ∈ K.blueNbr v, (T.card - r) := by
          rw [Finset.sum_const_nat (fun _ _ => rfl)]
      _ ≤ _ := Finset.sum_le_sum (fun u hu => K.blue_into_T_lower r hr v u hu)
  -- upper: split T into Q and R
  have hQR : ∑ w ∈ T, ((K.blueNbr w) ∩ K.blueNbr v).card
      = (∑ w ∈ Q, ((K.blueNbr w) ∩ K.blueNbr v).card)
        + ∑ w ∈ R, ((K.blueNbr w) ∩ K.blueNbr v).card := by
    rw [hQ, hR]; exact (Finset.sum_filter_add_sum_filter_not T _ _).symm
  have hupQ : (∑ w ∈ Q, ((K.blueNbr w) ∩ K.blueNbr v).card) + Q.card * T.card
      ≤ Q.card * (r + 1 + d) := by
    have : ∀ w ∈ Q, ((K.blueNbr w) ∩ K.blueNbr v).card + T.card ≤ r + 1 + d := by
      intro w hw
      rw [hQ, Finset.mem_filter] at hw
      exact K.blue_into_S_upper_sharp r hr v w hw.1 d hw.2
    calc (∑ w ∈ Q, ((K.blueNbr w) ∩ K.blueNbr v).card) + Q.card * T.card
        = ∑ w ∈ Q, (((K.blueNbr w) ∩ K.blueNbr v).card + T.card) := by
          rw [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)]
      _ ≤ ∑ _w ∈ Q, (r + 1 + d) := Finset.sum_le_sum this
      _ = Q.card * (r + 1 + d) := by rw [Finset.sum_const_nat (fun _ _ => rfl)]
  have hupR : (∑ w ∈ R, ((K.blueNbr w) ∩ K.blueNbr v).card) ≤ R.card * b := by
    calc (∑ w ∈ R, ((K.blueNbr w) ∩ K.blueNbr v).card)
        ≤ ∑ _w ∈ R, b := Finset.sum_le_sum (fun w hw => by
            rw [hR, Finset.mem_filter] at hw
            exact K.blue_into_S_upper b hb v w hw.1)
      _ = R.card * b := by rw [Finset.sum_const_nat (fun _ _ => rfl)]
  omega

#print axioms Colouring.internal_class_cap

/-- A vertex of blue degree 8 has at most four RED neighbours of blue degree 8.
    Tight: the inequality is an equality at four. -/
theorem deg8_red_nbrs_le_four
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ 4)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ 7)
    (hN : N = 22) (v : Fin N) (hv : (K.blueNbr v).card = 8) :
    ((K.redNbr v).filter (fun w => (K.blueNbr w).card = 8)).card ≤ 4 := by
  classical
  have hpart := K.card_partition v
  have hT : (K.redNbr v).card = 13 := by omega
  have key := K.internal_class_cap 4 7 8 hb hr v
  rw [hv, hT] at key
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := K.redNbr v) (p := fun w => (K.blueNbr w).card = 8)
  rw [hT] at hsplit
  omega

/-- A vertex of blue degree 10 has at most four BLUE neighbours of blue degree 10. Obtained by
    applying the same cap to the swapped colouring, where blue degree 10 reads as red degree 11. -/
theorem deg10_blue_nbrs_le_four
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ 4)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ 7)
    (hN : N = 22) (v : Fin N) (hv : (K.blueNbr v).card = 10) :
    ((K.blueNbr v).filter (fun w => (K.redNbr w).card = 11)).card ≤ 4 := by
  classical
  have hb' : ∀ i j : Fin N, i ≠ j → ((K.swap).blueCodeg i j).card ≤ 7 := by
    intro i j hij; rw [swap_blueCodeg]; exact hr i j hij
  have hr' : ∀ i j : Fin N, i ≠ j → ((K.swap).redCodeg i j).card ≤ 4 := by
    intro i j hij; rw [swap_redCodeg]; exact hb i j hij
  have hpart := K.card_partition v
  have hsb : ((K.swap).blueNbr v).card = 11 := by rw [swap_blueNbr]; omega
  have hsr : ((K.swap).redNbr v).card = 10 := by rw [swap_redNbr]; omega
  have key := (K.swap).internal_class_cap 7 4 11 hb' hr' v
  rw [hsb, hsr] at key
  simp only [swap_blueNbr, swap_redNbr] at key
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := K.blueNbr v) (p := fun w => (K.redNbr w).card = 11)
  rw [hv] at hsplit
  omega

#print axioms Colouring.deg8_red_nbrs_le_four
#print axioms Colouring.deg10_blue_nbrs_le_four

/-! ## `n8 ≤ 7`, assembled -/

/-- Intersecting with a `univ.filter` is filtering. -/
lemma inter_univ_filter (S : Finset (Fin N)) (d : ℕ) :
    S ∩ (Finset.univ.filter (fun y => (K.blueNbr y).card = d)) = S.filter (fun y => (K.blueNbr y).card = d) := by
  ext y; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Inside the degree-8 class, what a member sees red is exactly its red neighbours of degree 8. -/
lemma red_inter_class (d : ℕ) (x : Fin N) :
    (K.redNbr x) ∩ (Finset.univ.filter (fun y => (K.blueNbr y).card = d))
      = (K.redNbr x).filter (fun y => (K.blueNbr y).card = d) := by
  ext y; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The three quantities the moment argument needs, for the degree-8 class at N = 22. -/
lemma deg8_class_data
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ 4)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ 7)
    (hN : N = 22) :
    let Q := (Finset.univ.filter (fun y => (K.blueNbr y).card = 8))
    (∑ x ∈ Q, ((K.redNbr x) ∩ Q).card) ≤ 4 * Q.card
  ∧ (∑ x : Fin N, ((K.redNbr x) ∩ Q).card) = 13 * Q.card
  ∧ (∑ x : Fin N, (((K.redNbr x) ∩ Q).card) ^ 2) ≤ 13 * Q.card + 7 * (Q.card * (Q.card - 1)) := by
  classical
  intro Q
  refine ⟨?_, ?_, ?_⟩
  · calc ∑ x ∈ Q, ((K.redNbr x) ∩ Q).card
        ≤ ∑ _x ∈ Q, 4 := Finset.sum_le_sum (fun x hx => by
          have hx8 : (K.blueNbr x).card = 8 := (Finset.mem_filter.mp hx).2
          rw [K.red_inter_class 8 x]
          exact K.deg8_red_nbrs_le_four hb hr hN x hx8)
      _ = Q.card * 4 := by rw [Finset.sum_const_nat (fun _ _ => rfl)]
      _ = 4 * Q.card := Nat.mul_comm _ _
  · rw [K.red_incidence_sum Q]
    have : ∀ u ∈ Q, (K.redNbr u).card = 13 := by
      intro u hu
      have h8 : (K.blueNbr u).card = 8 := (Finset.mem_filter.mp hu).2
      have := K.card_partition u; omega
    rw [Finset.sum_congr rfl this, Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
  · have hm := K.second_moment Q 7 hr
    have hsum : ∑ u ∈ Q, (K.redNbr u).card = 13 * Q.card := by
      have : ∀ u ∈ Q, (K.redNbr u).card = 13 := by
        intro u hu
        have h8 : (K.blueNbr u).card = 8 := (Finset.mem_filter.mp hu).2
        have := K.card_partition u; omega
      rw [Finset.sum_congr rfl this, Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
    rw [hsum] at hm; exact hm

#print axioms Colouring.deg8_class_data

set_option maxHeartbeats 1000000 in
/-- The arithmetic core of `n8 ≤ 7`, isolated so its cost is contained: for every class size from
    8 to 22 the split Cauchy-Schwarz inequality is contradicted. Verified numerically first -- at
    h = 8 the margin is 55808 against 55552, and it widens. -/
lemma n8_arith (h q p M : ℕ) (hh : 8 ≤ h) (hh22 : h ≤ 22)
    (hq : q ≤ 4 * h) (hqp : q + p = 13 * h)
    (hM : M ≤ 13 * h + 7 * (h * (h - 1)))
    (hcs : q ^ 2 * (22 - h) + p ^ 2 * h ≤ h * (22 - h) * M) : False := by
  interval_cases h <;> simp_all <;> nlinarith [hq, hqp, hM, hcs]

/-- **`n8 ≤ 7`.** At most seven vertices of a good colouring of K22 have blue degree 8 -- one of the
    two class-size bounds the 44 histograms rest on, and which the degree lemma does not give. -/
theorem n8_le_seven
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ 4)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ 7)
    (hN : N = 22) :
    (Finset.univ.filter (fun y => (K.blueNbr y).card = 8)).card ≤ 7 := by
  classical
  by_contra hgt
  push_neg at hgt
  obtain ⟨hq, hTot, hM⟩ := K.deg8_class_data hb hr hN
  set Q := (Finset.univ.filter (fun y => (K.blueNbr y).card = 8)) with hQdef
  set z : Fin N → ℕ := fun x => ((K.redNbr x) ∩ Q).card with hz
  have hcs := split_cs Q z
  have hc : Q.card + Qᶜ.card = 22 := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]; omega
  have hqp : (∑ x ∈ Q, z x) + (∑ x ∈ Qᶜ, z x) = 13 * Q.card := by
    rw [Finset.sum_add_sum_compl]; exact hTot
  have hc2 : Qᶜ.card = 22 - Q.card := by omega
  rw [hc2] at hcs
  exact n8_arith Q.card (∑ x ∈ Q, z x) (∑ x ∈ Qᶜ, z x) (∑ x, (z x) ^ 2)
    (by omega) (by omega) hq hqp hM hcs

#print axioms Colouring.n8_le_seven

/-! ## `n10 ≤ 10`, by the same route on the swapped colouring -/

/-- At N = 22 a vertex has blue degree 10 exactly when it has red degree 11. -/
lemma deg10_iff_red11 (hN : N = 22) (y : Fin N) :
    (K.blueNbr y).card = 10 ↔ (K.redNbr y).card = 11 := by
  have := K.card_partition y; omega

lemma deg10_class_data
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ 4)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ 7)
    (hN : N = 22) :
    let Q := (Finset.univ.filter (fun y => (K.blueNbr y).card = 10))
    (∑ x ∈ Q, (((K.swap).redNbr x) ∩ Q).card) ≤ 4 * Q.card
  ∧ (∑ x : Fin N, (((K.swap).redNbr x) ∩ Q).card) = 10 * Q.card
  ∧ (∑ x : Fin N, ((((K.swap).redNbr x) ∩ Q).card) ^ 2)
      ≤ 10 * Q.card + 4 * (Q.card * (Q.card - 1)) := by
  classical
  intro Q
  have hr' : ∀ i j : Fin N, i ≠ j → ((K.swap).redCodeg i j).card ≤ 4 := by
    intro i j hij; rw [swap_redCodeg]; exact hb i j hij
  have hdeg : ∀ u ∈ Q, ((K.swap).redNbr u).card = 10 := by
    intro u hu; rw [swap_redNbr]; exact (Finset.mem_filter.mp hu).2
  refine ⟨?_, ?_, ?_⟩
  · calc ∑ x ∈ Q, (((K.swap).redNbr x) ∩ Q).card
        ≤ ∑ _x ∈ Q, 4 := Finset.sum_le_sum (fun x hx => by
          have h10 : (K.blueNbr x).card = 10 := (Finset.mem_filter.mp hx).2
          rw [swap_redNbr, K.inter_univ_filter (K.blueNbr x) 10]
          have hcap := K.deg10_blue_nbrs_le_four hb hr hN x h10
          have hfe : (K.blueNbr x).filter (fun y => (K.blueNbr y).card = 10)
              = (K.blueNbr x).filter (fun y => (K.redNbr y).card = 11) := by
            apply Finset.filter_congr; intro y _; simp [K.deg10_iff_red11 hN y]
          rw [hfe]; exact hcap)
      _ = Q.card * 4 := by rw [Finset.sum_const_nat (fun _ _ => rfl)]
      _ = 4 * Q.card := Nat.mul_comm _ _
  · rw [(K.swap).red_incidence_sum Q, Finset.sum_congr rfl hdeg,
        Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
  · have hm := (K.swap).second_moment Q 4 hr'
    have hs : ∑ u ∈ Q, ((K.swap).redNbr u).card = 10 * Q.card := by
      rw [Finset.sum_congr rfl hdeg, Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
    rw [hs] at hm
    exact hm

#print axioms Colouring.deg10_class_data

set_option maxHeartbeats 1000000 in
/-- Arithmetic core of `n10 ≤ 10`: contradicted for every class size 11 to 22, at h = 11 by
    69212 against 66550. -/
lemma n10_arith (h q p M : ℕ) (hh : 11 ≤ h) (hh22 : h ≤ 22)
    (hq : q ≤ 4 * h) (hqp : q + p = 10 * h)
    (hM : M ≤ 10 * h + 4 * (h * (h - 1)))
    (hcs : q ^ 2 * (22 - h) + p ^ 2 * h ≤ h * (22 - h) * M) : False := by
  interval_cases h <;> simp_all <;> nlinarith [hq, hqp, hM, hcs]

/-- **`n10 ≤ 10`.** The second class-size bound the 44 histograms rest on. -/
theorem n10_le_ten
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ 4)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ 7)
    (hN : N = 22) :
    (Finset.univ.filter (fun y => (K.blueNbr y).card = 10)).card ≤ 10 := by
  classical
  by_contra hgt
  push_neg at hgt
  obtain ⟨hq, hTot, hM⟩ := K.deg10_class_data hb hr hN
  set Q := (Finset.univ.filter (fun y => (K.blueNbr y).card = 10)) with hQdef
  set z : Fin N → ℕ := fun x => (((K.swap).redNbr x) ∩ Q).card with hz
  have hcs := split_cs Q z
  have hc : Q.card + Qᶜ.card = 22 := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]; omega
  have hqp : (∑ x ∈ Q, z x) + (∑ x ∈ Qᶜ, z x) = 10 * Q.card := by
    rw [Finset.sum_add_sum_compl]; exact hTot
  have hc2 : Qᶜ.card = 22 - Q.card := by omega
  rw [hc2] at hcs
  exact n10_arith Q.card (∑ x ∈ Q, z x) (∑ x ∈ Qᶜ, z x) (∑ x, (z x) ^ 2)
    (by omega) (by omega) hq hqp hM hcs

/-- **BOTH CLASS-SIZE BOUNDS.** Together with `degree_in_eight_nine_ten` this is everything the
    44-histogram count assumes about degrees. -/
theorem class_bounds
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ 4)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ 7)
    (hN : N = 22) :
    (Finset.univ.filter (fun y => (K.blueNbr y).card = 8)).card ≤ 7
  ∧ (Finset.univ.filter (fun y => (K.blueNbr y).card = 10)).card ≤ 10 :=
  ⟨K.n8_le_seven hb hr hN, K.n10_le_ten hb hr hN⟩

#print axioms Colouring.n10_le_ten
#print axioms Colouring.class_bounds

/-! ## Histogram membership

Round 36: closing the degree dependencies is not the same as formalising "exactly 44 histograms".
That step also needs handshaking. This section supplies it. -/

/-- The red degree sum is even: the handshake lemma at `S = univ`. -/
theorem red_degree_sum_even : Even (∑ v : Fin N, (K.redNbr v).card) := by
  classical
  have h := K.even_internal_red_degree_sum Finset.univ
  simpa using h

/-- Hence so is the blue degree sum. -/
theorem blue_degree_sum_even (hN : N = 22) : Even (∑ v : Fin N, (K.blueNbr v).card) := by
  classical
  have hred := K.red_degree_sum_even
  have hpt : ∀ v : Fin N, (K.blueNbr v).card + (K.redNbr v).card = 21 := by
    intro v; have := K.card_partition v; omega
  have hsum : (∑ v : Fin N, (K.blueNbr v).card) + (∑ v : Fin N, (K.redNbr v).card)
      = 462 := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun v _ => hpt v),
        Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ, Fintype.card_fin, hN]
  obtain ⟨k, hk⟩ := hred
  exact ⟨231 - k, by omega⟩

/-- **Histogram membership.** Every good colouring of K22 has a degree census satisfying exactly the
    constraints the 44-histogram enumeration assumes: the three classes partition the vertices, the
    two class caps hold, and the degree-9 class is even. -/
theorem histogram_membership
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ 4)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ 7)
    (hN : N = 22) :
    (Finset.univ.filter (fun y => (K.blueNbr y).card = 8)).card
      + (Finset.univ.filter (fun y => (K.blueNbr y).card = 9)).card
      + (Finset.univ.filter (fun y => (K.blueNbr y).card = 10)).card = 22
  ∧ (Finset.univ.filter (fun y => (K.blueNbr y).card = 8)).card ≤ 7
  ∧ (Finset.univ.filter (fun y => (K.blueNbr y).card = 10)).card ≤ 10
  ∧ Even (Finset.univ.filter (fun y => (K.blueNbr y).card = 9)).card := by
  classical
  set A := (Finset.univ.filter (fun y => (K.blueNbr y).card = 8)) with hA
  set B := (Finset.univ.filter (fun y => (K.blueNbr y).card = 9)) with hB
  set C := (Finset.univ.filter (fun y => (K.blueNbr y).card = 10)) with hC
  -- the three classes exhaust the vertices
  have hcover : ∀ v : Fin N, v ∈ A ∨ v ∈ B ∨ v ∈ C := by
    intro v
    rcases K.degree_in_eight_nine_ten hb hr hN v with h | h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩))
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩))
  have hpart : A.card + B.card + C.card = 22 := by
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_left]; intro x hx hx'
      rw [hA, Finset.mem_filter] at hx; rw [hB, Finset.mem_filter] at hx'; omega
    have hABC : Disjoint (A ∪ B) C := by
      rw [Finset.disjoint_left]; intro x hx hx'
      rw [hC, Finset.mem_filter] at hx'
      rcases Finset.mem_union.mp hx with h | h
      · rw [hA, Finset.mem_filter] at h; omega
      · rw [hB, Finset.mem_filter] at h; omega
    have huniv : A ∪ B ∪ C = Finset.univ := by
      ext x; simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      rcases hcover x with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    -- N cannot be rewritten here: it occurs in the types. Let omega combine the facts instead.
    have h2 := Finset.card_union_of_disjoint hABC
    have h1 := Finset.card_union_of_disjoint hAB
    have h3 : (A ∪ B ∪ C).card = Fintype.card (Fin N) := by rw [huniv, Finset.card_univ]
    have h4 : Fintype.card (Fin N) = 22 := by rw [Fintype.card_fin]; omega
    omega
  -- the degree sum, class by class
  have hdegsum : 8 * A.card + 9 * B.card + 10 * C.card = ∑ v : Fin N, (K.blueNbr v).card := by
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_left]; intro x hx hx'
      rw [hA, Finset.mem_filter] at hx; rw [hB, Finset.mem_filter] at hx'; omega
    have hABC : Disjoint (A ∪ B) C := by
      rw [Finset.disjoint_left]; intro x hx hx'
      rw [hC, Finset.mem_filter] at hx'
      rcases Finset.mem_union.mp hx with h | h
      · rw [hA, Finset.mem_filter] at h; omega
      · rw [hB, Finset.mem_filter] at h; omega
    have huniv : A ∪ B ∪ C = Finset.univ := by
      ext x; simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      rcases hcover x with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have hsA : ∑ v ∈ A, (K.blueNbr v).card = 8 * A.card := by
      rw [Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2),
          Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
    have hsB : ∑ v ∈ B, (K.blueNbr v).card = 9 * B.card := by
      rw [Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2),
          Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
    have hsC : ∑ v ∈ C, (K.blueNbr v).card = 10 * C.card := by
      rw [Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2),
          Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
    calc 8 * A.card + 9 * B.card + 10 * C.card
        = (∑ v ∈ A, (K.blueNbr v).card) + (∑ v ∈ B, (K.blueNbr v).card)
          + ∑ v ∈ C, (K.blueNbr v).card := by rw [hsA, hsB, hsC]
      _ = ∑ v ∈ (A ∪ B ∪ C), (K.blueNbr v).card := by
          rw [Finset.sum_union hABC, Finset.sum_union hAB]
      _ = ∑ v : Fin N, (K.blueNbr v).card := by rw [huniv]
  refine ⟨hpart, K.n8_le_seven hb hr hN, K.n10_le_ten hb hr hN, ?_⟩
  have heven := K.blue_degree_sum_even hN
  rw [← hdegsum] at heven
  rcases heven with ⟨k, hk⟩
  exact ⟨(B.card) / 2, by omega⟩

#print axioms Colouring.red_degree_sum_even
#print axioms Colouring.blue_degree_sum_even
#print axioms Colouring.histogram_membership

/-- The admissible histograms, as a finite set: `n8` in 0..7, `n10` in 0..10, and `n8 + n10` even
    (equivalently `n9` even, since the three sum to 22). -/
def admissibleHistograms : Finset (ℕ × ℕ) :=
  (Finset.range 8 ×ˢ Finset.range 11).filter (fun p => (p.1 + p.2) % 2 = 0)

/-- **There are exactly 44 of them**, by decision. This is the number the census enumerates. -/
theorem admissibleHistograms_card : admissibleHistograms.card = 44 := by decide

/-- **The bridge.** Every good colouring of K22 has its degree census among those 44. -/
theorem histogram_in_admissible
    (hb : ∀ i j, i ≠ j → (K.blueCodeg i j).card ≤ 4)
    (hr : ∀ i j, i ≠ j → (K.redCodeg i j).card ≤ 7)
    (hN : N = 22) :
    ((Finset.univ.filter (fun y => (K.blueNbr y).card = 8)).card,
     (Finset.univ.filter (fun y => (K.blueNbr y).card = 10)).card) ∈ admissibleHistograms := by
  obtain ⟨hsum, h8, h10, h9even⟩ := K.histogram_membership hb hr hN
  rw [admissibleHistograms, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_range]
  obtain ⟨k, hk⟩ := h9even
  exact ⟨⟨by omega, by omega⟩, by omega⟩

#print axioms Colouring.admissibleHistograms_card
#print axioms Colouring.histogram_in_admissible
