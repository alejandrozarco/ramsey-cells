/-
# M4, part 5c: what an UNSAT cover CNF certifies, and `CensusCover` from the M0 certificates

* `cover_sound`: if `coverCNF k cap lo hi perms blocked` is `CNF.Unsat`, then every graph `x` on
  `Fin k` meeting the caps (filter (i)), the edge window (filter (ii)), and lex-`≤` its image under
  every recorded permutation, has the word of some blocked word.
* `family_cover`: for a family certificate (`FamCert`) whose recorded permutations are
  degree-preserving permutations and whose filter-(iii) blockers fail `failIIIPy` on their `U`,
  `CNF.Unsat` of `famCNF` puts every `FiltersOK` stage-1 leader on a listed word.
* `censusCover_of_certs`: `CensusCover C` from one certificate per census family, the `CNF.Unsat`
  verdicts and the correspondence listed word ↔ cube of `C` (`c.H = wordEdges k w`).
-/
import RootedM4.Main
import RootedM4.CoverSound
import RootedM4.CoverBase
import RootedM4.FilterCheck

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace SB.Rooted.M4.Cover
open SB SB.BipBridge SB.Rooted SB.Rooted.M4 LRATCatcher.Rooted Finset

section Assign
variable {k : ℕ}

/-- The graph variables of `x` (variable `n + 1` is position `n`). -/
def σ0 (x : EColouring k 2) : ℕ → Bool := fun v => if 1 ≤ v ∧ v ≤ Ek k then wd x (v - 1) else false

theorem σ0_var (x : EColouring k 2) {n : ℕ} (hn : n < Ek k) : σ0 x (n + 1) = wd x n := by
  unfold σ0; rw [if_pos ⟨by omega, by omega⟩]; rfl

theorem pos_edgeOf {i j : ℕ} (h : i < j ∧ j < k) : pos (edgeOf (k := k) i j h) = pIdx k i j := rfl

theorem gOf_lt (x : EColouring k 2) {i j : Fin k} (hij : i < j) :
    gOf x i j = decide (x (edgeOf i.val j.val ⟨hij, j.isLt⟩) = 1) := by
  unfold gOf; rw [dif_neg (ne_of_lt hij), mkEdge_pos (ne_of_lt hij) hij]; rfl

theorem gOf_symm (x : EColouring k 2) (i j : Fin k) : gOf x i j = gOf x j i := by
  unfold gOf
  by_cases h : i = j
  · subst h; rfl
  · rw [dif_neg h, dif_neg (Ne.symm h), mkEdge_comm]

theorem σ0_xvN (hp : PairFacts k) (x : EColouring k 2) {i j : ℕ} (hi : i < k) (hj : j < k)
    (hij : i ≠ j) : σ0 x (xvN k i j) = gOf x ⟨i, hi⟩ ⟨j, hj⟩ := by
  unfold xvN
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · rw [if_pos h, σ0_var x (hp.surj i j h hj).1, gOf_lt x (show (⟨i, hi⟩ : Fin k) < ⟨j, hj⟩ from h),
      ← pos_edgeOf ⟨h, hj⟩, wd_pos hp]
  · rw [if_neg (by omega), σ0_var x (hp.surj j i h hi).1, gOf_symm,
      gOf_lt x (show (⟨j, hj⟩ : Fin k) < ⟨i, hi⟩ from h), ← pos_edgeOf ⟨h, hi⟩, wd_pos hp]

end Assign

/-! ## Counting over `Fin k` -/

/-! ## Filter (i): the cap clauses -/

theorem caps_sat {k : ℕ} (hp : PairFacts k) (x : EColouring k 2) (cap : ℕ → ℤ)
    (hcap : ∀ i : Fin k, (popRow (gOf x) i : ℤ) ≤ cap i.val) :
    BipBridge.ListSat (σ0 x) (capClauses k cap) := by
  intro c hc
  unfold capClauses at hc
  simp only [List.mem_flatMap, List.mem_range] at hc
  obtain ⟨i, hi, hc⟩ := hc
  have hci : (popRow (gOf x) ⟨i, hi⟩ : ℤ) ≤ cap i := hcap ⟨i, hi⟩
  split_ifs at hc with hneg
  · exfalso; have : (0 : ℤ) ≤ popRow (gOf x) ⟨i, hi⟩ := by positivity
    omega
  obtain ⟨sub, hsub, rfl⟩ := List.mem_map.mp hc
  set row := ((List.range k).filter (fun j => j != i)).map (fun j => xvN k i j) with hrow
  obtain ⟨hsl, hlen⟩ := combos_sub _ row sub hsub
  -- some variable of `sub` is false
  by_contra hns
  have hall : ∀ v ∈ sub, σ0 x v = true := by
    intro v hv
    by_contra hf
    apply hns
    have hv0 : 0 < v := by
      have := hsl.subset hv
      rw [hrow, List.mem_map] at this
      obtain ⟨j, -, rfl⟩ := this; unfold xvN; omega
    refine ⟨-(v : ℤ), List.mem_map.mpr ⟨v, hv, rfl⟩, by omega, ?_⟩
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    simp only [Bool.not_eq_true] at hf; rw [hf]; simp
  have h1 : sub.Sublist (row.filter (σ0 x)) := by
    have := hsl.filter (σ0 x)
    rwa [List.filter_eq_self.mpr (fun v hv => hall v hv)] at this
  have h2 := h1.length_le
  have h3 : (row.filter (σ0 x)).length = popRow (gOf x) ⟨i, hi⟩ := by
    rw [hrow, List.filter_map, List.length_map, List.filter_filter]
    unfold popRow
    apply count_finK
    intro j
    by_cases hji : j.val = i
    · have : j = ⟨i, hi⟩ := Fin.ext hji
      subst this; simp [gOf]
    · simp only [Function.comp, bne_iff_ne, ne_eq, hji, not_false_eq_true, decide_true,
        Bool.true_and]
      rw [σ0_xvN hp x hi j.isLt (Ne.symm hji)]
      simp only [Fin.eta, Bool.decide_eq_true]
      simp [hji]
  rw [hlen, h3] at h2
  omega

/-! ## Filter (ii): the window -/

theorem edges_count {k : ℕ} (hp : PairFacts k) (x : EColouring k 2) :
    edgesPy (gOf x) = ((List.range (Ek k)).filter (wd x)).length := by
  classical
  rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter _), List.toFinset_filter,
    List.toFinset_range]
  unfold edgesPy
  symm
  refine Finset.card_bij' (fun n hn => (⟨(pairAt k n).1, by
        have := hp.valid n (Finset.mem_range.mp (Finset.mem_filter.mp hn).1); omega⟩,
      ⟨(pairAt k n).2, (hp.valid n (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)).2⟩))
    (fun q hq => pIdx k q.1.val q.2.val) ?_ ?_ ?_ ?_
  · intro n hn
    have hnE := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    have hw : wd x n = true := by simpa using (Finset.mem_filter.mp hn).2
    have hv := hp.valid n hnE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hv.1, ?_⟩
    rw [gOf_lt x (show (⟨(pairAt k n).1, by omega⟩ : Fin k) < ⟨(pairAt k n).2, hv.2⟩ from hv.1)]
    rw [← hw]; unfold wd; rw [dif_pos hv]
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    have hs := hp.surj q.1.val q.2.val hq.1 q.2.isLt
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨hs.1, ?_⟩
    rw [← pos_edgeOf ⟨hq.1, q.2.isLt⟩, wd_pos hp, ← gOf_lt x hq.1]; simpa using hq.2
  · intro n hn
    have hnE := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    exact hp.idx n hnE
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    have hs := hp.surj q.1.val q.2.val hq.1 q.2.isLt
    ext <;> simp [hs.2]

theorem count_pos_lits (σ : ℕ → Bool) (E : ℕ) :
    (((List.range E).map (fun n => ((n + 1 : ℕ) : ℤ))).filter (litT σ)).length =
      ((List.range E).filter (fun n => σ (n + 1))).length := by
  rw [List.filter_map, List.length_map]
  congr 1
  all_goals (apply List.filter_congr; intro n _; exact litT_nat σ (Nat.succ_pos n))

theorem count_neg_lits (σ : ℕ → Bool) (E : ℕ) :
    ((((List.range E).map (fun n => ((n + 1 : ℕ) : ℤ))).map (fun v => -v)).filter (litT σ)).length =
      ((List.range E).filter (fun n => !σ (n + 1))).length := by
  rw [List.map_map, List.filter_map, List.length_map]
  congr 1
  all_goals (apply List.filter_congr; intro n _; exact litT_negNat σ (Nat.succ_pos n))

/-! ## The blocking clauses -/

theorem blocker_sat {σ : ℕ → Bool} {wb : List Bool} (h : ∃ n < wb.length, σ (n + 1) ≠ wb.getD n false) :
    BipBridge.ClauseSat σ (blocker wb) := by
  obtain ⟨n, hn, hne⟩ := h
  rw [clauseSat_iff (by
    intro l hl; unfold blocker at hl
    obtain ⟨m, -, rfl⟩ := List.mem_map.mp hl
    split_ifs <;> omega)]
  refine ⟨if wb.getD n false then -((n + 1 : ℕ) : ℤ) else ((n + 1 : ℕ) : ℤ),
    List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩, ?_⟩
  cases hb : wb.getD n false
  · simp only [Bool.false_eq_true, if_false]; rw [litT_nat σ (by omega)]
    rw [hb] at hne; simpa using hne
  · simp only [if_true]; rw [litT_negNat σ (by omega)]
    rw [hb] at hne; simpa using hne

theorem blocker_vars (wb : List Bool) : ∀ l ∈ blocker wb, l ≠ 0 ∧ l.natAbs ≤ wb.length := by
  intro l hl; unfold blocker at hl
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hl
  rw [List.mem_range] at hm
  split_ifs <;> simp <;> omega

/-! ## All recorded permutations -/

theorem llAll_sound {k : ℕ} (hp : PairFacts k) (x : EColouring k 2) :
    ∀ (perms : List (List ℕ)) (nv : ℕ) (σ : ℕ → Bool),
      (∀ p ∈ perms, ∃ h : PermOK k p, lexView x ≤ lexView (actV (permOf h) x)) →
      Ek k ≤ nv → (∀ n < Ek k, σ (n + 1) = wd x n) →
      ∃ σ' : ℕ → Bool, (∀ v, v ≤ nv → σ' v = σ v) ∧ BipBridge.ListSat σ' (llAll k perms nv).1 ∧
        VarsLe (llAll k perms nv).1 (llAll k perms nv).2 ∧ nv ≤ (llAll k perms nv).2
  | [], nv, σ, _, _, _ =>
    ⟨σ, fun _ _ => rfl, fun c hc => by simp [llAll] at hc, fun c hc => by simp [llAll] at hc,
      by simp [llAll]⟩
  | p :: ps, nv, σ, hperm, hE, hσ => by
    obtain ⟨hpk, hle⟩ := hperm p (by simp)
    have hlex := lexLeW_of_lexView hp hpk x hle
    have hf : ∀ n < Ek k, fP k p n < Ek k := fun n hn => fP_lt hp hpk hn
    obtain ⟨σ1, hag1, hs1, hv1, hm1⟩ := llChain_sound (Ek k) (wd x) (fP k p) hf hlex _ 0 none nv σ
      rfl hE hσ (fun m hm => absurd hm (Nat.not_lt_zero _))
    have hmv := movedVars_eq hp hpk
    obtain ⟨σ2, hag2, hs2, hv2, hm2⟩ := llAll_sound hp x ps (llChain ((List.filter (fun n => fP k p n != n)
        (List.range' 0 (Ek k - 0))).map (toV (fP k p))) none nv).2 σ1
      (fun q hq => hperm q (by simp [hq])) (by omega)
      (fun n hn => by rw [hag1 _ (by omega)]; exact hσ n hn)
    refine ⟨σ2, fun v hv => by rw [hag2 v (by omega), hag1 v hv], ?_, ?_, ?_⟩
    · simp only [llAll, llClauses, hmv]
      exact listSat_append (listSat_agree hs1 hv1 hag2) hs2
    · simp only [llAll, llClauses, hmv]
      exact VarsLe.append (hv1.mono hm2) hv2
    · simp only [llAll, llClauses, hmv]; omega

/-! ## What an UNSAT cover CNF certifies -/

theorem cover_sound {k : ℕ} (hp : PairFacts k) (cap : ℕ → ℤ) (lo hi : ℤ)
    (perms : List (List ℕ)) (blocked : List (List Bool))
    (hU : (toCNFV (coverCNF k cap lo hi perms blocked).1).Unsat)
    (hlen : ∀ wb ∈ blocked, wb.length = Ek k)
    (x : EColouring k 2)
    (hcap : ∀ i : Fin k, (popRow (gOf x) i : ℤ) ≤ cap i.val)
    (hlo : lo ≤ edgesPy (gOf x)) (hhi : (edgesPy (gOf x) : ℤ) ≤ hi)
    (hperm : ∀ p ∈ perms, ∃ h : PermOK k p, lexView x ≤ lexView (actV (permOf h) x)) :
    ∃ wb ∈ blocked, ∀ n < Ek k, wd x n = wb.getD n false := by
  by_contra hno
  push_neg at hno
  set E := Ek k with hEdef
  have hEeq : k * (k - 1) / 2 = E := rfl
  set xs : List ℤ := (List.range E).map (fun n => ((n + 1 : ℕ) : ℤ)) with hxs
  have hxsv : ∀ l ∈ xs, l ≠ 0 ∧ l.natAbs ≤ E := by
    intro l hl; obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hl; rw [List.mem_range] at hn
    exact ⟨by omega, by simp; omega⟩
  have hσ0 : ∀ n < E, σ0 x (n + 1) = wd x n := fun n hn => σ0_var x hn
  have hcnt : ((List.range E).filter (fun n => σ0 x (n + 1))).length = edgesPy (gOf x) := by
    rw [edges_count hp]; congr 1; apply List.filter_congr; intro n hn
    rw [List.mem_range] at hn; rw [hσ0 n hn]
  -- window, at most `hi`
  obtain ⟨σ1, hag1, hs1, hv1, hm1⟩ := atMost_sound xs hi E (σ0 x) hxsv (by
    rw [hxs, count_pos_lits, hcnt]; exact hhi)
  -- window, at least `lo`
  have hnegv : ∀ l ∈ xs.map (fun v => -v), l ≠ 0 ∧ l.natAbs ≤ (atMost xs hi E).2 := by
    intro l hl; obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
    have := hxsv l' hl'; exact ⟨by omega, by rw [Int.natAbs_neg]; omega⟩
  obtain ⟨σ2, hag2, hs2, hv2, hm2⟩ := atMost_sound (xs.map (fun v => -v)) ((E : ℤ) - lo)
    (atMost xs hi E).2 σ1 hnegv (by
      rw [hxs, count_neg_lits]
      have e1 : ((List.range E).filter (fun n => !σ1 (n + 1))).length =
          ((List.range E).filter (fun n => !σ0 x (n + 1))).length := by
        congr 1; apply List.filter_congr; intro n hn; rw [List.mem_range] at hn
        rw [hag1 _ (by omega)]
      have e2 := List.length_eq_length_filter_add (l := List.range E) (f := fun n => σ0 x (n + 1))
      rw [List.length_range] at e2
      rw [e1]
      have e3 : ((List.range E).filter (fun n => !σ0 x (n + 1))).length =
          ((List.range E).filter (fun n => !(σ0 x (n + 1)))).length := rfl
      rw [hcnt] at e2
      omega)
  -- the lex chains
  obtain ⟨σ3, hag3, hs3, hv3, hm3⟩ := llAll_sound hp x perms (atMost (xs.map (fun v => -v))
      ((E : ℤ) - lo) (atMost xs hi E).2).2 σ2 hperm (by omega)
    (fun n hn => by rw [hag2 _ (by omega), hag1 _ (by omega)]; exact hσ0 n hn)
  have hag30 : ∀ v, v ≤ E → σ3 v = σ0 x v := fun v hv => by
    rw [hag3 v (by omega), hag2 v (by omega), hag1 v hv]
  -- every clause is satisfied by `σ3`
  have hsat : BipBridge.ListSat σ3 (coverCNF k cap lo hi perms blocked).1 := by
    unfold coverCNF
    simp only
    rw [hEeq]
    refine listSat_append (listSat_append (listSat_append (listSat_append ?_ ?_) ?_) hs3) ?_
    · refine listSat_agree (caps_sat hp x cap hcap) ?_ hag30
      intro c hc l hl
      unfold capClauses at hc
      simp only [List.mem_flatMap, List.mem_range] at hc
      obtain ⟨i, hi, hc⟩ := hc
      split_ifs at hc with hneg
      · exfalso; have : (0 : ℤ) ≤ popRow (gOf x) ⟨i, hi⟩ := by positivity
        have : (popRow (gOf x) ⟨i, hi⟩ : ℤ) ≤ cap i := hcap ⟨i, hi⟩; omega
      obtain ⟨sub, hsub, rfl⟩ := List.mem_map.mp hc
      obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
      have := (combos_sub _ _ sub hsub).1.subset hl'
      simp only [List.mem_map, List.mem_filter, List.mem_range] at this
      obtain ⟨j, ⟨hj, hji⟩, rfl⟩ := this
      have hji' : j ≠ i := by simpa using hji
      have hpos : 0 < xvN k i j := by unfold xvN; omega
      refine ⟨by omega, ?_⟩
      simp only [Int.natAbs_neg, Int.natAbs_natCast]
      unfold xvN
      rcases Nat.lt_or_gt_of_ne hji' with h | h
      · rw [if_neg (by omega)]; have := (hp.surj j i h hi).1; omega
      · rw [if_pos h]; have := (hp.surj i j h hj).1; omega
    · exact listSat_agree hs1 hv1 (fun v hv => by rw [hag3 v (by omega), hag2 v hv])
    · exact listSat_agree hs2 hv2 hag3
    · intro c hc
      obtain ⟨wb, hwb, rfl⟩ := List.mem_map.mp hc
      obtain ⟨n, hn, hne⟩ := hno wb hwb
      apply blocker_sat
      refine ⟨n, by rw [hlen wb hwb]; exact hn, ?_⟩
      rw [hag30 _ (by omega), hσ0 n hn]; exact hne
  exact not_listSat_of_toCNFV_unsat _ hU σ3 hsat


/-! ## Family certificates -/

/-- The checks `validate.py` makes, as propositions. -/
structure FamOK (fc : FamCert) : Prop where
  perms : ∀ p ∈ fc.perms, PermOK fc.k p ∧
    ∀ i < fc.k, (histDegs fc.v8 fc.v9 fc.v10)[pAt p i]! = (histDegs fc.v8 fc.v9 fc.v10)[i]!
  lens : ∀ b ∈ fc.blocked, b.1.length = Ek fc.k
  filt : ∀ b ∈ fc.blocked, ∀ U, b.2 = some U → failIIIPy fc.k (gW fc.k b.1) fc.D (finU fc.k U) = true

/-! ## The `validate.py` checks as one Boolean per data chunk -/

/-- A recorded permutation: a permutation of `0..k-1` preserving the degree vector. -/
def permOKB (k v8 v9 v10 : ℕ) (p : List ℕ) : Bool :=
  (List.range k).all (fun i => decide (pAt p i < k) &&
    ((histDegs v8 v9 v10)[pAt p i]! == (histDegs v8 v9 v10)[i]!)) &&
  (List.range k).all (fun i => (List.range k).all (fun j => !(pAt p i == pAt p j) || (i == j)))

/-- A raw blocker `(m, U)`: listed (`U = 0`) or failing `fail_iii` on `U`. -/
def blockOKB (k v8 v9 v10 : ℕ) (b : ℕ × ℕ) : Bool :=
  (b.2 == 0) || failIIIL k (fun a => (((histDegs v8 v9 v10)[a]! : ℕ) : ℤ)) b.1 b.2

theorem wbits_length (E m : ℕ) : (wbits E m).length = E := by simp [wbits]

theorem famOK_of_raw {k v8 v9 v10 : ℕ} {perms : List (List ℕ)} {raw : List (ℕ × ℕ)}
    (hk : k = 8 ∨ k = 9 ∨ k = 10) (hp : perms.all (permOKB k v8 v9 v10) = true)
    (hb : raw.all (blockOKB k v8 v9 v10) = true) : FamOK (rawCert k v8 v9 v10 perms raw) := by
  have hpf := pairFacts_census hk
  refine ⟨fun p hp' => ?_, fun b hb' => ?_, fun b hb' U hU => ?_⟩
  · have h := List.all_eq_true.mp hp p hp'
    unfold permOKB at h
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq,
      Bool.or_eq_true, Bool.not_eq_true'] at h
    refine ⟨⟨fun i hi => (h.1 i hi).1, fun i hi j hj e => ?_⟩, fun i hi => (h.1 i hi).2⟩
    rcases h.2 i hi j hj with h' | h'
    · simp at h'; exact absurd e h'
    · exact h'
  · obtain ⟨r, -, rfl⟩ := List.mem_map.mp hb'
    exact wbits_length _ _
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb'
    have h := List.all_eq_true.mp hb r hr
    split_ifs at hU with h0
    obtain rfl := Option.some.inj hU
    unfold blockOKB at h
    simp only [Bool.or_eq_true, beq_iff_eq, h0, false_or] at h
    have := failIIIL_eq hpf (fun a => (((histDegs v8 v9 v10)[a]! : ℕ) : ℤ)) r.1 r.2
    rw [h] at this
    exact this.symm

/-- The listed words of a family. -/
def listedWords (fc : FamCert) : List (List Bool) :=
  (fc.blocked.filter (fun b => b.2.isNone)).map Prod.fst

theorem gOf_eq_gW {k : ℕ} (hp : PairFacts k) (x : EColouring k 2) (wb : List Bool)
    (hw : ∀ n < Ek k, wd x n = wb.getD n false) : gOf x = gW k wb := by
  funext a b
  unfold gW
  by_cases hab : a.val < b.val
  · rw [if_pos hab, gOf_lt x hab, ← wd_pos hp, pos_edgeOf, hw _ (hp.surj _ _ hab b.isLt).1]
  · rw [if_neg hab]
    by_cases hba : b.val < a.val
    · rw [if_pos hba, gOf_symm, gOf_lt x hba, ← wd_pos hp, pos_edgeOf, hw _ (hp.surj _ _ hba a.isLt).1]
    · rw [if_neg hba]
      have : a = b := Fin.ext (by omega)
      subst this; simp [gOf]

/-- **What a family's UNSAT cover CNF certifies.** -/
theorem family_cover (fc : FamCert) (hok : FamOK fc) (hk : fc.k = 8 ∨ fc.k = 9 ∨ fc.k = 10)
    (hU : (toCNFV (famCNF fc).1).Unsat) (x : EColouring fc.k 2)
    (hf : FiltersOK fc.k fc.D (gOf x))
    (hlead : ∀ p, DPres fc.k fc.v8 fc.v9 fc.v10 p → lexView x ≤ lexView (actV p x)) :
    ∃ wb ∈ listedWords fc, ∀ n < Ek fc.k, wd x n = wb.getD n false := by
  have hp := pairFacts_census hk
  obtain ⟨hcap, ⟨hlo, hhi⟩, hiii⟩ := hf
  obtain ⟨wb, hwb, hw⟩ := cover_sound hp fc.cap _ _ fc.perms (fc.blocked.map Prod.fst) hU
    (fun wb hwb => by obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hwb; exact hok.lens b hb) x
    (fun i => by unfold FamCert.cap; rw [dif_pos i.isLt]; exact hcap i) hlo hhi
    (fun p hp' => ⟨(hok.perms p hp').1, hlead _ (fun i => by
      rw [permOf_val]; exact (hok.perms p hp').2 i.val i.isLt)⟩)
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hwb
  refine ⟨b.1, ?_, hw⟩
  cases hk2 : b.2 with
  | none => exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hb, by simp [hk2]⟩, rfl⟩
  | some U =>
    exfalso
    have h1 := hok.filt b hb U hk2
    rw [← gOf_eq_gW hp x b.1 hw, hiii] at h1
    exact Bool.noConfusion h1

/-- The `H` of a word in encoder numbering (position pair `(i, j)` is the edge `(i + 2, j + 2)`),
in row-major order, as in the list files. -/
def wordEdges (k : ℕ) (wb : List Bool) : List (ℕ × ℕ) :=
  (List.range (Ek k)).filterMap fun n =>
    if wb.getD n false then some ((pairAt k n).1 + 2, (pairAt k n).2 + 2) else none

theorem mem_wordEdges_srt {k : ℕ} (hp : PairFacts k) (wb : List Bool) (q : ℕ × ℕ) :
    q ∈ (wordEdges k wb).map (fun p => srt p.1 p.2) ↔
      ∃ n < Ek k, wb.getD n false = true ∧ q = ((pairAt k n).1 + 2, (pairAt k n).2 + 2) := by
  unfold wordEdges
  simp only [List.mem_map, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨e, ⟨n, hn, he⟩, rfl⟩
    split_ifs at he with hb
    simp only [Option.some.injEq] at he; subst he
    have hv := hp.valid n hn
    refine ⟨n, hn, hb, ?_⟩
    unfold srt; rw [if_pos (by omega)]
  · rintro ⟨n, hn, hb, rfl⟩
    have hv := hp.valid n hn
    refine ⟨_, ⟨n, hn, by rw [if_pos hb]⟩, ?_⟩
    unfold srt; rw [if_pos (by omega)]

theorem edges_match {k : ℕ} (hp : PairFacts k) (x : EColouring k 2) (wb : List Bool)
    (hw : ∀ n < Ek k, wd x n = wb.getD n false) (q : ℕ × ℕ) :
    q ∈ (wordEdges k wb).map (fun p => srt p.1 p.2) ↔ q ∈ hEdges x := by
  obtain ⟨u, w⟩ := q
  rw [mem_wordEdges_srt hp, mem_hEdges]
  constructor
  · rintro ⟨n, hn, hb, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hv := hp.valid n hn
    refine ⟨⟨(pairAt k n).1, by omega⟩, ⟨(pairAt k n).2, hv.2⟩, hv.1, ?_, rfl, rfl⟩
    have := hw n hn
    rw [hb] at this
    unfold wd at this; rw [dif_pos hv] at this
    simpa using this
  · rintro ⟨i, j, hij, hh, rfl, rfl⟩
    have hs := hp.surj i.val j.val hij j.isLt
    refine ⟨pIdx k i.val j.val, hs.1, ?_, by rw [hs.2]⟩
    rw [← hw _ hs.1, ← pos_edgeOf ⟨hij, j.isLt⟩, wd_pos hp]
    simpa using hh

/-- **`CensusCover` from the M0 certificates**: one family certificate per census case, its
`CNF.Unsat` verdict, the `validate.py` checks, and the listed words matched to cubes of `C`. -/
theorem censusCover_of_certs (C : List Cube) (cert : ℕ → ℕ → ℕ → ℕ → FamCert)
    (h : ∀ n8 n9 n10 v8 v9 v10, ValidCase n8 n9 n10 v8 v9 v10 →
      (cert (rootOf n8 n10) v8 v9 v10).k = rootOf n8 n10 ∧
      (cert (rootOf n8 n10) v8 v9 v10).v8 = v8 ∧ (cert (rootOf n8 n10) v8 v9 v10).v9 = v9 ∧
      (cert (rootOf n8 n10) v8 v9 v10).v10 = v10 ∧
      FamOK (cert (rootOf n8 n10) v8 v9 v10) ∧
      (toCNFV (famCNF (cert (rootOf n8 n10) v8 v9 v10)).1).Unsat ∧
      ∀ wb ∈ listedWords (cert (rootOf n8 n10) v8 v9 v10), ∃ c ∈ C,
        c.degs = histDegs n8 n9 n10 ∧ c.k = rootOf n8 n10 ∧
        c.comp = compF v8 v9 v10 ∧
        c.H = wordEdges (rootOf n8 n10) wb ∧ c.o.shortfall = false) :
    CensusCover C := by
  intro n8 n9 n10 v8 v9 v10 hv x hf hlead
  have hkm := rootOf_mem n8 n10
  obtain ⟨hk, h8, h9, h10, hok, hU, hlist⟩ := h n8 n9 n10 v8 v9 v10 hv
  generalize hfc : cert (rootOf n8 n10) v8 v9 v10 = fc at hk h8 h9 h10 hok hU hlist
  obtain ⟨k, w8, w9, w10, perms, blocked⟩ := fc
  simp only at hk h8 h9 h10
  subst h8 h9 h10
  subst hk
  obtain ⟨wb, hwb, hw⟩ := family_cover _ hok hkm hU x hf hlead
  obtain ⟨c, hc, hdeg, hck, hcomp, hH, hsf⟩ := hlist wb hwb
  refine ⟨c, hc, hdeg, hck, hcomp, fun q => ?_, hsf⟩
  rw [hH]
  exact edges_match (pairFacts_census hkm) x wb hw q

end SB.Rooted.M4.Cover

#print axioms SB.Rooted.M4.Cover.caps_sat
#print axioms SB.Rooted.M4.Cover.edges_count
#print axioms SB.Rooted.M4.Cover.llAll_sound
#print axioms SB.Rooted.M4.Cover.cover_sound
#print axioms SB.Rooted.M4.Cover.family_cover
#print axioms SB.Rooted.M4.Cover.censusCover_of_certs
#print axioms SB.Rooted.M4.Cover.famOK_of_raw
