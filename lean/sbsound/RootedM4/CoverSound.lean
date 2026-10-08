/-
# M4, part 5b: soundness of the cover CNF gadgets

Satisfaction is `SB.BipBridge.ListSat` (DIMACS clause lists, 1-based variables). Each gadget is
shown satisfiable by an assignment that changes only its own fresh variables (`> nv`) and reads
its inputs (`≤ nv`) from the given assignment:

* `atMost_sound`: `Builder._atmost(lits, K)` with the truthful registers, if at most `K` of the
  literals are true;
* `llChain_sound`: the `ll_clauses` chain, with the truthful prefix-equality variables, for a
  word that is lex-`≤` its image (positions in row-major order).
-/
import RootedM4.CoverCNF
import RootedBridge.Canon

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace SB.Rooted.M4.Cover
open SB SB.BipBridge LRATCatcher.Rooted

/-! ## Literals -/

/-- The value of a literal. -/
def litT (σ : ℕ → Bool) (l : ℤ) : Bool := if 0 < l then σ l.natAbs else !σ l.natAbs

theorem litSat_iff {σ : ℕ → Bool} {l : ℤ} (h : l ≠ 0) : BipBridge.LitSat σ l ↔ litT σ l = true := by
  unfold SB.BipBridge.LitSat litT
  by_cases hl : 0 < l
  · simp [hl, h]
  · simp [hl, h]

theorem litT_neg (σ : ℕ → Bool) {l : ℤ} (h : l ≠ 0) : litT σ (-l) = !litT σ l := by
  unfold litT
  rw [Int.natAbs_neg]
  by_cases hl : 0 < l
  · rw [if_pos hl, if_neg (by omega)]
  · rw [if_neg hl, if_pos (by omega), Bool.not_not]

theorem litT_nat (σ : ℕ → Bool) {v : ℕ} (h : 0 < v) : litT σ (v : ℤ) = σ v := by
  unfold litT; rw [if_pos (by omega)]; simp

theorem litT_negNat (σ : ℕ → Bool) {v : ℕ} (h : 0 < v) : litT σ (-(v : ℤ)) = !σ v := by
  rw [litT_neg σ (by omega), litT_nat σ h]

theorem clauseSat_iff {σ : ℕ → Bool} {c : List ℤ} (hc : ∀ l ∈ c, l ≠ 0) :
    BipBridge.ClauseSat σ c ↔ ∃ l ∈ c, litT σ l = true := by
  unfold BipBridge.ClauseSat
  constructor
  · rintro ⟨l, hl, hs⟩; exact ⟨l, hl, (litSat_iff (hc l hl)).mp hs⟩
  · rintro ⟨l, hl, hs⟩; exact ⟨l, hl, (litSat_iff (hc l hl)).mpr hs⟩

/-! ## Variable ranges and agreement -/

/-- Every literal of `cs` is nonzero with variable at most `n`. -/
def VarsLe (cs : List (List ℤ)) (n : ℕ) : Prop := ∀ c ∈ cs, ∀ l ∈ c, l ≠ 0 ∧ l.natAbs ≤ n

theorem VarsLe.mono {cs : List (List ℤ)} {n m : ℕ} (h : VarsLe cs n) (hnm : n ≤ m) : VarsLe cs m :=
  fun c hc l hl => ⟨(h c hc l hl).1, le_trans (h c hc l hl).2 hnm⟩

theorem VarsLe.append {cs ds : List (List ℤ)} {n : ℕ} (h1 : VarsLe cs n) (h2 : VarsLe ds n) :
    VarsLe (cs ++ ds) n := by
  intro c hc; rcases List.mem_append.mp hc with h | h
  · exact h1 c h
  · exact h2 c h

theorem litT_agree {σ σ' : ℕ → Bool} {l : ℤ} {n : ℕ} (hl : l.natAbs ≤ n)
    (h : ∀ v, v ≤ n → σ' v = σ v) : litT σ' l = litT σ l := by
  unfold litT; rw [h _ hl]

theorem listSat_agree {σ σ' : ℕ → Bool} {cs : List (List ℤ)} {n : ℕ} (hs : BipBridge.ListSat σ cs)
    (hv : VarsLe cs n) (h : ∀ v, v ≤ n → σ' v = σ v) : BipBridge.ListSat σ' cs := by
  intro c hc
  obtain ⟨l, hl, hls⟩ := hs c hc
  have ⟨hl0, hln⟩ := hv c hc l hl
  refine ⟨l, hl, ?_⟩
  rw [litSat_iff hl0] at hls ⊢
  rw [litT_agree hln h]; exact hls

theorem listSat_append {σ : ℕ → Bool} {cs ds : List (List ℤ)} (h1 : BipBridge.ListSat σ cs)
    (h2 : BipBridge.ListSat σ ds) : BipBridge.ListSat σ (cs ++ ds) := by
  intro c hc; rcases List.mem_append.mp hc with h | h
  · exact h1 c h
  · exact h2 c h

/-! ## Prefix counts -/

/-- How many of the first `i + 1` literals are true. -/
def cnt (σ : ℕ → Bool) (lits : List ℤ) (i : ℕ) : ℕ := ((lits.take (i + 1)).filter (litT σ)).length

theorem cnt_succ (σ : ℕ → Bool) (lits : List ℤ) {i : ℕ} (hi : i + 1 < lits.length) :
    cnt σ lits (i + 1) = cnt σ lits i + (if litT σ (lits.getD (i + 1) 0) then 1 else 0) := by
  unfold cnt
  rw [List.take_succ (i := i + 1), List.filter_append, List.length_append]
  rw [List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]
  by_cases h : litT σ lits[i + 1] <;> simp [h]

theorem cnt_zero (σ : ℕ → Bool) (lits : List ℤ) (h : 0 < lits.length) :
    cnt σ lits 0 = if litT σ (lits.getD 0 0) then 1 else 0 := by
  unfold cnt
  obtain ⟨a, l, rfl⟩ : ∃ a l, lits = a :: l := by
    cases lits with
    | nil => simp at h
    | cons a l => exact ⟨a, l, rfl⟩
  by_cases ha : litT σ a <;> simp [ha]

theorem cnt_le_total (σ : ℕ → Bool) (lits : List ℤ) (i : ℕ) :
    cnt σ lits i ≤ (lits.filter (litT σ)).length :=
  ((List.take_sublist _ _).filter _).length_le

theorem cnt_mono (σ : ℕ → Bool) (lits : List ℤ) {i j : ℕ} (h : i ≤ j) :
    cnt σ lits i ≤ cnt σ lits j := by
  unfold cnt
  apply List.Sublist.length_le
  apply List.Sublist.filter
  exact (List.take_sublist_take_left (by omega))

theorem cnt_pos (σ : ℕ → Bool) (lits : List ℤ) {i : ℕ} (hi : i < lits.length)
    (h : litT σ (lits.getD i 0) = true) : 1 ≤ cnt σ lits i := by
  cases i with
  | zero => rw [cnt_zero σ lits (by omega), if_pos h]
  | succ i => rw [cnt_succ σ lits hi, if_pos h]; omega

theorem cnt_step (σ : ℕ → Bool) (lits : List ℤ) {i : ℕ} (hi : i + 1 < lits.length)
    (h : litT σ (lits.getD (i + 1) 0) = true) : cnt σ lits i + 1 ≤ cnt σ lits (i + 1) := by
  rw [cnt_succ σ lits hi, if_pos h]

theorem cnt_zero_le (σ : ℕ → Bool) (lits : List ℤ) : cnt σ lits 0 ≤ 1 := by
  unfold cnt
  calc ((lits.take 1).filter (litT σ)).length ≤ (lits.take 1).length := List.length_filter_le _ _
    _ ≤ 1 := by simp

/-! ## `atMost` -/

theorem getD_mem {lits : List ℤ} {i : ℕ} (hi : i < lits.length) : lits.getD i 0 ∈ lits := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi

theorem atMostCore_vars (lits : List ℤ) (Kn nv : ℕ) (hn : 2 ≤ lits.length) (hK : 1 ≤ Kn)
    (hl : ∀ l ∈ lits, l ≠ 0 ∧ l.natAbs ≤ nv) :
    VarsLe (atMostCore lits Kn nv) (nv + (lits.length - 1) * Kn) := by
  have hsle : ∀ i j, i + 1 < lits.length → j < Kn →
      nv + i * Kn + j + 1 ≤ nv + (lits.length - 1) * Kn := by
    intro i j hi hj
    have : (i + 1) * Kn ≤ (lits.length - 1) * Kn := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul] at this; omega
  have hL : ∀ i, i < lits.length → -(lits.getD i 0) ≠ 0 ∧
      (-(lits.getD i 0)).natAbs ≤ nv + (lits.length - 1) * Kn := by
    intro i hi
    have := hl _ (getD_mem hi)
    exact ⟨by omega, by rw [Int.natAbs_neg]; omega⟩
  have hS : ∀ i j, i + 1 < lits.length → j < Kn →
      ((nv + i * Kn + j + 1 : ℕ) : ℤ) ≠ 0 ∧
        ((nv + i * Kn + j + 1 : ℕ) : ℤ).natAbs ≤ nv + (lits.length - 1) * Kn := by
    intro i j hi hj
    exact ⟨by omega, by rw [Int.natAbs_natCast]; exact hsle i j hi hj⟩
  have hSn : ∀ i j, i + 1 < lits.length → j < Kn →
      -((nv + i * Kn + j + 1 : ℕ) : ℤ) ≠ 0 ∧
        (-((nv + i * Kn + j + 1 : ℕ) : ℤ)).natAbs ≤ nv + (lits.length - 1) * Kn := by
    intro i j hi hj
    exact ⟨by omega, by rw [Int.natAbs_neg, Int.natAbs_natCast]; exact hsle i j hi hj⟩
  intro c hc l hl'
  unfold atMostCore at hc
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap, List.mem_range'_1,
    List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | ⟨j, hj, rfl⟩) | ⟨i, hi, hc⟩) | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
    rcases hl' with rfl | rfl
    · exact hL 0 (by omega)
    · exact hS 0 0 (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
    subst hl'; exact hSn 0 j (by omega) (by omega)
  · obtain ⟨hi1, hi2⟩ := hi
    rcases hc with ((rfl | rfl) | ⟨j, hj, hc⟩) | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
      rcases hl' with rfl | rfl
      · exact hL i (by omega)
      · exact hS i 0 (by omega) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
      rcases hl' with rfl | rfl
      · exact hSn (i - 1) 0 (by omega) (by omega)
      · exact hS i 0 (by omega) (by omega)
    · obtain ⟨hj1, hj2⟩ := hj
      rcases hc with rfl | rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
        rcases hl' with rfl | rfl | rfl
        · exact hL i (by omega)
        · exact hSn (i - 1) (j - 1) (by omega) (by omega)
        · exact hS i j (by omega) (by omega)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
        rcases hl' with rfl | rfl
        · exact hSn (i - 1) j (by omega) (by omega)
        · exact hS i j (by omega) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
      rcases hl' with rfl | rfl
      · exact hL i (by omega)
      · exact hSn (i - 1) (Kn - 1) (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl'
    rcases hl' with rfl | rfl
    · exact hL (lits.length - 1) (by omega)
    · exact hSn (lits.length - 2) (Kn - 1) (by omega) (by omega)

theorem atMostCore_sat (lits : List ℤ) (Kn nv : ℕ) (σ : ℕ → Bool) (hn : Kn < lits.length)
    (hK : 1 ≤ Kn) (hl : ∀ l ∈ lits, l ≠ 0 ∧ l.natAbs ≤ nv)
    (hcnt : (lits.filter (litT σ)).length ≤ Kn) :
    ∃ σ' : ℕ → Bool, (∀ v, v ≤ nv → σ' v = σ v) ∧ BipBridge.ListSat σ' (atMostCore lits Kn nv) := by
  set n := lits.length with hndef
  let σ' : ℕ → Bool := fun v =>
    if nv < v ∧ v ≤ nv + (n - 1) * Kn then
      decide ((v - nv - 1) % Kn + 1 ≤ cnt σ lits ((v - nv - 1) / Kn))
    else σ v
  have hag : ∀ v, v ≤ nv → σ' v = σ v := by
    intro v hv; simp only [σ']; rw [if_neg (by omega)]
  have hreg : ∀ i j, i + 1 < n → j < Kn →
      σ' (nv + i * Kn + j + 1) = decide (j + 1 ≤ cnt σ lits i) := by
    intro i j hi hj
    have hle : i * Kn + j + 1 ≤ (n - 1) * Kn := by
      have : (i + 1) * Kn ≤ (n - 1) * Kn := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul] at this; omega
    simp only [σ']
    rw [if_pos ⟨by omega, by omega⟩]
    have e1 : nv + i * Kn + j + 1 - nv - 1 = j + Kn * i := by rw [Nat.mul_comm]; omega
    rw [e1, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ (by omega),
      Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj, Nat.zero_add]
  have hcntK : ∀ i, cnt σ lits i ≤ Kn := fun i => le_trans (cnt_le_total σ lits i) hcnt
  have hlit : ∀ i, i < n → litT σ' (lits.getD i 0) = litT σ (lits.getD i 0) :=
    fun i hi => litT_agree (hl _ (getD_mem hi)).2 hag
  have hl0 : ∀ i, i < n → lits.getD i 0 ≠ 0 := fun i hi => (hl _ (getD_mem hi)).1
  have hV := atMostCore_vars lits Kn nv (by omega) hK hl
  refine ⟨σ', hag, fun c hc => ?_⟩
  rw [clauseSat_iff (fun l hl' => (hV c hc l hl').1)]
  unfold atMostCore at hc
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap, List.mem_range'_1,
    List.not_mem_nil, or_false] at hc
  simp only [← hndef] at hc
  -- the literal values
  have negL : ∀ i, i < n → ¬ litT σ (lits.getD i 0) = true → litT σ' (-(lits.getD i 0)) = true := by
    intro i hi h; rw [litT_neg σ' (hl0 i hi), hlit i hi]; simpa using h
  have posS : ∀ i j, i + 1 < n → j < Kn → j + 1 ≤ cnt σ lits i →
      litT σ' ((nv + i * Kn + j + 1 : ℕ) : ℤ) = true := by
    intro i j hi hj h; rw [litT_nat σ' (by omega), hreg i j hi hj]; simpa using h
  have negS : ∀ i j, i + 1 < n → j < Kn → ¬ j + 1 ≤ cnt σ lits i →
      litT σ' (-((nv + i * Kn + j + 1 : ℕ) : ℤ)) = true := by
    intro i j hi hj h; rw [litT_negNat σ' (by omega), hreg i j hi hj]; simpa using h
  rcases hc with ((rfl | ⟨j, hj, rfl⟩) | ⟨i, hi, hc⟩) | rfl
  · -- [-l 0, s 0 0]
    by_cases h : litT σ (lits.getD 0 0) = true
    · exact ⟨_, by simp, posS 0 0 (by omega) (by omega) (cnt_pos σ lits (by omega) h)⟩
    · exact ⟨_, by simp, negL 0 (by omega) h⟩
  · -- [-s 0 j], 1 ≤ j < Kn
    have := cnt_zero_le σ lits
    exact ⟨_, by simp, negS 0 j (by omega) (by omega) (by omega)⟩
  · obtain ⟨hi1, hi2⟩ := hi
    have hin : i + 1 < n := by omega
    have hi' : (i - 1) + 1 = i := by omega
    have hm := cnt_mono σ lits (show i - 1 ≤ i by omega)
    have hst : litT σ (lits.getD i 0) = true → cnt σ lits (i - 1) + 1 ≤ cnt σ lits i := by
      intro hh; have := cnt_step σ lits (i := i - 1) (by omega) (by rw [hi']; exact hh)
      rwa [hi'] at this
    rcases hc with ((rfl | rfl) | ⟨j, hj, hc⟩) | rfl
    · -- [-l i, s i 0]
      by_cases h : litT σ (lits.getD i 0) = true
      · exact ⟨_, by simp, posS i 0 hin (by omega) (cnt_pos σ lits (by omega) h)⟩
      · exact ⟨_, by simp, negL i (by omega) h⟩
    · -- [-s (i-1) 0, s i 0]
      by_cases h : 1 ≤ cnt σ lits (i - 1)
      · exact ⟨_, by simp, posS i 0 hin (by omega) (by omega)⟩
      · exact ⟨_, by simp, negS (i - 1) 0 (by omega) (by omega) (by omega)⟩
    · obtain ⟨hj1, hj2⟩ := hj
      rcases hc with rfl | rfl
      · -- [-l i, -s (i-1) (j-1), s i j]
        by_cases h : litT σ (lits.getD i 0) = true
        · by_cases h' : j ≤ cnt σ lits (i - 1)
          · have := hst h
            exact ⟨_, by simp, posS i j hin (by omega) (by omega)⟩
          · exact ⟨_, by simp, negS (i - 1) (j - 1) (by omega) (by omega) (by omega)⟩
        · exact ⟨_, by simp, negL i (by omega) h⟩
      · -- [-s (i-1) j, s i j]
        by_cases h : j + 1 ≤ cnt σ lits (i - 1)
        · exact ⟨_, by simp, posS i j hin (by omega) (by omega)⟩
        · exact ⟨_, by simp, negS (i - 1) j (by omega) (by omega) h⟩
    · -- [-l i, -s (i-1) (Kn-1)]
      by_cases h : litT σ (lits.getD i 0) = true
      · have := hst h; have := hcntK i
        exact ⟨_, by simp, negS (i - 1) (Kn - 1) (by omega) (by omega) (by omega)⟩
      · exact ⟨_, by simp, negL i (by omega) h⟩
  · -- [-l (n-1), -s (n-2) (Kn-1)]
    by_cases h : litT σ (lits.getD (n - 1) 0) = true
    · have e : n - 2 + 1 = n - 1 := by omega
      have := cnt_step σ lits (i := n - 2) (by omega) (by rw [e]; exact h)
      rw [e] at this; have := hcntK (n - 1)
      exact ⟨_, by simp, negS (n - 2) (Kn - 1) (by omega) (by omega) (by omega)⟩
    · exact ⟨_, by simp, negL (n - 1) (by omega) h⟩

theorem atMost_sound (lits : List ℤ) (K : ℤ) (nv : ℕ) (σ : ℕ → Bool)
    (hl : ∀ l ∈ lits, l ≠ 0 ∧ l.natAbs ≤ nv)
    (hcnt : ((lits.filter (litT σ)).length : ℤ) ≤ K) :
    ∃ σ' : ℕ → Bool, (∀ v, v ≤ nv → σ' v = σ v) ∧ BipBridge.ListSat σ' (atMost lits K nv).1 ∧
      VarsLe (atMost lits K nv).1 (atMost lits K nv).2 ∧ nv ≤ (atMost lits K nv).2 := by
  unfold atMost
  split_ifs with h1 h2 h3
  · exact ⟨σ, fun _ _ => rfl, fun c hc => by simp at hc, fun c hc => by simp at hc, le_rfl⟩
  · exfalso; have : (0 : ℤ) ≤ _ := Int.natCast_nonneg ((lits.filter (litT σ)).length); omega
  · -- K = 0: every literal is false
    subst h3
    have hz : (lits.filter (litT σ)).length = 0 := by omega
    have hf : ∀ l ∈ lits, litT σ l = false := by
      intro l hl'
      by_contra hne
      have : l ∈ lits.filter (litT σ) := List.mem_filter.mpr ⟨hl', by simpa using hne⟩
      rw [List.length_eq_zero_iff.mp hz] at this; simp at this
    refine ⟨σ, fun _ _ => rfl, ?_, ?_, le_rfl⟩
    · intro c hc
      obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hc
      have h0 := (hl l hl').1
      rw [clauseSat_iff (by intro l' hl''; simp at hl''; subst hl''; omega)]
      refine ⟨-l, by simp, ?_⟩
      rw [litT_neg σ h0, hf l hl']; rfl
    · intro c hc l' hl''
      obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl''; subst hl''
      exact ⟨by have := (hl l hl').1; omega, by rw [Int.natAbs_neg]; exact (hl l hl').2⟩
  · have hK : 1 ≤ K.toNat := by omega
    obtain ⟨σ', hag, hs⟩ := atMostCore_sat lits K.toNat nv σ (by omega) hK hl (by omega)
    exact ⟨σ', hag, hs, atMostCore_vars lits K.toNat nv (by omega) hK hl, Nat.le_add_right _ _⟩


/-! ## The `ll_clauses` chain -/

section Chain
variable (E : ℕ) (w : ℕ → Bool) (f : ℕ → ℕ)

/-- The word agrees with its image on every position below `θ`. -/
def Pre (θ : ℕ) : Prop := ∀ m < θ, w m = w (f m)

/-- The word is lex-`≤` its image, position by position (`0 < 1`). -/
def LexLeW : Prop := ∀ n < E, Pre w f n → w n = true → w (f n) = true

/-- The guard is sound: a true guard variable means the prefix below `θ` agrees. -/
def GuardOK (σ : ℕ → Bool) : Option ℤ → ℕ → ℕ → Prop
  | none, θ, _ => Pre w f θ
  | some a, θ, nv => 0 < a ∧ a.natAbs ≤ nv ∧ (σ a.natAbs = true → Pre w f θ)

/-- A moved position as its pair of variables. -/
def toV (n : ℕ) : ℤ × ℤ := (((n + 1 : ℕ) : ℤ), ((f n + 1 : ℕ) : ℤ))

end Chain

theorem filter_range'_cons (q : ℕ → Bool) : ∀ (len θ n : ℕ) (rest : List ℕ),
    (List.range' θ len).filter q = n :: rest →
    θ ≤ n ∧ n < θ + len ∧ q n = true ∧ (∀ m, θ ≤ m → m < n → q m = false) ∧
      rest = (List.range' (n + 1) (θ + len - (n + 1))).filter q
  | 0, θ, n, rest, h => by simp at h
  | len + 1, θ, n, rest, h => by
    rw [List.range'_succ, List.filter_cons] at h
    by_cases hq : q θ = true
    · rw [if_pos hq] at h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨le_rfl, by omega, hq, fun m h1 h2 => absurd h1 (by omega), ?_⟩
      rw [show θ + (len + 1) - (θ + 1) = len by omega]
    · rw [if_neg hq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := filter_range'_cons q len (θ + 1) n rest h
      refine ⟨by omega, by omega, h3, fun m hm1 hm2 => ?_, by
        rw [h5, show θ + 1 + len - (n + 1) = θ + (len + 1) - (n + 1) by omega]⟩
      by_cases hm : m = θ
      · subst hm; simpa using hq
      · exact h4 m (by omega) hm2

theorem pre_gap {w : ℕ → Bool} {f : ℕ → ℕ} {θ n : ℕ} (h : Pre w f θ)
    (hgap : ∀ m, θ ≤ m → m < n → (f m != m) = false) : Pre w f n := by
  intro m hm
  by_cases hmθ : m < θ
  · exact h m hmθ
  · have := hgap m (by omega) hm
    simp at this; rw [this]

theorem pre_succ {w : ℕ → Bool} {f : ℕ → ℕ} {n : ℕ} (h : Pre w f n) (he : w n = w (f n)) :
    Pre w f (n + 1) := by
  intro m hm
  by_cases hmn : m < n
  · exact h m hmn
  · have : m = n := by omega
    subst this; exact he

theorem guard_cases {w : ℕ → Bool} {f : ℕ → ℕ} {σ : ℕ → Bool} {g : Option ℤ} {θ nv : ℕ}
    (hg : GuardOK w f σ g θ nv) :
    (∃ l ∈ guard g, l ≠ 0 ∧ litT σ l = true) ∨ Pre w f θ := by
  cases g with
  | none => exact Or.inr hg
  | some a =>
    obtain ⟨ha, hle, hp⟩ := hg
    by_cases hs : σ a.natAbs = true
    · exact Or.inr (hp hs)
    · left
      refine ⟨-a, by simp [guard], by omega, ?_⟩
      rw [litT_neg σ (by omega)]
      unfold litT; simp [ha]; simpa using hs

theorem guard_vars {w : ℕ → Bool} {f : ℕ → ℕ} {σ : ℕ → Bool} {g : Option ℤ} {θ nv : ℕ}
    (hg : GuardOK w f σ g θ nv) : ∀ l ∈ guard g, l ≠ 0 ∧ l.natAbs ≤ nv := by
  cases g with
  | none => intro l hl; simp [guard] at hl
  | some a =>
    obtain ⟨ha, hle, -⟩ := hg
    intro l hl; simp [guard] at hl; subst hl
    exact ⟨by omega, by rw [Int.natAbs_neg]; exact hle⟩

theorem guard_agree {w : ℕ → Bool} {f : ℕ → ℕ} {σ σ' : ℕ → Bool} {g : Option ℤ} {θ nv : ℕ}
    (hg : GuardOK w f σ g θ nv) (h : ∀ v, v ≤ nv → σ' v = σ v) : GuardOK w f σ' g θ nv := by
  cases g with
  | none => exact hg
  | some a =>
    obtain ⟨ha, hle, hp⟩ := hg
    exact ⟨ha, hle, fun hs => hp (by rw [← h _ hle]; exact hs)⟩

theorem llChain_sound (E : ℕ) (w : ℕ → Bool) (f : ℕ → ℕ) (hf : ∀ n < E, f n < E)
    (hlex : LexLeW E w f) :
    ∀ (L : List ℕ) (θ : ℕ) (g : Option ℤ) (nv : ℕ) (σ : ℕ → Bool),
      L = (List.range' θ (E - θ)).filter (fun n => f n != n) → E ≤ nv →
      (∀ n < E, σ (n + 1) = w n) → GuardOK w f σ g θ nv →
      ∃ σ' : ℕ → Bool, (∀ v, v ≤ nv → σ' v = σ v) ∧
        BipBridge.ListSat σ' (llChain (L.map (toV f)) g nv).1 ∧
        VarsLe (llChain (L.map (toV f)) g nv).1 (llChain (L.map (toV f)) g nv).2 ∧
        nv ≤ (llChain (L.map (toV f)) g nv).2 := by
  intro L
  induction L with
  | nil =>
    intro θ g nv σ _ _ _ _
    exact ⟨σ, fun _ _ => rfl, fun c hc => by simp [llChain] at hc,
      fun c hc => by simp [llChain] at hc, by simp [llChain]⟩
  | cons n rest ih =>
    intro θ g nv σ hL hE hσ hg
    obtain ⟨hθn, hnE, hmv, hgap, hrest⟩ := filter_range'_cons _ _ _ _ _ hL.symm
    have hnE' : n < E := by omega
    have hfn := hf n hnE'
    have hmv' : f n ≠ n := by simpa using hmv
    -- the first clause, under any assignment agreeing with `σ` up to `nv`
    have hx : ∀ σ' : ℕ → Bool, (∀ v, v ≤ nv → σ' v = σ v) →
        litT σ' (((n + 1 : ℕ) : ℤ)) = w n ∧ litT σ' (((f n + 1 : ℕ) : ℤ)) = w (f n) := by
      intro σ' hag
      rw [litT_nat σ' (by omega), litT_nat σ' (by omega), hag _ (by omega), hag _ (by omega),
        hσ n hnE', hσ (f n) hfn]
      exact ⟨rfl, rfl⟩
    have hpre : (∃ l ∈ guard g, l ≠ 0 ∧ litT σ l = true) ∨ Pre w f n := by
      rcases guard_cases hg with h | h
      · exact Or.inl h
      · exact Or.inr (pre_gap h hgap)
    have hgv := guard_vars hg
    have hC1 : ∀ σ' : ℕ → Bool, (∀ v, v ≤ nv → σ' v = σ v) →
        BipBridge.ClauseSat σ' (guard g ++ [-((n + 1 : ℕ) : ℤ), ((f n + 1 : ℕ) : ℤ)]) := by
      intro σ' hag
      rw [clauseSat_iff (by
        intro l hl; rcases List.mem_append.mp hl with h | h
        · exact (hgv l h).1
        · simp at h; omega)]
      obtain ⟨h1, h2⟩ := hx σ' hag
      rcases hpre with ⟨l, hl, hl0, hlt⟩ | hp
      · exact ⟨l, List.mem_append_left _ hl, by rw [litT_agree (hgv l hl).2 hag]; exact hlt⟩
      · by_cases hw : w n = true
        · exact ⟨((f n + 1 : ℕ) : ℤ), by simp, by rw [h2]; exact hlex n hnE' hp hw⟩
        · exact ⟨-((n + 1 : ℕ) : ℤ), by simp, by rw [litT_neg σ' (by omega), h1]; simpa using hw⟩
    have hV1 : ∀ m, nv ≤ m → ∀ l ∈ guard g ++ [-((n + 1 : ℕ) : ℤ), ((f n + 1 : ℕ) : ℤ)],
        l ≠ 0 ∧ l.natAbs ≤ m := by
      intro m hm l hl
      rcases List.mem_append.mp hl with h | h
      · exact ⟨(hgv l h).1, le_trans (hgv l h).2 hm⟩
      · simp at h; rcases h with rfl | rfl <;> simp <;> omega
    cases rest with
    | nil =>
      have hL : llChain (List.map (toV f) [n]) g nv =
          ([guard g ++ [-((n + 1 : ℕ) : ℤ), ((f n + 1 : ℕ) : ℤ)]], nv) := rfl
      rw [hL]
      refine ⟨σ, fun _ _ => rfl, ?_, ?_, le_rfl⟩
      · intro c hc; simp only [List.mem_singleton] at hc; subst hc
        exact hC1 σ (fun _ _ => rfl)
      · intro c hc; simp only [List.mem_singleton] at hc; subst hc
        exact hV1 nv le_rfl
    | cons r rest' =>
      -- the next guard variable `nv + 1`, set to the truth of `Pre (n+1)`
      classical
      let σ1 : ℕ → Bool := fun v => if v = nv + 1 then decide (Pre w f (n + 1)) else σ v
      have hag1 : ∀ v, v ≤ nv → σ1 v = σ v := fun v hv => by simp only [σ1]; rw [if_neg (by omega)]
      obtain ⟨σ', hag', hsat, hvars, hmono⟩ := ih (n + 1) (some ((nv + 1 : ℕ) : ℤ)) (nv + 1) σ1
        (by rw [hrest, Nat.add_sub_cancel' (le_trans hθn (le_of_lt hnE'))]) (by omega)
        (fun m hm => by rw [hag1 _ (by omega)]; exact hσ m hm)
        ⟨by omega, by rw [Int.natAbs_natCast],
          fun hs => by simp only [Int.natAbs_natCast, σ1, if_true] at hs; simpa using hs⟩
      have hagσ : ∀ v, v ≤ nv → σ' v = σ v := fun v hv => by rw [hag' v (by omega), hag1 v hv]
      have ha2 : σ' (nv + 1) = decide (Pre w f (n + 1)) := by rw [hag' _ le_rfl]; simp [σ1]
      have hL : llChain (List.map (toV f) (n :: r :: rest')) g nv =
          ((guard g ++ [-((n + 1 : ℕ) : ℤ), ((f n + 1 : ℕ) : ℤ)]) ::
            (guard g ++ [-((n + 1 : ℕ) : ℤ), ((nv + 1 : ℕ) : ℤ)]) ::
            (guard g ++ [((f n + 1 : ℕ) : ℤ), ((nv + 1 : ℕ) : ℤ)]) ::
            (llChain (List.map (toV f) (r :: rest')) (some ((nv + 1 : ℕ) : ℤ)) (nv + 1)).1,
           (llChain (List.map (toV f) (r :: rest')) (some ((nv + 1 : ℕ) : ℤ)) (nv + 1)).2) := rfl
      rw [hL]
      refine ⟨σ', hagσ, ?_, ?_, by omega⟩
      · intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | rfl | rfl | hc
        · exact hC1 σ' hagσ
        · -- guard ∧ x_n → a2
          rw [clauseSat_iff (by
            intro l hl; rcases List.mem_append.mp hl with h | h
            · exact (hgv l h).1
            · simp at h; omega)]
          obtain ⟨h1, h2⟩ := hx σ' hagσ
          rcases hpre with ⟨l, hl, hl0, hlt⟩ | hp
          · exact ⟨l, List.mem_append_left _ hl, by rw [litT_agree (hgv l hl).2 hagσ]; exact hlt⟩
          · by_cases hw : w n = true
            · refine ⟨((nv + 1 : ℕ) : ℤ), by simp, ?_⟩
              rw [litT_nat σ' (by omega), ha2]
              simpa using pre_succ hp (by rw [hw, hlex n hnE' hp hw])
            · exact ⟨-((n + 1 : ℕ) : ℤ), by simp, by rw [litT_neg σ' (by omega), h1]; simpa using hw⟩
        · -- guard ∧ ¬y_n → a2
          rw [clauseSat_iff (by
            intro l hl; rcases List.mem_append.mp hl with h | h
            · exact (hgv l h).1
            · simp at h; omega)]
          obtain ⟨h1, h2⟩ := hx σ' hagσ
          rcases hpre with ⟨l, hl, hl0, hlt⟩ | hp
          · exact ⟨l, List.mem_append_left _ hl, by rw [litT_agree (hgv l hl).2 hagσ]; exact hlt⟩
          · by_cases hw : w (f n) = true
            · exact ⟨((f n + 1 : ℕ) : ℤ), by simp, by rw [h2]; exact hw⟩
            · refine ⟨((nv + 1 : ℕ) : ℤ), by simp, ?_⟩
              rw [litT_nat σ' (by omega), ha2]
              have hwn : w n = false := by
                by_contra hc; exact hw (hlex n hnE' hp (by simpa using hc))
              simpa using pre_succ hp (by rw [hwn]; simpa using hw)
        · exact hsat c hc
      · intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | rfl | rfl | hc
        · exact hV1 _ (by omega)
        · intro l hl; rcases List.mem_append.mp hl with h | h
          · exact ⟨(hgv l h).1, by have := (hgv l h).2; omega⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl
            · exact ⟨by omega, by rw [Int.natAbs_neg, Int.natAbs_natCast]; omega⟩
            · exact ⟨by omega, by rw [Int.natAbs_natCast]; omega⟩
        · intro l hl; rcases List.mem_append.mp hl with h | h
          · exact ⟨(hgv l h).1, by have := (hgv l h).2; omega⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl
            · exact ⟨by omega, by rw [Int.natAbs_natCast]; omega⟩
            · exact ⟨by omega, by rw [Int.natAbs_natCast]; omega⟩
        · exact hvars c hc



/-! ## Pairs and positions -/

/-- `k (k - 1) / 2`, the number of pairs. -/
def Ek (k : ℕ) : ℕ := k * (k - 1) / 2

/-- The `n`-th pair of `pairsK k`. -/
def pairAt (k n : ℕ) : ℕ × ℕ := (pairsK k).getD n (0, 0)

/-- The finite facts about `pairsK` that the proofs use (kernel-checked for `k = 8, 9, 10`). -/
def pairFactsB (k : ℕ) : Bool :=
  ((pairsK k).length == Ek k) &&
  (List.range (Ek k)).all (fun n => decide ((pairAt k n).1 < (pairAt k n).2) &&
    decide ((pairAt k n).2 < k) && (pIdx k (pairAt k n).1 (pairAt k n).2 == n)) &&
  (List.range k).all (fun i => (List.range k).all (fun j =>
    !decide (i < j) || (decide (pIdx k i j < Ek k) && (pairAt k (pIdx k i j) == (i, j)))))

structure PairFacts (k : ℕ) : Prop where
  len : (pairsK k).length = Ek k
  valid : ∀ n < Ek k, (pairAt k n).1 < (pairAt k n).2 ∧ (pairAt k n).2 < k
  idx : ∀ n < Ek k, pIdx k (pairAt k n).1 (pairAt k n).2 = n
  surj : ∀ i j, i < j → j < k → pIdx k i j < Ek k ∧ pairAt k (pIdx k i j) = (i, j)

theorem pairFacts_of_B {k : ℕ} (h : pairFactsB k = true) : PairFacts k := by
  unfold pairFactsB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun n hn => ⟨(h2 n hn).1.1, (h2 n hn).1.2⟩, fun n hn => (h2 n hn).2, ?_⟩
  intro i j hij hj
  rcases h3 i (by omega) j hj with h | h
  · exact absurd hij h
  · exact h

theorem pairFactsB_8 : pairFactsB 8 = true := by decide +kernel
theorem pairFactsB_9 : pairFactsB 9 = true := by decide +kernel
theorem pairFactsB_10 : pairFactsB 10 = true := by decide +kernel

theorem pairFacts_census {k : ℕ} (hk : k = 8 ∨ k = 9 ∨ k = 10) : PairFacts k := by
  rcases hk with rfl | rfl | rfl
  · exact pairFacts_of_B pairFactsB_8
  · exact pairFacts_of_B pairFactsB_9
  · exact pairFacts_of_B pairFactsB_10

/-- On valid pairs `pIdx` is the row-major order (M3's `edgeIdx_lt_of_lt'`). -/
theorem pIdx_lt_iff {k i j i' j' : ℕ} (hij : i < j) (hj : j < k) (hij' : i' < j') (hj' : j' < k) :
    pIdx k i j < pIdx k i' j' ↔ (i < i' ∨ (i = i' ∧ j < j')) := by
  unfold pIdx
  constructor
  · intro h
    rcases Nat.lt_trichotomy i i' with h1 | h1 | h1
    · exact Or.inl h1
    · subst h1
      rcases Nat.lt_trichotomy j j' with h2 | h2 | h2
      · exact Or.inr ⟨rfl, h2⟩
      · subst h2; omega
      · have := edgeIdx_same_row' (n := k) (i := i + 1) (show i + 1 < j' + 1 by omega)
          (show j' + 1 < j + 1 by omega); omega
    · have := edgeIdx_lt_of_lt' (n := k) (i := i' + 1) (j := j' + 1) (i' := i + 1) (j' := j + 1)
        (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega)); omega
  · intro h
    exact edgeIdx_lt_of_lt' (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rcases h with h | ⟨h1, h2⟩ <;> [exact Or.inl (by omega); exact Or.inr ⟨by omega, by omega⟩])

theorem pIdx_inj {k i j i' j' : ℕ} (hij : i < j) (hj : j < k) (hij' : i' < j') (hj' : j' < k)
    (h : pIdx k i j = pIdx k i' j') : i = i' ∧ j = j' := by
  have h1 := (pIdx_lt_iff hij hj hij' hj').not.mp (by omega)
  have h2 := (pIdx_lt_iff hij' hj' hij hj).not.mp (by omega)
  omega

/-! ## The word of a graph -/

section Word
variable {k : ℕ}

/-- The edge of a valid pair. -/
def edgeOf (i j : ℕ) (h : i < j ∧ j < k) : Edge k := ⟨toLex (⟨i, by omega⟩, ⟨j, h.2⟩), h.1⟩

/-- Position `n` of the word of `x` (`0` off the valid positions). -/
def wd (x : EColouring k 2) (n : ℕ) : Bool :=
  if h : (pairAt k n).1 < (pairAt k n).2 ∧ (pairAt k n).2 < k then
    decide (x (edgeOf _ _ h) = 1) else false

/-- The position of an edge. -/
def pos (e : Edge k) : ℕ := pIdx k (ofLex e.val).1.val (ofLex e.val).2.val

theorem edge_valid (e : Edge k) : (ofLex e.val).1.val < (ofLex e.val).2.val ∧ (ofLex e.val).2.val < k :=
  ⟨e.prop, (ofLex e.val).2.isLt⟩

theorem pairAt_pos (hp : PairFacts k) (e : Edge k) :
    pos e < Ek k ∧ pairAt k (pos e) = ((ofLex e.val).1.val, (ofLex e.val).2.val) :=
  hp.surj _ _ (edge_valid e).1 (edge_valid e).2

theorem edgeOf_eq (e : Edge k) (h) : edgeOf (k := k) (ofLex e.val).1.val (ofLex e.val).2.val h = e := by
  apply Subtype.ext; rfl

theorem wd_pos (hp : PairFacts k) (x : EColouring k 2) (e : Edge k) :
    wd x (pos e) = decide (x e = 1) := by
  obtain ⟨-, hpa⟩ := pairAt_pos hp e
  unfold wd
  have hv : (pairAt k (pos e)).1 < (pairAt k (pos e)).2 ∧ (pairAt k (pos e)).2 < k := by
    rw [hpa]; exact edge_valid e
  rw [dif_pos hv]
  have he : edgeOf (k := k) (pairAt k (pos e)).1 (pairAt k (pos e)).2 hv = e := by
    apply Subtype.ext
    show toLex (_, _) = e.val
    have e1 : (pairAt k (pos e)).1 = (ofLex e.val).1.val := by rw [hpa]
    have e2 : (pairAt k (pos e)).2 = (ofLex e.val).2.val := by rw [hpa]
    have : e.val = toLex (ofLex e.val) := rfl
    rw [this]
    apply congrArg toLex
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  rw [he]

theorem pos_lt_iff (e e' : Edge k) : pos e' < pos e ↔ e' < e := by
  unfold pos
  rw [pIdx_lt_iff (edge_valid e').1 (edge_valid e').2 (edge_valid e).1 (edge_valid e).2]
  show _ ↔ e'.val < e.val
  have hl : e'.val < e.val ↔ toLex (ofLex e'.val) < toLex (ofLex e.val) := Iff.rfl
  rw [hl, Prod.Lex.toLex_lt_toLex]
  simp only [Fin.lt_def, Fin.ext_iff]

/-- The edge at a valid position. -/
theorem exists_edge (hp : PairFacts k) {n : ℕ} (hn : n < Ek k) : ∃ e : Edge k, pos e = n := by
  have hv := hp.valid n hn
  refine ⟨edgeOf _ _ hv, ?_⟩
  unfold pos edgeOf
  exact hp.idx n hn

end Word

/-! ## Recorded permutations -/

section Perms
variable {k : ℕ}

/-- A list `p` that is a permutation of `0..k-1` (`sorted(p) == list(range(k))`). -/
def PermOK (k : ℕ) (p : List ℕ) : Prop :=
  (∀ i < k, pAt p i < k) ∧ (∀ i < k, ∀ j < k, pAt p i = pAt p j → i = j)

instance (k : ℕ) (p : List ℕ) : Decidable (PermOK k p) := by unfold PermOK; infer_instance

/-- The permutation of `Fin k` given by a valid list. -/
noncomputable def permOf {p : List ℕ} (h : PermOK k p) : Equiv.Perm (Fin k) :=
  Equiv.ofBijective (fun i => ⟨pAt p i.val, h.1 i.val i.isLt⟩)
    (Finite.injective_iff_bijective.mp (fun i j e => Fin.ext (h.2 _ i.isLt _ j.isLt (congrArg Fin.val e))))

theorem permOf_val {p : List ℕ} (h : PermOK k p) (i : Fin k) : (permOf h i).val = pAt p i.val := rfl

/-- The image position of position `n` under `p`. -/
def fP (k : ℕ) (p : List ℕ) (n : ℕ) : ℕ :=
  pIdx k (srt (pAt p (pairAt k n).1) (pAt p (pairAt k n).2)).1 (srt (pAt p (pairAt k n).1) (pAt p (pairAt k n).2)).2

theorem srt_valid {a b k : ℕ} (ha : a < k) (hb : b < k) (hab : a ≠ b) :
    (srt a b).1 < (srt a b).2 ∧ (srt a b).2 < k := by
  unfold srt; split_ifs <;> simp <;> omega

theorem fP_lt (hp : PairFacts k) {p : List ℕ} (h : PermOK k p) {n : ℕ} (hn : n < Ek k) :
    fP k p n < Ek k := by
  have hv := hp.valid n hn
  have := srt_valid (h.1 (pairAt k n).1 (by omega)) (h.1 (pairAt k n).2 hv.2) (fun e => by have := h.2 (pairAt k n).1 (by omega) (pairAt k n).2 hv.2 e; omega)
  exact (hp.surj _ _ this.1 this.2).1

/-- The word of `actV (permOf p) x` at position `n` is the word of `x` at `fP p n`. -/
theorem wd_fP (hp : PairFacts k) {p : List ℕ} (h : PermOK k p) (x : EColouring k 2) (e : Edge k) :
    wd x (fP k p (pos e)) = decide (actV (permOf h) x e = 1) := by
  obtain ⟨-, hpa⟩ := pairAt_pos hp e
  have hne : permOf h (ofLex e.val).1 ≠ permOf h (ofLex e.val).2 :=
    (permOf h).injective.ne (ne_of_lt e.prop)
  let e' := mkEdge (permOf h (ofLex e.val).1) (permOf h (ofLex e.val).2) hne
  have : fP k p (pos e) = pos e' := by
    unfold fP
    rw [hpa]
    unfold pos
    simp only [e', mkEdge]
    split_ifs with hlt
    · simp only [permOf_val] ; unfold srt
      rw [if_pos (by have : (permOf h (ofLex e.val).1).val < (permOf h (ofLex e.val).2).val := hlt
                     rw [permOf_val, permOf_val] at this; omega)]
      rfl
    · simp only [permOf_val]; unfold srt
      have : (permOf h (ofLex e.val).2).val < (permOf h (ofLex e.val).1).val := by
        have := Fin.val_ne_of_ne hne; have : ¬ (permOf h (ofLex e.val).1).val < (permOf h (ofLex e.val).2).val := hlt
        omega
      rw [permOf_val, permOf_val] at this
      rw [if_neg (by omega)]
      rfl
  rw [this, wd_pos hp]
  rfl

/-- **The lex comparison in position form.** -/
theorem lexLeW_of_lexView (hp : PairFacts k) {p : List ℕ} (h : PermOK k p) (x : EColouring k 2)
    (hle : lexView x ≤ lexView (actV (permOf h) x)) : LexLeW (Ek k) (wd x) (fP k p) := by
  intro n hn hpre hw
  obtain ⟨e, rfl⟩ := exists_edge hp hn
  have hagree : ∀ e' < e, x e' = actV (permOf h) x e' := by
    intro e' he'
    have := hpre (pos e') ((pos_lt_iff e e').mpr he')
    rw [wd_pos hp, wd_fP hp h] at this
    exact fin2_eq_of this
  have hle' := lex_first_diff hle e hagree
  rw [wd_pos hp] at hw
  rw [wd_fP hp h]
  simp only [decide_eq_true_eq] at hw ⊢
  rw [hw] at hle'
  revert hle'; generalize actV (permOf h) x e = z; revert z; decide

theorem filterMap_eq_map_filter {α β : Type*} (G : α → Option β) (q : α → Bool) (hh : α → β) :
    ∀ l : List α, (∀ a ∈ l, G a = if q a then some (hh a) else none) →
      l.filterMap G = (l.filter q).map hh
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, h a (by simp), List.filter_cons]
    have ih := filterMap_eq_map_filter G q hh l (fun b hb => h b (by simp [hb]))
    split_ifs <;> simp [ih]

theorem pairsK_eq (hp : PairFacts k) : pairsK k = (List.range (Ek k)).map (pairAt k) := by
  apply List.ext_getElem (by simp [hp.len])
  intro n h1 h2
  simp [pairAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

theorem xv_pair (hp : PairFacts k) {n : ℕ} (hn : n < Ek k) :
    xv k (pairAt k n).1 (pairAt k n).2 = ((n + 1 : ℕ) : ℤ) := by
  unfold xv xvN; rw [if_pos (hp.valid n hn).1, hp.idx n hn]

/-- `movedVars` is the chain input of `llChain_sound`. -/
theorem movedVars_eq (hp : PairFacts k) {p : List ℕ} (h : PermOK k p) :
    movedVars k p = ((List.range' 0 (Ek k - 0)).filter (fun n => fP k p n != n)).map (toV (fP k p)) := by
  unfold movedVars
  rw [pairsK_eq hp, List.filterMap_map, Nat.sub_zero, ← List.range_eq_range']
  apply filterMap_eq_map_filter
  intro n hn
  rw [List.mem_range] at hn
  have hv := hp.valid n hn
  have hs := srt_valid (h.1 (pairAt k n).1 (by omega)) (h.1 (pairAt k n).2 hv.2) (fun e => by have := h.2 (pairAt k n).1 (by omega) (pairAt k n).2 hv.2 e; omega)
  simp only [Function.comp]
  by_cases hf : fP k p n = n
  · have : srt (pAt p (pairAt k n).1) (pAt p (pairAt k n).2) = pairAt k n := by
      have := pIdx_inj hs.1 hs.2 hv.1 hv.2 (by rw [hp.idx n hn]; exact hf)
      exact Prod.ext this.1 this.2
    simp [this, hf]
  · have : ¬ srt (pAt p (pairAt k n).1) (pAt p (pairAt k n).2) = pairAt k n := by
      intro e; apply hf; unfold fP; rw [e]; exact hp.idx n hn
    simp only [this, if_false, hf, bne_iff_ne, ne_eq, not_false_eq_true, if_true, toV]
    rw [xv_pair hp hn]
    unfold xv xvN fP; rw [if_pos hs.1]

end Perms

end SB.Rooted.M4.Cover

#print axioms SB.Rooted.M4.Cover.atMost_sound
#print axioms SB.Rooted.M4.Cover.llChain_sound
#print axioms SB.Rooted.M4.Cover.pairFacts_census
#print axioms SB.Rooted.M4.Cover.lexLeW_of_lexView
#print axioms SB.Rooted.M4.Cover.movedVars_eq
