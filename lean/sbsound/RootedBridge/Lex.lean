/-
# M3: `lexLeq` (rooted_encode.lex_leq) is satisfied by a colouring that is lex-below its image

`lexLeq 22 pairs` encodes, for the list `pairs = [(e₀,f₀), (e₁,f₁), …]`, that the colour sequence
`col e₀, col e₁, …` is lexicographically `≤` the sequence `col f₀, col f₁, …` (red < blue), with an
equality chain. `LexOK col pairs` is that statement (at the first index where the two sequences
differ, the `e` side is red and the `f` side blue). Truthful values: `q_t = (col e_t = col f_t)`,
`ch_t = (∀ s ≤ t, col e_s = col f_s)`.
-/
import RootedBridge.Edges

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

/-- The colour of the encoder pair `e` (blue = true). -/
def colP (col : Nat → Nat → Bool) (e : Nat × Nat) : Bool := col e.1 e.2

/-- Lex-`≤` of the `e`-sequence against the `f`-sequence, red < blue. -/
def LexOK (col : Nat → Nat → Bool) (pairs : Array ((Nat × Nat) × (Nat × Nat))) : Prop :=
  ∀ t (ht : t < pairs.size), (∀ s (hs : s < t), colP col pairs[s].1 = colP col pairs[s].2) →
    ¬ (colP col pairs[t].1 = true ∧ colP col pairs[t].2 = false)

/-- All pairs of the list are valid vertex pairs. -/
def PairsOK (pairs : Array ((Nat × Nat) × (Nat × Nat))) : Prop :=
  ∀ t (ht : t < pairs.size), VPair pairs[t].1.1 pairs[t].1.2 ∧ VPair pairs[t].2.1 pairs[t].2.2

theorem lv_upd_self (σ : Nat → Bool) (v : Nat) (b : Bool) (hv : 0 < v) :
    lv (upd σ v b) (v : Int) = b := by
  rw [lv_natCast _ hv]; simp [upd]

theorem lv_upd_other (σ : Nat → Bool) (v : Nat) (b : Bool) {l : Int} (hl : l.natAbs ≠ v) :
    lv (upd σ v b) l = lv σ l := by
  unfold lv upd; rw [if_neg hl]

/-- The invariant of the `lexLeq` loop after `t` positions. -/
def LexInv (col : Nat → Nat → Bool) (pairs : Array ((Nat × Nat) × (Nat × Nat))) (n₀ : Nat)
    (t : Nat) (eqch : Option Int) (s : St) (σ : Nat → Bool) : Prop :=
  n₀ ≤ s.nv ∧ EdgeOK col σ ∧
  (t < pairs.size →
    ((t = 0 ∧ eqch = none) ∨
     (0 < t ∧ ∃ ch : Nat, eqch = some (ch : Int) ∧ 0 < ch ∧ ch ≤ s.nv ∧
       σ ch = decide (∀ s' (hs : s' < t) (hs' : s' < pairs.size),
         colP col pairs[s'].1 = colP col pairs[s'].2))))

theorem lexLeq_spec (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a)
    (pairs : Array ((Nat × Nat) × (Nat × Nat))) (hP : PairsOK pairs) (hL : LexOK col pairs)
    (s : St) (σ : Nat → Bool) (H : Prop) (hn : 462 ≤ s.nv) (hE : EdgeOK col σ) :
    Spec H (lexLeq 22 pairs) s σ (fun _ _ _ => True) := by
  unfold lexLeq
  refine spec_bind (Q₁ := fun _ _ _ => True) ?_ (fun _ _ _ => spec_pure (fun _ _ _ => trivial))
  refine spec_forIn_range (I := LexInv col pairs s.nv) 0 pairs.size none _ ?_ ?_
    (fun _ _ _ _ _ _ => trivial)
  · intro _ _ _
    exact ⟨Nat.le_refl _, hE, fun _ => Or.inl ⟨rfl, rfl⟩⟩
  · intro t ht eqch s₁ σ₁
    simp only [Nat.zero_add, Nat.sub_zero] at ht ⊢
    generalize hpt : pairs.get!Internal t = ef
    have hef : ef = pairs[t] := by rw [← hpt]; exact getElem!_pos pairs t ht
    obtain ⟨hv1, hv2⟩ := hP t ht
    rw [← hef] at hv1 hv2
    have hLt := hL t ht
    rw [← hef] at hLt
    -- the truth of the prefix equality before and including `t`
    let pre : Prop := ∀ s' (hs : s' < t) (hs' : s' < pairs.size),
      colP col pairs[s'].1 = colP col pairs[s'].2
    let pre' : Prop := ∀ s' (hs : s' < t + 1) (hs' : s' < pairs.size),
      colP col pairs[s'].1 = colP col pairs[s'].2
    have hpre' : pre' ↔ pre ∧ colP col ef.1 = colP col ef.2 := by
      constructor
      · intro h
        refine ⟨fun s' hs hs' => h s' (by omega) hs', ?_⟩
        have := h t (by omega) ht
        rw [hef]; exact this
      · intro ⟨h1, h2⟩ s' hs hs'
        by_cases hst : s' < t
        · exact h1 s' hst hs'
        · have : s' = t := by omega
          subst this; rw [← hef]; exact h2
    have hcmp : ∀ σ' : Nat → Bool, EdgeOK col σ' →
        lv σ' (-varE 22 2 ef.1.1 ef.1.2 2) = !colP col ef.1 ∧
        lv σ' (-varE 22 2 ef.2.1 ef.2.2 1) = colP col ef.2 := by
      intro σ' hσ'
      rw [lv_neg _ (varE_bounds hv1 (Or.inr rfl)).2.2, lv_neg _ (varE_bounds hv2 (Or.inl rfl)).2.2,
        lv_varE hsym hσ' hv1 (Or.inr rfl), lv_varE hsym hσ' hv2 (Or.inl rfl)]
      simp [colV, colP]
    refine spec_bind (Q₁ := fun _ s₂ σ₂ => s₂.nv = s₁.nv ∧ σ₂ = σ₁) (spec_add (fun hH hg he => ?_)) ?_
    · obtain ⟨-, hn₁, hE₁, hI⟩ := hH
      have hb1 := varE_bounds hv1 (Or.inr rfl)
      have hb2 := varE_bounds hv2 (Or.inl rfl)
      obtain ⟨hc1, hc2⟩ := hcmp σ₁ hE₁
      rcases hI ht with ⟨rfl, rfl⟩ | ⟨ht0, ch, rfl, hch0, hchn, hchv⟩
      · refine ⟨?_, ?_, rfl, rfl⟩
        · intro l hl
          simp at hl
          rcases hl with rfl | rfl <;> simp only [Int.natAbs_neg] <;> omega
        · refine clauseSat_of_any (fun l hl => ?_) ?_
          · simp at hl; rcases hl with rfl | rfl <;> omega
          · have := hLt (fun s hs => absurd hs (by omega))
            simp only [Array.toList_append, List.any_append]
            simp [hc1, hc2]
            cases h1 : colP col ef.1 <;> cases h2 : colP col ef.2 <;> simp_all
      · refine ⟨?_, ?_, rfl, rfl⟩
        · intro l hl
          simp at hl
          rcases hl with rfl | rfl | rfl <;> simp only [Int.natAbs_neg, Int.natAbs_natCast] <;> omega
        · refine clauseSat_of_any (fun l hl => ?_) ?_
          · simp at hl; rcases hl with rfl | rfl | rfl <;> omega
          · simp only [Array.toList_append, List.any_append]
            simp [hc1, hc2, lv_neg_natCast _ hch0, hchv]
            by_cases hp : pre
            · have := hLt (fun s hs => hp s hs (by omega))
              cases h1 : colP col ef.1 <;> cases h2 : colP col ef.2 <;> simp_all
            · left
              exact Classical.byContradiction (fun hc =>
                hp (fun x hx hx' => Classical.byContradiction (fun h => hc ⟨x, hx, hx', h⟩)))
    · intro _ s₂ σ₂
      split
      · exact spec_pure (fun hH _ _ => by
          obtain ⟨⟨-, hn₁, hE₁, -⟩, -, -, -, -, hs2, hσ2⟩ := hH
          exact ⟨by omega, by rw [hσ2]; exact hE₁, fun h => absurd h (by omega)⟩)
      · next hlast =>
        have hlast' : t + 1 < pairs.size := by
          simp only [beq_iff_eq] at hlast; omega
        refine spec_bind (spec_pure (Q := fun _ s₃ σ₃ => s₃ = s₂ ∧ σ₃ = σ₂)
          (fun _ _ _ => ⟨rfl, rfl⟩)) ?_
        intro _ s₃ σ₃
        refine spec_bind (spec_fresh (decide (colP col ef.1 = colP col ef.2))
          (Q := fun q s₄ σ₄ => q = s₃.nv + 1 ∧ s₄.nv = s₃.nv + 1 ∧
            σ₄ = upd σ₃ (s₃.nv + 1) (decide (colP col ef.1 = colP col ef.2)))
          (fun _ _ _ => ⟨rfl, rfl, rfl⟩)) ?_
        intro q s₄ σ₄
        refine spec_bind (Q₁ := fun _ s₅ σ₅ => s₅.nv = s₄.nv ∧ σ₅ = σ₄)
          (spec_of_co_gated (post := fun _ => True)
            (F := EdgeOK col σ₄ ∧ 462 < q ∧ q = s₄.nv ∧
              σ₄ q = decide (colP col ef.1 = colP col ef.2)) ?_ ?_
            (fun _ _ _ _ => ⟨rfl, rfl⟩)) ?_
        · apply co_forIn_range
          intro c hc1 hc2 _ s'
          co_tac
          all_goals
            intro ⟨hE₄, hq0, hqn, hqv⟩
            have hc : c = 1 ∨ c = 2 := by omega
            have hb1 := varE_bounds hv1 hc
            have hb2 := varE_bounds hv2 hc
            have hl1 := lv_varE hsym hE₄ hv1 hc
            have hl2 := lv_varE hsym hE₄ hv2 hc
            refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
            · simp at hl
              rcases hl with rfl | rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> omega
            · simp at hl; rcases hl with rfl | rfl | rfl <;> omega
            · simp [lv_neg_natCast _ (by omega : 0 < q), lv_natCast _ (by omega : 0 < q),
                lv_neg _ hb1.2.2, lv_neg _ hb2.2.2, hl1, hl2, hqv]
              rcases hc with rfl | rfl <;> simp [colV, colP] <;>
                cases col ef.1.1 ef.1.2 <;> cases col ef.2.1 ef.2.2 <;> try simp
        · intro hH
          obtain ⟨⟨⟨⟨-, hn₁, hE₁, -⟩, -, -, -, -, hs2, hσ2⟩, -, -, -, -, hs3, hσ3⟩, -, -, -, -,
            hq, hs4, hσ4⟩ := hH
          subst hσ4 hq hσ3 hσ2 hs3
          refine ⟨EdgeOK.agree hE₁ (agree_upd _ _ _) (by omega), by omega, by omega, ?_⟩
          simp [upd]
        · intro _ s₅ σ₅
          refine spec_bind (spec_fresh (decide (pre ∧ colP col ef.1 = colP col ef.2))
            (Q := fun nc s₆ σ₆ => nc = s₅.nv + 1 ∧ s₆.nv = s₅.nv + 1 ∧
              σ₆ = upd σ₅ (s₅.nv + 1) (decide (pre ∧ colP col ef.1 = colP col ef.2)))
            (fun _ _ _ => ⟨rfl, rfl, rfl⟩)) ?_
          intro nc s₆ σ₆
          refine spec_of_co_gated (post := fun r => r = ForInStep.yield (some (nc : Int)))
            (F := EdgeOK col σ₆ ∧ 462 < q ∧ q < nc ∧ nc ≤ s₆.nv ∧
              σ₆ q = decide (colP col ef.1 = colP col ef.2) ∧
              σ₆ nc = decide (pre ∧ colP col ef.1 = colP col ef.2) ∧
              (eqch = none → t = 0) ∧
              (∀ p, eqch = some p → ∃ ch : Nat, p = ch ∧ 0 < ch ∧ ch < q ∧ σ₆ ch = decide pre))
            ?_ ?_ ?_
          · split
            all_goals
              co_tac
              all_goals
                intro ⟨hE₆, hq0, hqnc, hncn, hqv, hncv, hnone, hsome⟩
                first
                | (have ht0 := hnone rfl
                   refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
                   · simp at hl
                     rcases hl with rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> omega
                   · simp at hl; rcases hl with rfl | rfl <;> omega
                   · have hpre : pre := fun s' hs => absurd hs (by omega)
                     simp [lv_neg_natCast _ (by omega : 0 < q), lv_natCast _ (by omega : 0 < q),
                       lv_neg_natCast _ (by omega : 0 < nc), lv_natCast _ (by omega : 0 < nc), hqv, hncv,
                       hpre])
                | (obtain ⟨ch, rfl, hch0, hchq, hchv⟩ := hsome _ rfl
                   refine ⟨fun l hl => ?_, clauseSat_of_any (fun l hl => ?_) ?_⟩
                   · simp at hl
                     rcases hl with rfl | rfl | rfl <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast]) <;> omega
                   · simp at hl; rcases hl with rfl | rfl | rfl <;> omega
                   · simp [lv_neg_natCast _ (by omega : 0 < q), lv_natCast _ (by omega : 0 < q),
                       lv_neg_natCast _ (by omega : 0 < nc), lv_natCast _ (by omega : 0 < nc),
                       lv_neg_natCast _ hch0, lv_natCast _ hch0, hqv, hncv, hchv]
                     by_cases hp : pre <;> simp [hp] <;>
                       cases colP col ef.1 <;> cases colP col ef.2 <;> simp)
          · intro hH
            obtain ⟨H5, -, -, -, -, hnc, hs6, hσ6⟩ := hH
            obtain ⟨H4, -, -, -, -, hs5, hσ5⟩ := H5
            obtain ⟨H3, -, -, -, -, hq, hs4, hσ4⟩ := H4
            obtain ⟨H2, -, -, -, -, hs3, hσ3⟩ := H3
            obtain ⟨⟨-, hn₁, hE₁, hI⟩, -, -, -, -, hs2, hσ2⟩ := H2
            subst hσ6 hσ5 hσ4 hσ3 hσ2 hs3 hq hnc
            refine ⟨EdgeOK.agree (EdgeOK.agree hE₁ (agree_upd _ _ _) (by omega)) (agree_upd _ _ _)
              (by omega), by omega, by omega, by omega, by simp [upd]; omega, by simp [upd], ?_, ?_⟩
            · intro he
              rcases hI ht with ⟨h0, -⟩ | ⟨-, ch, hch, -⟩
              · exact h0
              · rw [he] at hch; cases hch
            · intro p hp
              rcases hI ht with ⟨-, h0⟩ | ⟨ht0, ch, hch, hch0, hchn, hchv⟩
              · rw [hp] at h0; cases h0
              · rw [hp] at hch
                refine ⟨ch, Option.some.inj hch, hch0, by omega, ?_⟩
                simp only [upd]
                rw [if_neg (by omega), if_neg (by omega), hchv]
          · intro x cs hH hx
            subst hx
            obtain ⟨H5, -, -, -, -, hnc, hs6, hσ6⟩ := hH
            obtain ⟨H4, -, -, -, -, hs5, hσ5⟩ := H5
            obtain ⟨H3, -, -, -, -, hq, hs4, hσ4⟩ := H4
            obtain ⟨H2, -, -, -, -, hs3, hσ3⟩ := H3
            obtain ⟨⟨-, hn₁, hE₁, hI⟩, -, -, -, -, hs2, hσ2⟩ := H2
            subst hσ6 hσ5 hσ4 hσ3 hσ2 hs3 hq hnc
            refine ⟨by simp only; omega,
              EdgeOK.agree (EdgeOK.agree hE₁ (agree_upd _ _ _) (by omega)) (agree_upd _ _ _) (by omega),
              fun _ => Or.inr ⟨by omega, s₅.nv + 1, rfl, by omega, by simp only; omega, ?_⟩⟩
            simp only [upd, if_pos]
            congr 1
            exact propext hpre'.symm


end SB.Rooted
namespace SB.Rooted
open LRATCatcher.Rooted

theorem mono_lexLeq (pairs : Array ((Nat × Nat) × (Nat × Nat))) : Mono (lexLeq 22 pairs) := by
  unfold lexLeq; mono_tac

/-- `lexLeq_spec` with its state hypotheses taken from the path condition. -/
theorem lexLeq_spec' (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a)
    (pairs : Array ((Nat × Nat) × (Nat × Nat))) (hP : PairsOK pairs) (hL : LexOK col pairs)
    (s : St) (σ : Nat → Bool) (H : Prop) (hpre : H → 462 ≤ s.nv ∧ EdgeOK col σ) :
    Spec H (lexLeq 22 pairs) s σ (fun _ _ _ => True) :=
  ⟨mono_lexLeq pairs s, fun hH => (lexLeq_spec col hsym pairs hP hL s σ H (hpre hH).1 (hpre hH).2).2 hH⟩

/-- `lexLeq_spec` with every hypothesis taken from the path condition. -/
theorem lexLeq_spec_gated (col : Nat → Nat → Bool) (hsym : ∀ a b, col a b = col b a)
    (pairs : Array ((Nat × Nat) × (Nat × Nat))) (s : St) (σ : Nat → Bool) (H : Prop)
    (hpre : H → PairsOK pairs ∧ LexOK col pairs ∧ 462 ≤ s.nv ∧ EdgeOK col σ) :
    Spec H (lexLeq 22 pairs) s σ (fun _ _ _ => True) :=
  ⟨mono_lexLeq pairs s, fun hH =>
    (lexLeq_spec col hsym pairs (hpre hH).1 (hpre hH).2.1 s σ H (hpre hH).2.2.1 (hpre hH).2.2.2).2 hH⟩

end SB.Rooted

#print axioms SB.Rooted.lexLeq_spec
