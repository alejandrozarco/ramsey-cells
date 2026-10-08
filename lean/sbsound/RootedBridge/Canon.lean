/-
# M3: the interface `RootedCanon` and the soundness bridge for the rooted encoder

`RootedCanon a k cells Hs o` says that the 2-colouring `a` of `K_22` (`SB` colour 1 = BLUE = encoder
colour 2) is in the canonical rooted form a cube `(degs, k, comp, H)` assumes, stated about `a`
alone (vertex `x : Fin 22` is encoder vertex `x + 1`; the root is `0`):

* `row1`   : the root's blue neighbours are exactly the vertices `1..k`;
* `deg`    : vertex `v` has blue degree `cells.D[v]` (the cube's degree list, `cellsOf`);
* `hunits` : the blue graph induced on `1..k` is `H` (`Hs = normH H`, the encoder's normal form);
* `wlex`   : `a` is lex-`≤` (`SB.lexView`, red < blue, row-major edges) its image under every
             adjacent transposition `(v v+1)` inside a W-cell;
* `wall`   : (option `wallpairs`) the same for every transposition `(p q)` inside a W-cell;
* `auth`   : (option `auth`) the same for every permutation fixing all non-N-cell vertices, sending
             each N-cell vertex into its cell, and sending every edge of `Hs` into `Hs` (`CellAut`).

`CubeWF` collects the facts about the cube data the bridge needs (cells inside `1..22`, N-cell
vertices distinct).

**Main results.**
* `rooted_bridge`: a good colouring (`NoKst a 0 2 8 ∧ NoKst a 1 2 5`) in `RootedCanon` form for a
  well-formed cube satisfies every clause the encoder emits for that cube (options with
  `shortfall = false`; all of O1, O2, O3).
* `no_canon_of_unsat`: hence `CNF.Unsat` of the printed formula excludes every such colouring.
* `no_canon_of_children_unsat`: the same for a parent proved through a complete split.
-/
import RootedLemmas.FiltersPy
import Sbsound.SBKeystone
import Sbsound.BipBridge
import RootedBridge.LexOrder
import RootedBridge.Split

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

open SB Finset

/-! ## The colouring at the encoder's level -/

/-- `x ↦ x - 1` as a vertex of `Fin 22` (total; meant for `1 ≤ x ≤ 22`). -/
def fv (u : Nat) : Fin 22 := ⟨(u - 1) % 22, Nat.mod_lt _ (by decide)⟩

theorem fv_val {u : Nat} (h1 : 1 ≤ u) (h2 : u ≤ 22) : (fv u).val = u - 1 := by
  simp only [fv]; omega

theorem fv_succ (x : Fin 22) : fv (x.val + 1) = x := by
  apply Fin.ext; simp only [fv]; have := x.isLt; omega

/-- Blue (= `1`) on the encoder pair `{i, j}`, `false` off the valid pairs. -/
def colOf (a : EColouring 22 2) (i j : Nat) : Bool :=
  if h : fv i ≠ fv j ∧ 1 ≤ i ∧ i ≤ 22 ∧ 1 ≤ j ∧ j ≤ 22 then decide (a (mkEdge (fv i) (fv j) h.1) = 1)
  else false

theorem colOf_symm (a : EColouring 22 2) (i j : Nat) : colOf a i j = colOf a j i := by
  unfold colOf
  by_cases h : fv i ≠ fv j ∧ 1 ≤ i ∧ i ≤ 22 ∧ 1 ≤ j ∧ j ≤ 22
  · have h' : fv j ≠ fv i ∧ 1 ≤ j ∧ j ≤ 22 ∧ 1 ≤ i ∧ i ≤ 22 :=
      ⟨fun e => h.1 e.symm, h.2.2.2.1, h.2.2.2.2, h.2.1, h.2.2.1⟩
    rw [dif_pos h, dif_pos h', mkEdge_comm]
  · have h' : ¬ (fv j ≠ fv i ∧ 1 ≤ j ∧ j ≤ 22 ∧ 1 ≤ i ∧ i ≤ 22) := fun h' =>
      h ⟨fun e => h'.1 e.symm, h'.2.2.2.1, h'.2.2.2.2, h'.2.1, h'.2.2.1⟩
    rw [dif_neg h, dif_neg h']

/-- The `Lemma12` colouring of `a`. -/
def kOf (a : EColouring 22 2) : Colouring 22 where
  C x y := colOf a (x.val + 1) (y.val + 1)
  symm x y := colOf_symm a _ _

theorem kOf_C (a : EColouring 22 2) (x y : Fin 22) :
    (kOf a).C x y = if h : x = y then false else decide (a (mkEdge x y h) = 1) := by
  show colOf a (x.val + 1) (y.val + 1) = _
  unfold colOf
  have hx := x.isLt; have hy := y.isLt
  by_cases h : x = y
  · subst h; simp [fv_succ]
  · have h' : fv (x.val + 1) ≠ fv (y.val + 1) ∧ 1 ≤ x.val + 1 ∧ x.val + 1 ≤ 22 ∧ 1 ≤ y.val + 1 ∧
        y.val + 1 ≤ 22 := ⟨by rw [fv_succ, fv_succ]; exact h, by omega, by omega, by omega, by omega⟩
    rw [dif_pos h', dif_neg h]
    simp only [fv_succ]

theorem colOf_eq_kOf (a : EColouring 22 2) {i j : Nat} (hi1 : 1 ≤ i) (hi2 : i ≤ 22) (hj1 : 1 ≤ j)
    (hj2 : j ≤ 22) : colOf a i j = (kOf a).C (fv i) (fv j) := by
  show colOf a i j = colOf a ((fv i).val + 1) ((fv j).val + 1)
  rw [fv_val hi1 hi2, fv_val hj1 hj2, Nat.sub_add_cancel hi1, Nat.sub_add_cancel hj1]

theorem fin2_cases (z : Fin 2) : (if z = 1 then (1 : Fin 2) else 0) = z := by
  fin_cases z <;> rfl

theorem toE_kOf (a : EColouring 22 2) : Colouring.toE (kOf a) = a := by
  funext e
  unfold Colouring.toE
  rw [kOf_C]
  have hne : (ofLex e.val).1 ≠ (ofLex e.val).2 := ne_of_lt e.prop
  rw [dif_neg hne]
  have he : mkEdge (ofLex e.val).1 (ofLex e.val).2 hne = e := by
    rw [mkEdge_pos hne e.prop]; rfl
  rw [he]
  simp only [decide_eq_true_eq]
  exact fin2_cases (a e)

theorem fin2_eq_of {u v : Fin 2} (h : decide (u = 1) = decide (v = 1)) : u = v := by
  revert u v; decide

/-! ## Edges: `Edge 22` against `edgesOf 22` -/

/-- The index of an edge in `edgesOf 22`. -/
def eIdx (e : Edge 22) : Nat := edgeIdx 22 ((ofLex e.val).1.val + 1) ((ofLex e.val).2.val + 1)

theorem eIdx_props (e : Edge 22) :
    ∃ h : eIdx e < (edgesOf 22).size,
      (edgesOf 22)[eIdx e] = ((ofLex e.val).1.val + 1, (ofLex e.val).2.val + 1) := by
  have hlt : (ofLex e.val).1.val < (ofLex e.val).2.val := e.prop
  have h2 := (ofLex e.val).2.isLt
  have hg := edgesOf_get (i := (ofLex e.val).1.val + 1) (j := (ofLex e.val).2.val + 1)
    (by omega) (by omega) (by omega)
  have hsz : eIdx e < (edgesOf 22).size := (Array.getElem?_eq_some_iff.mp hg).1
  exact ⟨hsz, Option.some.inj ((Array.getElem?_eq_getElem hsz).symm.trans hg)⟩

theorem eIdx_lt_iff (e e' : Edge 22) : eIdx e' < eIdx e ↔ e' < e := by
  have h1 : (ofLex e.val).1.val < (ofLex e.val).2.val := e.prop
  have h1' : (ofLex e'.val).1.val < (ofLex e'.val).2.val := e'.prop
  have h2 := (ofLex e.val).2.isLt
  have h2' := (ofLex e'.val).2.isLt
  unfold eIdx
  rw [edgeIdx_lt_iff (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  show _ ↔ e'.val < e.val
  have hl : e'.val < e.val ↔ toLex (ofLex e'.val) < toLex (ofLex e.val) := Iff.rfl
  rw [hl, Prod.Lex.toLex_lt_toLex]
  simp only [Fin.lt_def, Fin.ext_iff]
  omega

theorem eIdx_surj {p : Nat} (hp : p < (edgesOf 22).size) :
    ∃ e : Edge 22, eIdx e = p := by
  rw [edgesOf_size] at hp
  obtain ⟨i, j, -, hi, hij, hj, hidx⟩ := edgesOf_mem hp
  refine ⟨⟨toLex (fv i, fv j), ?_⟩, ?_⟩
  · show fv i < fv j
    rw [Fin.lt_def, fv_val hi (by omega), fv_val (by omega) hj]; omega
  · unfold eIdx
    show edgeIdx 22 ((fv i).val + 1) ((fv j).val + 1) = p
    rw [fv_val hi (by omega), fv_val (by omega) hj, Nat.sub_add_cancel hi,
      Nat.sub_add_cancel (by omega : 1 ≤ j)]
    exact hidx

/-- A permutation of `Fin 22` as a map of encoder vertices (identity off `1..22`). -/
def τN (τ : Equiv.Perm (Fin 22)) (u : Nat) : Nat :=
  if 1 ≤ u ∧ u ≤ 22 then (τ (fv u)).val + 1 else u

theorem colP_edge (a : EColouring 22 2) (e : Edge 22) :
    colP (colOf a) ((ofLex e.val).1.val + 1, (ofLex e.val).2.val + 1) = decide (a e = 1) := by
  unfold colP
  simp only
  rw [colOf_eq_kOf a (by omega) (by have := (ofLex e.val).1.isLt; omega) (by omega)
    (by have := (ofLex e.val).2.isLt; omega), fv_succ, fv_succ, kOf_C]
  have hne : (ofLex e.val).1 ≠ (ofLex e.val).2 := ne_of_lt e.prop
  rw [dif_neg hne, mkEdge_pos hne e.prop]
  rfl

theorem colP_srt (a : EColouring 22 2) (i j : Nat) : colP (colOf a) (srt i j) = colOf a i j := by
  unfold colP srt; split <;> simp [colOf_symm]

theorem colP_img (a : EColouring 22 2) (τ : Equiv.Perm (Fin 22)) (e : Edge 22) :
    colP (colOf a) (imgE (τN τ) ((ofLex e.val).1.val + 1, (ofLex e.val).2.val + 1)) =
      decide (actV τ a e = 1) := by
  unfold imgE
  rw [colP_srt]
  simp only [τN]
  rw [if_pos ⟨by omega, by have := (ofLex e.val).1.isLt; omega⟩,
    if_pos ⟨by omega, by have := (ofLex e.val).2.isLt; omega⟩, fv_succ, fv_succ]
  rw [colOf_eq_kOf a (by omega) (by have := (τ (ofLex e.val).1).isLt; omega) (by omega)
    (by have := (τ (ofLex e.val).2).isLt; omega), fv_succ, fv_succ, kOf_C]
  have hne : τ (ofLex e.val).1 ≠ τ (ofLex e.val).2 := τ.injective.ne (ne_of_lt e.prop)
  rw [dif_neg hne]
  rfl

theorem lex_first_diff {ι : Type*} [LinearOrder ι] {β : Type*} [PartialOrder β] {x y : ι → β}
    (h : toLex x ≤ toLex y) (e : ι) (hagree : ∀ e' < e, x e' = y e') : x e ≤ y e := by
  rcases h.lt_or_eq with hlt | heq
  · obtain ⟨i, hi, hxi⟩ := hlt
    rcases lt_trichotomy i e with h1 | rfl | h1
    · exact absurd (hagree i h1) (ne_of_lt hxi)
    · exact le_of_lt hxi
    · exact le_of_eq (hi e h1)
  · have : x = y := by simpa using congrArg ofLex heq
    rw [this]

/-- **`lexView` to first-difference form.** -/
theorem lexLeE_of_lexView (a : EColouring 22 2) (τ : Equiv.Perm (Fin 22))
    (h : lexView a ≤ lexView (actV τ a)) : LexLeE (colOf a) (τN τ) := by
  intro p hp hpre ⟨h1, h2⟩
  obtain ⟨e, rfl⟩ := eIdx_surj hp
  obtain ⟨hs, hes⟩ := eIdx_props e
  have hagree : ∀ e' < e, a e' = actV τ a e' := by
    intro e' he'
    obtain ⟨hs', hes'⟩ := eIdx_props e'
    have := hpre (eIdx e') ((eIdx_lt_iff e e').mpr he')
    rw [hes', colP_edge, colP_img] at this
    exact fin2_eq_of this
  have hle := lex_first_diff h e hagree
  rw [hes, colP_edge] at h1
  rw [hes, colP_img] at h2
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2
  have : actV τ a e = 0 := by
    revert h2; generalize actV τ a e = z; revert z; decide
  rw [h1, this] at hle
  exact absurd hle (by decide)

/-! ## Counting: lists over `1..22` against `Finset`s over `Fin 22` -/

theorem range'_eq_map_finRange (n : Nat) :
    List.range' 1 n = (List.finRange n).map (fun x => x.val + 1) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_range', Nat.add_comm]

theorem count_fin (P : Fin 22 → Prop) [DecidablePred P] (Q : Nat → Bool)
    (hQ : ∀ x : Fin 22, Q (x.val + 1) = decide (P x)) :
    ((List.range' 1 22).filter Q).length = (univ.filter P).card := by
  rw [range'_eq_map_finRange, List.filter_map, List.length_map]
  have : (List.finRange 22).filter (Q ∘ fun x => x.val + 1) =
      (List.finRange 22).filter (fun x => decide (P x)) := by
    apply List.filter_congr; intro x _; simp [hQ]
  rw [this, ← List.toFinset_card_of_nodup ((List.nodup_finRange 22).filter _), List.toFinset_filter,
    List.toFinset_finRange]
  simp

theorem bne_fv (x : Fin 22) {u : Nat} (h1 : 1 ≤ u) (h2 : u ≤ 22) :
    (x.val + 1 != u) = decide (x ≠ fv u) := by
  by_cases hx : x = fv u
  · subst hx; rw [fv_val h1 h2]; simp; omega
  · have : x.val + 1 ≠ u := fun h => hx (by apply Fin.ext; rw [fv_val h1 h2]; omega)
    simp [this, hx]

theorem colOf_succ_right (a : EColouring 22 2) (x : Fin 22) {u : Nat} (h1 : 1 ≤ u) (h2 : u ≤ 22) :
    colOf a u (x.val + 1) = (kOf a).C (fv u) x := by
  rw [colOf_eq_kOf a h1 h2 (by omega) (by have := x.isLt; omega), fv_succ]

/-- The `kOf` colouring's codegrees are the encoder's list counts. -/
theorem Cb_eq (a : EColouring 22 2) {i j : Nat} (hi1 : 1 ≤ i) (hi2 : i ≤ 22) (hj1 : 1 ≤ j) (hj2 : j ≤ 22) :
    Cb (colOf a) i j = ((kOf a).blueCodeg (fv i) (fv j)).card := by
  unfold Cb cbList Colouring.blueCodeg
  apply count_fin
  intro x
  rw [bne_fv x hi1 hi2, bne_fv x hj1 hj2, colOf_succ_right a x hi1 hi2, colOf_succ_right a x hj1 hj2]
  simp [Bool.and_assoc]

theorem Cr_eq (a : EColouring 22 2) {i j : Nat} (hi1 : 1 ≤ i) (hi2 : i ≤ 22) (hj1 : 1 ≤ j) (hj2 : j ≤ 22) :
    Cr (colOf a) i j = ((kOf a).redCodeg (fv i) (fv j)).card := by
  unfold Cr crList Colouring.redCodeg
  apply count_fin
  intro x
  rw [bne_fv x hi1 hi2, bne_fv x hj1 hj2, colOf_succ_right a x hi1 hi2, colOf_succ_right a x hj1 hj2]
  simp [Bool.and_assoc]

theorem blueUpTo_eq (a : EColouring 22 2) {v : Nat} (h1 : 1 ≤ v) (h2 : v ≤ 22) :
    (blueUpTo (colOf a) v 22).length = ((kOf a).blueNbr (fv v)).card := by
  unfold blueUpTo Colouring.blueNbr
  apply count_fin
  intro x
  rw [bne_fv x h1 h2, colOf_succ_right a x h1 h2]
  simp

/-! ## The interface -/

/-- A permutation fixing every vertex outside the N-cells, sending each N-cell vertex into a cell
containing it, and sending every edge of `Hs` into `Hs` (encoder vertex numbering via `τN`). -/
def CellAut (τ : Equiv.Perm (Fin 22)) (cells : Cells) (Hs : Array (Nat × Nat)) : Prop :=
  (∀ x : Fin 22, x.val + 1 ∉ cellVerts (nCellArrays cells) → τ x = x) ∧
  (∀ x : Fin 22, x.val + 1 ∈ cellVerts (nCellArrays cells) →
    ∃ c ∈ nCellArrays cells, x.val + 1 ∈ c ∧ (τ x).val + 1 ∈ c) ∧
  (∀ e ∈ Hs, Hs.contains (srt (τN τ e.1) (τN τ e.2)) = true)

/-- **The canonical rooted form** a cube's clauses assume (see the module docstring). -/
structure RootedCanon (a : EColouring 22 2) (k : Nat) (cells : Cells) (Hs : Array (Nat × Nat))
    (o : Opts) : Prop where
  row1 : ∀ u : Fin 22, (h : (0 : Fin 22) ≠ u) → (a (mkEdge 0 u h) = 1 ↔ u.val ≤ k)
  deg : ∀ v : Fin 22, deg a 1 v = cells.D[v.val]!
  hunits : ∀ x y : Fin 22, (h : x ≠ y) → 1 ≤ x.val → 1 ≤ y.val → x.val ≤ k → y.val ≤ k →
    (a (mkEdge x y h) = 1 ↔ Hs.contains (srt (x.val + 1) (y.val + 1)) = true)
  wlex : ∀ c ∈ cells.wcells, ∀ v, c.1 ≤ v → v < c.2.1 →
    lexView a ≤ lexView (actV (Equiv.swap (fv v) (fv (v + 1))) a)
  wall : o.wallpairs = true → ∀ c ∈ cells.wcells, ∀ p q, c.1 ≤ p → p < q → q ≤ c.2.1 →
    lexView a ≤ lexView (actV (Equiv.swap (fv p) (fv q)) a)
  auth : o.auth = true → ∀ τ : Equiv.Perm (Fin 22), CellAut τ cells Hs →
    lexView a ≤ lexView (actV τ a)

/-- What the bridge needs of the cube data itself (decidable for each concrete cube). -/
structure CubeWF (cells : Cells) : Prop where
  wcellsIn : ∀ c ∈ cells.wcells, 1 ≤ c.1 ∧ c.2.1 ≤ 22
  ncellsIn : ∀ v ∈ cellVerts (nCellArrays cells), 1 ≤ v ∧ v ≤ 22
  ncellsNodup : (cellVerts (nCellArrays cells)).Nodup

/-! ## From `RootedCanon` to the core premises -/

theorem beq_fv (x : Fin 22) {u : Nat} (h1 : 1 ≤ u) (h2 : u ≤ 22) :
    (x.val + 1 == u) = decide (x = fv u) := by
  have := bne_fv x h1 h2
  rw [bne] at this
  cases h : (x.val + 1 == u) <;> rw [h] at this <;> simp_all

theorem fv_inj {u w : Nat} (hu1 : 1 ≤ u) (hu2 : u ≤ 22) (hw1 : 1 ≤ w) (hw2 : w ≤ 22) (h : fv u = fv w) :
    u = w := by
  have := congrArg Fin.val h; rw [fv_val hu1 hu2, fv_val hw1 hw2] at this; omega

theorem τN_swap {p q : Nat} (hp1 : 1 ≤ p) (hp2 : p ≤ 22) (hq1 : 1 ≤ q) (hq2 : q ≤ 22) :
    τN (Equiv.swap (fv p) (fv q)) = swapF p q := by
  funext u
  unfold τN swapF
  by_cases hu : 1 ≤ u ∧ u ≤ 22
  · rw [if_pos hu, Equiv.swap_apply_def]
    by_cases h1 : u = p
    · subst h1; simp [fv_val hp1 hp2, fv_val hq1 hq2]; omega
    · have h1' : fv u ≠ fv p := fun h => h1 (fv_inj hu.1 hu.2 hp1 hp2 h)
      by_cases h2 : u = q
      · subst h2; simp [h1', fv_val hp1 hp2, fv_val hq1 hq2, h1]; omega
      · have h2' : fv u ≠ fv q := fun h => h2 (fv_inj hu.1 hu.2 hq1 hq2 h)
        simp [h1', h2', h1, h2, fv_val hu.1 hu.2]; omega
  · rw [if_neg hu]
    have h1 : u ≠ p := by omega
    have h2 : u ≠ q := by omega
    simp [h1, h2]

theorem ivVals_eq (L1 L2 di dj : Int) (tight : Bool) (act : Nat) (hact : act = 0 ∨ act = 1) :
    ivVals 22 4 7 L1 L2 di dj tight act =
      if tight then tightPy 22 4 7 di dj act L1 L2 else boundsPy 22 4 7 di dj act := by
  rcases hact with rfl | rfl <;> cases tight <;> simp [ivVals, tightPy, boundsPy, bounds]

theorem budgetOf_eq (d : Int) : LRATCatcher.Rooted.budgetOf 22 4 7 d = _root_.budgetOf 22 4 7 d := rfl

theorem count_range' (g : Nat → Bool) (m : Nat) :
    ((List.range' 1 m).filter g).length = ((Finset.Icc 1 m).filter (fun l => g l = true)).card := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_range' ..).filter _), List.toFinset_filter]
  congr 1
  ext l; simp [List.mem_range'_1]; omega

theorem filter_id_flatMap {α : Type*} (L : List α) (f : α → List Bool) :
    ((L.flatMap f).filter id).length = (L.map (fun u => ((f u).filter id).length)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.filter_append, ih]

theorem sum_range'_ne (v : Nat) (hv1 : 1 ≤ v) (hv2 : v ≤ 22) (F : Nat → Nat) :
    (((List.range' 1 22).filter (fun u => u != v)).map F).sum =
      ∑ x ∈ univ.erase (fv v), F (x.val + 1) := by
  rw [range'_eq_map_finRange, List.filter_map, List.map_map]
  rw [← List.sum_toFinset _ ((List.nodup_finRange 22).filter _), List.toFinset_filter, List.toFinset_finRange]
  rw [← Finset.filter_ne' univ (fv v)]
  apply Finset.sum_congr
  · ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
    rw [bne_fv x hv1 hv2]; simp
  · intro x _; rfl

theorem Cr_srt (a : EColouring 22 2) {u w : Nat} (hu1 : 1 ≤ u) (hu2 : u ≤ 22) (hw1 : 1 ≤ w)
    (hw2 : w ≤ 22) :
    (Cr (colOf a) (srt u w).1 (srt u w).2 : Int) = (kOf a).cR (fv u) (fv w) := by
  unfold srt
  split
  · rw [Cr_eq a hu1 hu2 hw1 hw2]; rfl
  · rw [Cr_eq a hw1 hw2 hu1 hu2, (kOf a).cR_symm]; rfl

theorem Cb_srt (a : EColouring 22 2) {u w : Nat} (hu1 : 1 ≤ u) (hu2 : u ≤ 22) (hw1 : 1 ≤ w)
    (hw2 : w ≤ 22) :
    (Cb (colOf a) (srt u w).1 (srt u w).2 : Int) = (kOf a).cB (fv u) (fv w) := by
  unfold srt
  split
  · rw [Cb_eq a hu1 hu2 hw1 hw2]; rfl
  · rw [Cb_eq a hw1 hw2 hu1 hu2, (kOf a).cB_symm]; rfl

theorem thrE_eq (a : EColouring 22 2) {v : Nat} (h1 : 1 ≤ v) (h2 : v ≤ 22) (x : Fin 22) (l : Nat) :
    thrE (colOf a) (x.val + 1) v l = decide ((kOf a).thresholdE (4 : ℕ) (7 : ℕ) (fv v) x l) := by
  have hx := x.isLt
  unfold thrE Colouring.thresholdE
  rw [Cr_srt a (by omega) (by omega) h1 h2, Cb_srt a (by omega) (by omega) h1 h2, fv_succ,
    colOf_symm a, colOf_succ_right a x h1 h2, (kOf a).cR_symm x, (kOf a).cB_symm x]
  by_cases hc : (kOf a).C (fv v) x = true <;> simp [hc]

theorem coreCanonL_of (a : EColouring 22 2) (hred : NoKst a 0 2 8) (hblue : NoKst a 1 2 5)
    (k : Nat) (cells : Cells) (Hs : Array (Nat × Nat)) (o : Opts)
    (hcan : RootedCanon a k cells Hs o) (hwf : CubeWF cells) (hsf : o.shortfall = false) :
    CoreCanonL (colOf a) k cells Hs o := by
  have hG : (kOf a).Good 4 7 :=
    Colouring.good_of_NoKst (kOf a) (by rw [toE_kOf]; exact hblue) (by rw [toE_kOf]; exact hred)
  have hdeg : ∀ v, 1 ≤ v → v ≤ 22 → ((kOf a).blueNbr (fv v)).card = cells.D[v - 1]! := by
    intro v h1 h2
    have h := hcan.deg (fv v)
    rw [← toE_kOf a, Colouring.deg_toE_one, fv_val h1 h2] at h
    exact h
  have hdg : ∀ v, 1 ≤ v → v ≤ 22 → (kOf a).dg (fv v) = ((cells.D[v - 1]! : Nat) : Int) := by
    intro v h1 h2; unfold Colouring.dg; rw [hdeg v h1 h2]
  refine
    { symm := colOf_symm a
      row1 := ?_, hunits := ?_, deg := ?_, iv := ?_, chan := ?_, bud := ?_, capR := ?_, capB := ?_
      wcellsIn := hwf.wcellsIn, wlex := ?_, wall := ?_, ncellsIn := hwf.ncellsIn
      ncellsNodup := hwf.ncellsNodup, auth := ?_, noShortfall := hsf }
  · -- row 1
    intro u h1 h2
    rw [colOf_eq_kOf a (by omega) (by omega) (by omega) h2, kOf_C]
    have h0 : fv 1 = 0 := rfl
    have hne : (0 : Fin 22) ≠ fv u := by
      intro h; have := congrArg Fin.val h; rw [fv_val (by omega) h2] at this; simp at this; omega
    rw [h0, dif_neg hne]
    have := hcan.row1 (fv u) hne
    rw [fv_val (by omega) h2] at this
    by_cases hb : a (mkEdge 0 (fv u) hne) = 1
    · simp [hb]; omega
    · simp [hb]; omega
  · -- the H units
    intro i j hi hij hj hi2 hjk
    rw [colOf_eq_kOf a hi (by omega) (by omega) hj, kOf_C]
    have hne : fv i ≠ fv j := fun h => by have := fv_inj hi (by omega) (by omega) hj h; omega
    rw [dif_neg hne]
    have := hcan.hunits (fv i) (fv j) hne (by rw [fv_val hi (by omega)]; omega)
      (by rw [fv_val (by omega) hj]; omega) (by rw [fv_val hi (by omega)]; omega)
      (by rw [fv_val (by omega) hj]; omega)
    rw [fv_val hi (by omega), fv_val (by omega) hj, Nat.sub_add_cancel hi,
      Nat.sub_add_cancel (by omega : 1 ≤ j)] at this
    have hs : srt i j = (i, j) := by simp [srt]; omega
    rw [hs] at this
    by_cases hb : a (mkEdge (fv i) (fv j) hne) = 1
    · simp only [hb, decide_true]; exact (this.mp hb).symm
    · simp only [hb, decide_false]
      cases hc : Hs.contains (i, j)
      · rfl
      · exact absurd (this.mpr hc) hb
  · -- degrees
    intro v h1 h2
    rw [blueUpTo_eq a h1 h2, hdeg v h1 h2]
  · -- intervals
    intro i j hi hij hj
    have hne : fv i ≠ fv j := fun h => by have := fv_inj hi (by omega) (by omega) hj h; omega
    have hCb : (Cb (colOf a) i j : Int) = (kOf a).cB (fv i) (fv j) := by
      unfold Colouring.cB; rw [Cb_eq a hi (by omega) (by omega) hj]
    have hCr : (Cr (colOf a) i j : Int) = (kOf a).cR (fv i) (fv j) := by
      unfold Colouring.cR; rw [Cr_eq a hi (by omega) (by omega) hj]
    have hcol : colOf a i j = (kOf a).C (fv i) (fv j) := colOf_eq_kOf a hi (by omega) (by omega) hj
    have hact : (((if colOf a i j then 1 else 0 : Nat)) : Int) = (kOf a).Aij (fv i) (fv j) := by
      unfold Colouring.Aij; rw [hcol]; split <;> simp
    have hl1 : lamD cells.D i = _root_.budgetOf 22 4 7 ((kOf a).dg (fv i)) := by
      unfold lamD; rw [hdg i hi (by omega)]; rfl
    have hl2 : lamD cells.D j = _root_.budgetOf 22 4 7 ((kOf a).dg (fv j)) := by
      unfold lamD; rw [hdg j (by omega) hj]; rfl
    simp only
    rw [ivVals_eq _ _ _ _ _ _ (by split <;> simp), hl1, hl2, hact, ← hdg i hi (by omega),
      ← hdg j (by omega) hj, hCb, hCr]
    cases o.tight
    · simpa using (kOf a).bounds_sound hG hne
    · simpa using (kOf a).tight_sound hG hne
  · -- channel
    intro _ i j hi hij hj
    have hne : fv i ≠ fv j := fun h => by have := fv_inj hi (by omega) (by omega) hj h; omega
    have hid := (kOf a).complement_identity hne
    have hcol : colOf a i j = (kOf a).C (fv i) (fv j) := colOf_eq_kOf a hi (by omega) (by omega) hj
    have hCb : (Cb (colOf a) i j : Int) = (kOf a).cB (fv i) (fv j) := by
      unfold Colouring.cB; rw [Cb_eq a hi (by omega) (by omega) hj]
    have hCr : (Cr (colOf a) i j : Int) = (kOf a).cR (fv i) (fv j) := by
      unfold Colouring.cR; rw [Cr_eq a hi (by omega) (by omega) hj]
    refine ⟨?_, ?_⟩
    · rw [hCb, hCr, hid, ← hdg i hi (by omega), ← hdg j (by omega) hj, hcol]
      unfold Colouring.Aij
      split <;> simp
    · rw [Cr_eq a hi (by omega) (by omega) hj]; exact hG.2 _ _ hne
  · -- budget
    intro _ v h1 h2
    have hlam : lamD cells.D v = _root_.budgetOf 22 4 7 ((kOf a).dg (fv v)) := by
      unfold lamD; rw [hdg v h1 h2]; rfl
    have hnn : 0 ≤ lamD cells.D v := by rw [hlam]; exact (kOf a).budget_nonneg hG (fv v)
    refine ⟨hnn, ?_⟩
    have hts := (kOf a).threshold_sum hG (fv v)
    simp only at hts
    have hlam' : _root_.budgetOf ((22 : ℕ) : ℤ) ((4 : ℕ) : ℤ) ((7 : ℕ) : ℤ) ((kOf a).dg (fv v)) =
        lamD cells.D v := by rw [hlam]; rfl
    rw [hlam'] at hts
    have htop : topOf cells.D v = min (lamD cells.D v).toNat (max 7 4) := by
      unfold topOf; omega
    -- the list count as a double sum
    have hcount : ((budList (colOf a) cells.D v 22).filter id).length =
        ∑ x ∈ univ.erase (fv v), ((Finset.Icc 1 (topOf cells.D v)).filter
          (fun l => (kOf a).thresholdE (4 : ℕ) (7 : ℕ) (fv v) x l)).card := by
      unfold budList
      rw [filter_id_flatMap, sum_range'_ne v h1 h2]
      apply Finset.sum_congr rfl
      intro x _
      rw [List.filter_map, List.length_map, count_range']
      congr 1
      apply Finset.filter_congr
      intro l _
      simp [Function.comp, thrE_eq a h1 h2 x l]
    have hz : (((budList (colOf a) cells.D v 22).filter id).length : Int) = lamD cells.D v := by
      rw [hcount, ← hts, htop]
      push_cast
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_boole]
    omega
  · -- red caps of the base layer
    intro _ u v hu huv hv
    have hne : fv u ≠ fv v := fun h => by have := fv_inj hu (by omega) (by omega) hv h; omega
    have : (commonC (colOf a) 1 [u, v] 22).length = ((kOf a).redCodeg (fv u) (fv v)).card := by
      unfold commonC Colouring.redCodeg
      apply count_fin
      intro x
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, List.all_cons, List.all_nil,
        Bool.and_true, colV, show (1 : Nat) ≠ 2 by decide, if_false]
      rw [beq_fv x hu (by omega), beq_fv x (by omega) hv,
        colOf_succ_right a x hu (by omega), colOf_succ_right a x (by omega) hv]
      simp [Bool.and_assoc]
    rw [this]; exact hG.2 _ _ hne
  · -- blue caps of the base layer
    intro _ u v hu huv hv
    have hne : fv u ≠ fv v := fun h => by have := fv_inj hu (by omega) (by omega) hv h; omega
    have : (commonC (colOf a) 2 [u, v] 22).length = ((kOf a).blueCodeg (fv u) (fv v)).card := by
      unfold commonC Colouring.blueCodeg
      apply count_fin
      intro x
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, List.all_cons, List.all_nil,
        Bool.and_true, colV, if_true]
      rw [beq_fv x hu (by omega), beq_fv x (by omega) hv,
        colOf_succ_right a x hu (by omega), colOf_succ_right a x (by omega) hv]
      simp [Bool.and_assoc]
    rw [this]; exact hG.1 _ _ hne
  · -- W-adjacent transpositions
    intro c hc v h1 h2
    have hin := hwf.wcellsIn c hc
    rw [← τN_swap (by omega) (by omega) (by omega) (by omega)]
    exact lexLeE_of_lexView a _ (hcan.wlex c hc v h1 h2)
  · -- all W transpositions
    intro hw c hc p q h1 h2 h3
    have hin := hwf.wcellsIn c hc
    rw [← τN_swap (by omega) (by omega) (by omega) (by omega)]
    exact lexLeE_of_lexView a _ (hcan.wall hw c hc p q h1 h2 h3)
  · -- H-automorphisms
    intro ha asg hasg
    obtain ⟨hcell, hoff, hinj, hHs⟩ := autos_img _ _ hwf.ncellsNodup asg hasg
    have hrange : ∀ u, 1 ≤ u → u ≤ 22 → 1 ≤ imgA asg u ∧ imgA asg u ≤ 22 := by
      intro u h1 h2
      by_cases hv : u ∈ cellVerts (nCellArrays cells)
      · obtain ⟨c, hc, hvc, hic⟩ := hcell u hv
        exact hwf.ncellsIn _ (mem_cellVerts.mpr ⟨c, hc, hic⟩)
      · rw [hoff u hv]; exact ⟨h1, h2⟩
    let f : Fin 22 → Fin 22 := fun x => fv (imgA asg (x.val + 1))
    have hfval : ∀ x : Fin 22, (f x).val + 1 = imgA asg (x.val + 1) := by
      intro x
      have := hrange (x.val + 1) (by omega) (by have := x.isLt; omega)
      show (fv _).val + 1 = _
      rw [fv_val this.1 this.2]; omega
    have hfinj : Function.Injective f := by
      intro x y hxy
      have h := congrArg (fun z : Fin 22 => z.val + 1) hxy
      simp only [hfval] at h
      have := hinj _ _ h
      apply Fin.ext; omega
    let τ := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
    have hτ : ∀ x, τ x = f x := fun x => rfl
    have hτN : τN τ = imgA asg := by
      funext u
      unfold τN
      by_cases hu : 1 ≤ u ∧ u ≤ 22
      · rw [if_pos hu, hτ, hfval, fv_val hu.1 hu.2, Nat.sub_add_cancel hu.1]
      · rw [if_neg hu]
        have : u ∉ cellVerts (nCellArrays cells) := fun h => hu (hwf.ncellsIn u h)
        rw [hoff u this]
    have hca : CellAut τ cells Hs := by
      refine ⟨fun x hx => ?_, fun x hx => ?_, fun e he => ?_⟩
      · rw [hτ]; apply Fin.ext; have := hfval x; rw [hoff _ hx] at this; omega
      · obtain ⟨c, hc, h1, h2⟩ := hcell _ hx
        exact ⟨c, hc, h1, by rw [hτ, hfval]; exact h2⟩
      · rw [hτN]; exact hHs e he
    have := lexLeE_of_lexView a τ (hcan.auth ha τ hca)
    rwa [hτN] at this

/-! ## The bridge -/

/-- **The soundness bridge.** A good 2-colouring of `K_22` (no red `K_{2,8}`, no blue `K_{2,5}`)
in the canonical rooted form of a well-formed cube satisfies every clause `rootedFormula` emits
for that cube, under any option set without `shortfall` (O1, O2, O3 included). -/
theorem rooted_bridge (degs : List Nat) (k : Nat) (comp H : List (Nat × Nat)) (o : Opts)
    (F : Formula) (hF : rootedFormula 22 ["K2x8", "K2x5"] degs k comp H o = .ok F)
    (cells : Cells) (hcells : cellsOf 22 degs k comp = .ok cells) (hwf : CubeWF cells)
    (hsf : o.shortfall = false) (a : EColouring 22 2) (hred : NoKst a 0 2 8)
    (hblue : NoKst a 1 2 5) (hcan : RootedCanon a k cells (normH H) o) :
    ∃ σ, ClsSat σ F.clauses :=
  rootedFormula_sat_coreL degs k comp H o F hF cells hcells (colOf a)
    (coreCanonL_of a hred hblue k cells (normH H) o hcan hwf hsf)

/-- The DIMACS view of an encoder formula (the clause body `writeDimacs` prints). -/
def fCNF (F : Formula) : Std.Sat.CNF Nat := SB.BipBridge.toCNFV (F.clauses.toList.map Array.toList)

theorem not_clsSat_of_unsat (F : Formula) (hU : (fCNF F).Unsat) : ∀ σ, ¬ ClsSat σ F.clauses := by
  intro σ hσ
  refine SB.BipBridge.not_listSat_of_toCNFV_unsat _ hU σ ?_
  intro c hc
  simp only [List.mem_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  obtain ⟨l, hl, hs⟩ := hσ c' (by simpa using hc')
  exact ⟨l, by simpa using hl, hs⟩

/-- **`CNF.Unsat` of the printed cube refutes every good colouring in its canonical form.** -/
theorem no_canon_of_unsat (degs : List Nat) (k : Nat) (comp H : List (Nat × Nat)) (o : Opts)
    (F : Formula) (hF : rootedFormula 22 ["K2x8", "K2x5"] degs k comp H o = .ok F)
    (cells : Cells) (hcells : cellsOf 22 degs k comp = .ok cells) (hwf : CubeWF cells)
    (hsf : o.shortfall = false) (hU : (fCNF F).Unsat) :
    ¬ ∃ a : EColouring 22 2, NoKst a 0 2 8 ∧ NoKst a 1 2 5 ∧ RootedCanon a k cells (normH H) o := by
  rintro ⟨a, hred, hblue, hcan⟩
  obtain ⟨σ, hσ⟩ := rooted_bridge degs k comp H o F hF cells hcells hwf hsf a hred hblue hcan
  exact not_clsSat_of_unsat F hU σ hσ

/-- **Split parents.** If the children (`F` plus the units of each leaf of a complete split,
`coversB`) are all `CNF.Unsat`, no good colouring is in the parent cube's canonical form. -/
theorem no_canon_of_children_unsat (degs : List Nat) (k : Nat) (comp H : List (Nat × Nat))
    (o : Opts) (F : Formula) (hF : rootedFormula 22 ["K2x8", "K2x5"] degs k comp H o = .ok F)
    (cells : Cells) (hcells : cellsOf 22 degs k comp = .ok cells) (hwf : CubeWF cells)
    (hsf : o.shortfall = false) (tag : String) (us : List (List Int)) (n : Nat)
    (hcov : coversB n us = true) (hU : ∀ u ∈ us, (fCNF (splitChild F tag u)).Unsat) :
    ¬ ∃ a : EColouring 22 2, NoKst a 0 2 8 ∧ NoKst a 1 2 5 ∧ RootedCanon a k cells (normH H) o := by
  rintro ⟨a, hred, hblue, hcan⟩
  obtain ⟨σ, hσ⟩ := rooted_bridge degs k comp H o F hF cells hcells hwf hsf a hred hblue hcan
  exact split_unsat F tag us n hcov (fun u hu σ' => not_clsSat_of_unsat _ (hU u hu) σ') σ hσ

end SB.Rooted

#print axioms SB.Rooted.lexLeE_of_lexView
#print axioms SB.Rooted.coreCanonL_of
#print axioms SB.Rooted.rooted_bridge
#print axioms SB.Rooted.no_canon_of_unsat
#print axioms SB.Rooted.no_canon_of_children_unsat
