/-
# The bridge: from `EncodeSoundFor` to a model of `encodeBip`

`SB.Portfolio.EncodeSoundFor n s₀ t₀ s₁ t₁` ends with a colouring `a` that avoids both
patterns, is a lex-leader under every vertex relabelling, and whose truthful Sinz
registers satisfy `Sinz.Clauses` for every `s`-set. `SB.Encoder.encodeBip` (vendored
verbatim from the n=19 deposit) is the DIMACS clause list the search refuted. This module
builds an assignment `σ : ℕ → Bool` of ALL variables of `encodeBip` from `a` and proves
every clause satisfied — so an UNSAT verdict on `encodeBip` refutes every good colouring.

Conventions (each pinned by a lemma below, none by comment alone):
* vertices: encoder `1..n` (`verts n = range' 1 n`), sbsound `Fin n`; `ofEdge` sends the
  sbsound edge `(i, j)` (`i < j`) to the encoder pair `(i+1, j+1)`;
* colours: encoder `c ∈ {1, 2}`, sbsound `Fin 2`; `evarNum n e c = var n 2 (ofEdge e) (c+1)`,
  so encoder colour 1 = sbsound colour 0 = the colour of `codegreeColour … 1 s₀ t₀` = the
  colour in which `NoKst a 0 s₀ t₀` forbids `K_{s₀,t₀}` (`K_{3,4}` for the cell);
* the `s`-set order is `combos s (verts n)` (itertools order) and the `w` order inside a
  set is ascending (`wsOf`); neither order matters for satisfaction, only the numbering;
* Sinz registers: encoder `R(i,j)` (`i = 1..m-1`, `j = 1..k`, number
  `regBase + (i-1)k + j`) is read as sbsound's truthful register at input position
  `ws[i-1]` and level `j-1`: "at least `j` of the first `i` candidate neighbours";
* vertex-lex: encoder transposition `v ∈ 1..n-1` is `vswap n (v-1)`; the `q`/chain
  variable at moved-position `t` is `nv+2t+1` / `nv+2t+2`; the comparison clause forbids
  `val(e) = 2 ∧ val(f) = 1`, i.e. demands `a e ≤ a (τ e)` at the first difference, which is
  `lexView a ≤ lexView (actV τ a)`.

Literal semantics: a DIMACS literal `l` is true under `σ` iff `l ≠ 0` and `σ |l| = (l > 0)`
(variables 1-based, as in the file). Requiring `l ≠ 0` of the witnessing literal is what
makes the Stage-D transfer through `dimacsLit` (`l ↦ (|l|-1, l>0)`) a pure unfolding.
-/
import Mathlib
import Std.Sat.CNF
import Sbsound.EncoderVendored
import Sbsound.SBClauses
import Sbsound.CodegreeEncode
import Sbsound.Portfolio

namespace SB.BipBridge

open SB SB.Encoder

/-! ### Satisfaction of DIMACS clause lists -/

/-- Literal `l` is true under `σ` (1-based variables): `l ≠ 0` and `σ |l| = (0 < l)`. -/
def LitSat (σ : ℕ → Bool) (l : ℤ) : Prop := l ≠ 0 ∧ σ l.natAbs = decide (0 < l)

instance (σ : ℕ → Bool) (l : ℤ) : Decidable (LitSat σ l) :=
  inferInstanceAs (Decidable (l ≠ 0 ∧ σ l.natAbs = decide (0 < l)))

/-- A clause is satisfied when some literal is true. -/
def ClauseSat (σ : ℕ → Bool) (c : List ℤ) : Prop := ∃ l ∈ c, LitSat σ l

instance (σ : ℕ → Bool) (c : List ℤ) : Decidable (ClauseSat σ c) :=
  inferInstanceAs (Decidable (∃ l ∈ c, LitSat σ l))

/-- A clause list is satisfied when every clause is. -/
def ListSat (σ : ℕ → Bool) (cs : List (List ℤ)) : Prop := ∀ c ∈ cs, ClauseSat σ c

instance (σ : ℕ → Bool) (cs : List (List ℤ)) : Decidable (ListSat σ cs) :=
  inferInstanceAs (Decidable (∀ c ∈ cs, ClauseSat σ c))

/-! ### Edges and edge variables -/

variable {n : ℕ}

/-- The encoder's 1-based pair of an sbsound edge. -/
def ofEdge (e : Edge n) : ℕ × ℕ := ((ofLex e.val).1.val + 1, (ofLex e.val).2.val + 1)

/-- The DIMACS variable of edge `e` in sbsound colour `c` (encoder colour `c+1`). -/
def evarNum (n : ℕ) (e : Edge n) (c : Fin 2) : ℕ :=
  var n 2 (ofEdge e).1 (ofEdge e).2 (c.val + 1)

/-- The edge-variable part of the assignment: `evarNum n e c ↦ decide (a e = c)`,
defined by search so that no closed-form inverse of `edgeIdx` is needed. -/
def edgeAssign (a : EColouring n 2) : ℕ → Bool :=
  fun x => decide (∃ e : Edge n, ∃ c : Fin 2, evarNum n e c = x ∧ a e = c)

/-! ### Extending an assignment above a variable count -/

/-- `extend σ nv vals` agrees with `σ` on `x ≤ nv` and with `vals` above. -/
def extend (σ : ℕ → Bool) (nv : ℕ) (vals : ℕ → Bool) : ℕ → Bool :=
  fun x => if x ≤ nv then σ x else vals x

/-! ### The codegree block of one `s`-set -/

/-- The sbsound `s`-set of an encoder `s`-set (a list of 1-based vertices). -/
def SF (n : ℕ) (S : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => (v.val + 1) ∈ S

/-- The candidate common neighbours, ascending — literally the encoder's `ws`. -/
def wsOf (n : ℕ) (S : List ℕ) : List ℕ := (verts n).filter (fun w => !S.contains w)

/-- 1-based vertex to `Fin n`. -/
def finOf (n : ℕ) (w : ℕ) : Option (Fin n) := if h : w - 1 < n then some ⟨w - 1, h⟩ else none

/-- Values of the `y` and register variables of the block for `S` allocated after `nv`:
`y_i` (number `nv+i`) is the codegree input at `ws[i-1]`; `R(i,j)` (number
`nv+m+(i-1)k+j`) is the truthful register at input `ws[i-1]`, level `j-1`. -/
def blockVals (a : EColouring n 2) (c : Fin 2) (k : ℕ) (S : List ℕ) (nv : ℕ) : ℕ → Bool :=
  let ws := wsOf n S
  let m := ws.length
  let y : Fin n → Bool := codegreeInputs a c (SF n S)
  let R : Fin n → Fin k → Bool := Sinz.truthful (k := k) y
  fun x =>
    if x ≤ nv + m then
      match finOf n (ws.getD (x - nv - 1) 0) with
      | some w => y w
      | none => false
    else
      let d := x - nv - m - 1
      match finOf n (ws.getD (d / k) 0) with
      | some w => if hj : d % k < k then R w ⟨d % k, hj⟩ else false
      | none => false

/-- The variable count after the block of `S` (mirrors `nv2` in `codegreeColour`). -/
def cgStepNv (n k : ℕ) (S : List ℕ) (nv : ℕ) : ℕ :=
  let m := (wsOf n S).length
  nv + m + (m - 1) * k

/-- The assignment after all blocks of one colour, threading the count like the encoder. -/
def codegreeAssign (a : EColouring n 2) (c : Fin 2) (s t : ℕ) (σ₀ : ℕ → Bool) (nv₀ : ℕ) :
    (ℕ → Bool) × ℕ :=
  (combos s (verts n)).foldl
    (fun acc S => (extend acc.1 acc.2 (blockVals a c (t - 1) S acc.2), cgStepNv n (t - 1) S acc.2))
    (σ₀, nv₀)

/-! ### The vertex-lex block of one transposition -/

/-- Values of the `q`/chain variables of transposition `v` allocated after `nv`: position
`t` has `q_t = nv+2t+1`, `ch_t = nv+2t+2`, read from sbsound's `canonAssign`. -/
def lexVals (a : EColouring n 2) (v : ℕ) (nv : ℕ) : ℕ → Bool := fun x =>
  let d := x - nv - 1
  if d % 2 = 0 then canonAssign a [] (qvar (v - 1) (d / 2) : SVar n 2)
  else canonAssign a [] (chvar (v - 1) (d / 2) : SVar n 2)

/-- The assignment after all transpositions `1..n-1`, threading the count via the
encoder's own `lexTransposition`. -/
def lexAssign (a : EColouring n 2) (σ₀ : ℕ → Bool) (nv₀ : ℕ) : (ℕ → Bool) × ℕ :=
  (List.range' 1 (n - 1)).foldl
    (fun acc v => (extend acc.1 acc.2 (lexVals a v acc.2), (lexTransposition n 2 v acc.2).2))
    (σ₀, nv₀)

/-! ### The whole assignment -/

/-- The model of `encodeBip n s₀ t₀ s₁ t₁` built from a colouring `a`: edge variables from
`a`, then the colour-1 (sbsound 0) blocks, the colour-2 (sbsound 1) blocks, the lex blocks,
allocated in the encoder's order. -/
def bridgeAssign (a : EColouring n 2) (s₀ t₀ s₁ t₁ : ℕ) : ℕ → Bool :=
  let E := n * (n - 1) / 2
  let m1 := codegreeAssign a 0 s₀ t₀ (edgeAssign a) (E * 2)
  let m2 := codegreeAssign a 1 s₁ t₁ m1.1 m1.2
  (lexAssign a m2.1 m2.2).1


/-! ## Proofs

### Satisfaction algebra -/

section Sat
variable {σ σ' : ℕ → Bool}

lemma litSat_pos {x : ℕ} (hx : 0 < x) : LitSat σ (x : ℤ) ↔ σ x = true := by
  unfold LitSat
  have h0 : x ≠ 0 := by omega
  simp [h0, hx]

lemma litSat_neg {x : ℕ} (hx : 0 < x) : LitSat σ (-(x : ℤ)) ↔ σ x = false := by
  unfold LitSat
  have h0 : x ≠ 0 := by omega
  have h2 : ¬ ((x : ℤ) < 0) := not_lt.mpr (Int.natCast_nonneg x)
  simp [h0, h2]

lemma clauseSat_of_mem {c : List ℤ} {l : ℤ} (hl : l ∈ c) (h : LitSat σ l) : ClauseSat σ c :=
  ⟨l, hl, h⟩

lemma listSat_nil : ListSat σ [] := by simp [ListSat]

lemma listSat_cons {c : List ℤ} {cs : List (List ℤ)} :
    ListSat σ (c :: cs) ↔ ClauseSat σ c ∧ ListSat σ cs := by simp [ListSat]

lemma listSat_singleton {c : List ℤ} : ListSat σ [c] ↔ ClauseSat σ c := by simp [ListSat]

lemma listSat_append {A B : List (List ℤ)} :
    ListSat σ (A ++ B) ↔ ListSat σ A ∧ ListSat σ B := by
  simp [ListSat, List.mem_append, or_imp, forall_and]

lemma listSat_flatMap {α : Type*} {l : List α} {f : α → List (List ℤ)} :
    ListSat σ (l.flatMap f) ↔ ∀ x ∈ l, ListSat σ (f x) := by
  simp only [ListSat, List.mem_flatMap]
  constructor
  · intro h x hx c hc; exact h c ⟨x, hx, hc⟩
  · rintro h c ⟨x, hx, hc⟩; exact h x hx c hc

lemma listSat_map {α : Type*} {l : List α} {f : α → List ℤ} :
    ListSat σ (l.map f) ↔ ∀ x ∈ l, ClauseSat σ (f x) := by
  simp [ListSat]

/-- A literal's truth depends only on its variable's value. -/
lemma litSat_congr {l : ℤ} (h : σ' l.natAbs = σ l.natAbs) : LitSat σ l → LitSat σ' l := by
  rintro ⟨h0, hv⟩; exact ⟨h0, h ▸ hv⟩

/-- Bound on the variables mentioned by a clause list. -/
def VarsLe (cs : List (List ℤ)) (nv : ℕ) : Prop := ∀ c ∈ cs, ∀ l ∈ c, l.natAbs ≤ nv

lemma varsLe_nil {nv : ℕ} : VarsLe [] nv := by simp [VarsLe]

lemma varsLe_append {A B : List (List ℤ)} {nv : ℕ} :
    VarsLe (A ++ B) nv ↔ VarsLe A nv ∧ VarsLe B nv := by
  simp [VarsLe, List.mem_append, or_imp, forall_and]

lemma varsLe_mono {cs : List (List ℤ)} {nv nv' : ℕ} (h : VarsLe cs nv) (hle : nv ≤ nv') :
    VarsLe cs nv' := fun c hc l hl => le_trans (h c hc l hl) hle

lemma varsLe_flatMap {α : Type*} {l : List α} {f : α → List (List ℤ)} {nv : ℕ} :
    VarsLe (l.flatMap f) nv ↔ ∀ x ∈ l, VarsLe (f x) nv := by
  simp only [VarsLe, List.mem_flatMap]
  constructor
  · intro h x hx c hc; exact h c ⟨x, hx, hc⟩
  · rintro h c ⟨x, hx, hc⟩; exact h x hx c hc

lemma varsLe_map {α : Type*} {l : List α} {f : α → List ℤ} {nv : ℕ} :
    VarsLe (l.map f) nv ↔ ∀ x ∈ l, ∀ l' ∈ f x, l'.natAbs ≤ nv := by
  simp [VarsLe]

/-- Satisfaction transfers to any assignment agreeing on the variables mentioned. -/
lemma listSat_of_agree {cs : List (List ℤ)} {nv : ℕ} (hs : ListSat σ cs) (hv : VarsLe cs nv)
    (ha : ∀ x ≤ nv, σ' x = σ x) : ListSat σ' cs := by
  intro c hc
  obtain ⟨l, hl, hlit⟩ := hs c hc
  exact ⟨l, hl, litSat_congr (ha _ (hv c hc l hl)) hlit⟩

@[simp] lemma extend_le {nv x : ℕ} {vals : ℕ → Bool} (h : x ≤ nv) :
    extend σ nv vals x = σ x := by simp [extend, h]

@[simp] lemma extend_gt {nv x : ℕ} {vals : ℕ → Bool} (h : nv < x) :
    extend σ nv vals x = vals x := by simp [extend, Nat.not_le.mpr h]

end Sat

/-! ### The extension fold

Both `codegreeColour` and `lexClauses` are `foldl`s that thread a variable count and
append the clauses of each item; `codegreeAssign`/`lexAssign` mirror them, extending the
assignment above the current count at each item. One lemma serves both. -/

/-- The property carried along every fold: the assignment reads the edge variables from
`a` and the count is past every edge variable. -/
def EdgeOK (a : EColouring n 2) (σ : ℕ → Bool) (nv : ℕ) : Prop :=
  n * (n - 1) / 2 * 2 ≤ nv ∧ ∀ e c, σ (evarNum n e c) = decide (a e = c)

theorem fold_extend {α : Type*} (a : EColouring n 2) (xs : List α)
    (new : α → ℕ → List (List ℤ)) (nvStep : α → ℕ → ℕ) (vals : α → ℕ → ℕ → Bool)
    (hmono : ∀ x ∈ xs, ∀ nv, nv ≤ nvStep x nv)
    (hstep : ∀ x ∈ xs, ∀ σ nv, EdgeOK a σ nv →
      ListSat (extend σ nv (vals x nv)) (new x nv) ∧ VarsLe (new x nv) (nvStep x nv))
    (hevar : ∀ e c, evarNum n e c ≤ n * (n - 1) / 2 * 2) :
    ∀ (cls₀ : List (List ℤ)) (σ₀ : ℕ → Bool) (nv₀ : ℕ), EdgeOK a σ₀ nv₀ → ListSat σ₀ cls₀ →
      VarsLe cls₀ nv₀ →
      (xs.foldl (fun acc x => (acc.1 ++ new x acc.2, nvStep x acc.2)) (cls₀, nv₀)).2 =
        (xs.foldl (fun acc x => (extend acc.1 acc.2 (vals x acc.2), nvStep x acc.2)) (σ₀, nv₀)).2 ∧
      EdgeOK a (xs.foldl (fun acc x => (extend acc.1 acc.2 (vals x acc.2), nvStep x acc.2)) (σ₀, nv₀)).1
        (xs.foldl (fun acc x => (extend acc.1 acc.2 (vals x acc.2), nvStep x acc.2)) (σ₀, nv₀)).2 ∧
      ListSat (xs.foldl (fun acc x => (extend acc.1 acc.2 (vals x acc.2), nvStep x acc.2)) (σ₀, nv₀)).1
        (xs.foldl (fun acc x => (acc.1 ++ new x acc.2, nvStep x acc.2)) (cls₀, nv₀)).1 ∧
      VarsLe (xs.foldl (fun acc x => (acc.1 ++ new x acc.2, nvStep x acc.2)) (cls₀, nv₀)).1
        (xs.foldl (fun acc x => (acc.1 ++ new x acc.2, nvStep x acc.2)) (cls₀, nv₀)).2 ∧
      nv₀ ≤ (xs.foldl (fun acc x => (acc.1 ++ new x acc.2, nvStep x acc.2)) (cls₀, nv₀)).2 ∧
      ∀ y ≤ nv₀, (xs.foldl (fun acc x => (extend acc.1 acc.2 (vals x acc.2), nvStep x acc.2)) (σ₀, nv₀)).1 y = σ₀ y := by
  induction xs with
  | nil =>
    intro cls₀ σ₀ nv₀ hP hs hv
    exact ⟨rfl, hP, hs, hv, le_refl _, fun _ _ => rfl⟩
  | cons x xs ih =>
    intro cls₀ σ₀ nv₀ hP hs hv
    simp only [List.foldl_cons]
    have hx : x ∈ x :: xs := List.mem_cons_self
    have hmono' : ∀ x ∈ xs, ∀ nv, nv ≤ nvStep x nv := fun y hy => hmono y (List.mem_cons_of_mem x hy)
    have hstep' : ∀ x ∈ xs, ∀ σ nv, EdgeOK a σ nv →
        ListSat (extend σ nv (vals x nv)) (new x nv) ∧ VarsLe (new x nv) (nvStep x nv) :=
      fun y hy => hstep y (List.mem_cons_of_mem x hy)
    have hle : nv₀ ≤ nvStep x nv₀ := hmono x hx nv₀
    obtain ⟨hsn, hvn⟩ := hstep x hx σ₀ nv₀ hP
    have hP' : EdgeOK a (extend σ₀ nv₀ (vals x nv₀)) (nvStep x nv₀) := by
      refine ⟨le_trans hP.1 hle, fun e c => ?_⟩
      rw [extend_le (le_trans (hevar e c) hP.1)]
      exact hP.2 e c
    have hs' : ListSat (extend σ₀ nv₀ (vals x nv₀)) (cls₀ ++ new x nv₀) := by
      rw [listSat_append]
      exact ⟨listSat_of_agree hs hv (fun y hy => extend_le hy), hsn⟩
    have hv' : VarsLe (cls₀ ++ new x nv₀) (nvStep x nv₀) := by
      rw [varsLe_append]
      exact ⟨varsLe_mono hv hle, hvn⟩
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih hmono' hstep' _ _ _ hP' hs' hv'
    refine ⟨h1, h2, h3, h4, le_trans hle h5, fun y hy => ?_⟩
    rw [h6 y (le_trans hy hle), extend_le hy]

/-! ### Edge indices: strict monotonicity and the bound -/

/-- The row start `edgeIdx n i (i+1)`. -/
lemma edgeIdx_row_succ {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    edgeIdx n (i + 1) (i + 2) = edgeIdx n i n + 1 := by
  unfold edgeIdx
  have hA : i * (i + 1) = (i - 1) * i + 2 * i := by
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hD : i * n = (i - 1) * n + n := by
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hB : (i - 1) * i ≤ (i - 1) * n := Nat.mul_le_mul_left _ (le_of_lt hin)
  simp only [Nat.add_sub_cancel]
  omega

lemma edgeIdx_same_row {n i j j' : ℕ} (hij : i < j) (hjj : j < j') :
    edgeIdx n i j < edgeIdx n i j' := by
  unfold edgeIdx; omega

lemma edgeIdx_same_row_le {n i j j' : ℕ} (hjj : j ≤ j') :
    edgeIdx n i j ≤ edgeIdx n i j' := by
  unfold edgeIdx; omega

/-- Row starts are monotone. -/
lemma edgeIdx_rowStart_mono {n i i' : ℕ} (hi : 1 ≤ i) (hii : i ≤ i') (hin : i' ≤ n) :
    edgeIdx n i (i + 1) ≤ edgeIdx n i' (i' + 1) := by
  induction i', hii using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih =>
    have h1 := ih (by omega)
    have h2 : edgeIdx n (m + 1) (m + 1 + 1) = edgeIdx n m n + 1 :=
      edgeIdx_row_succ (n := n) (i := m) (by omega) (by omega)
    have h3 : edgeIdx n m (m + 1) ≤ edgeIdx n m n := edgeIdx_same_row_le (by omega)
    omega

/-- Strict monotonicity in the row-major order, on valid pairs. -/
lemma edgeIdx_lt_of_lt {n i j i' j' : ℕ} (hi : 1 ≤ i) (hij : i < j) (hjn : j ≤ n)
    (hij' : i' < j') (hjn' : j' ≤ n)
    (hlt : i < i' ∨ (i = i' ∧ j < j')) : edgeIdx n i j < edgeIdx n i' j' := by
  rcases hlt with hlt | ⟨rfl, hlt⟩
  · have h1 : edgeIdx n i j ≤ edgeIdx n i n := edgeIdx_same_row_le hjn
    have h2 : edgeIdx n (i + 1) (i + 1 + 1) = edgeIdx n i n + 1 :=
      edgeIdx_row_succ (n := n) (i := i) hi (by omega)
    have h3 : edgeIdx n (i + 1) (i + 1 + 1) ≤ edgeIdx n i' (i' + 1) :=
      edgeIdx_rowStart_mono (by omega) hlt (by omega)
    have h4 : edgeIdx n i' (i' + 1) ≤ edgeIdx n i' j' := edgeIdx_same_row_le (by omega)
    omega
  · exact edgeIdx_same_row hij hlt

/-- The last row start equals `n(n-1)/2`, the number of edges. -/
lemma edgeIdx_last_row (n : ℕ) : edgeIdx n n (n + 1) = n * (n - 1) / 2 := by
  unfold edgeIdx
  have hX : (n - 1) * n = n * (n - 1) := Nat.mul_comm _ _
  have hE : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    apply Nat.two_mul_div_two_of_even
    rcases Nat.even_or_odd n with h | h
    · exact h.mul_right _
    · exact Even.mul_left (by obtain ⟨k, hk⟩ := h; exact ⟨k, by omega⟩) _
  omega

/-- Every valid edge index is below the edge count. -/
lemma edgeIdx_lt_E {n i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hjn : j ≤ n) :
    edgeIdx n i j < n * (n - 1) / 2 := by
  have h1 : edgeIdx n i j ≤ edgeIdx n i n := edgeIdx_same_row_le hjn
  have h2 : edgeIdx n (i + 1) (i + 1 + 1) = edgeIdx n i n + 1 :=
    edgeIdx_row_succ (n := n) (i := i) hi (by omega)
  have h3 : edgeIdx n (i + 1) (i + 1 + 1) ≤ edgeIdx n n (n + 1) :=
    edgeIdx_rowStart_mono (by omega) (by omega) (le_refl _)
  rw [edgeIdx_last_row] at h3
  omega

/-! ### `ofEdge` -/

lemma ofEdge_fst_pos (e : Edge n) : 1 ≤ (ofEdge e).1 := by simp [ofEdge]

lemma ofEdge_lt (e : Edge n) : (ofEdge e).1 < (ofEdge e).2 := by
  simp only [ofEdge]
  have := e.prop
  exact Nat.succ_lt_succ (Fin.lt_def.mp this)

lemma ofEdge_snd_le (e : Edge n) : (ofEdge e).2 ≤ n := by
  simp only [ofEdge]
  exact (ofLex e.val).2.isLt

lemma ofEdge_injective : Function.Injective (ofEdge (n := n)) := by
  intro e e' h
  simp only [ofEdge, Prod.mk.injEq, Nat.add_right_cancel_iff] at h
  apply Subtype.ext
  apply toLex.injective.eq_iff.mp
  · exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- `ofEdge` is strictly monotone from the `Edge` order into the row-major pair order. -/
lemma ofEdge_lt_of_lt {e e' : Edge n} (h : e < e') :
    (ofEdge e).1 < (ofEdge e').1 ∨ ((ofEdge e).1 = (ofEdge e').1 ∧ (ofEdge e).2 < (ofEdge e').2) := by
  have hv : (e.val : Lex (Fin n × Fin n)) < e'.val := Subtype.coe_lt_coe.mpr h
  rcases Prod.Lex.lt_iff.mp hv with hfst | ⟨hfst, hsnd⟩
  · left; simp only [ofEdge]; exact Nat.succ_lt_succ (Fin.lt_def.mp hfst)
  · right; simp only [ofEdge]
    exact ⟨by rw [hfst], Nat.succ_lt_succ (Fin.lt_def.mp hsnd)⟩

/-- Membership in the encoder's edge list. -/
lemma mem_edges {n : ℕ} {p : ℕ × ℕ} : p ∈ edges n ↔ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ n := by
  rcases p with ⟨i, j⟩
  simp only [edges, verts, List.mem_flatMap, List.mem_map, List.mem_range'_1, Prod.mk.injEq]
  constructor
  · rintro ⟨i', ⟨hi1, hi2⟩, j', ⟨hj1, hj2⟩, rfl, rfl⟩
    omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨i, ⟨h1, by omega⟩, j, ⟨by omega, by omega⟩, rfl, rfl⟩

lemma ofEdge_mem_edges (e : Edge n) : ofEdge e ∈ edges n :=
  mem_edges.mpr ⟨ofEdge_fst_pos e, ofEdge_lt e, ofEdge_snd_le e⟩

/-- Every encoder edge is the image of an sbsound edge. -/
lemma exists_ofEdge_eq {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ edges n) : ∃ e : Edge n, ofEdge e = p := by
  obtain ⟨h1, h2, h3⟩ := mem_edges.mp hp
  refine ⟨⟨toLex (⟨p.1 - 1, by omega⟩, ⟨p.2 - 1, by omega⟩), ?_⟩, ?_⟩
  · show (⟨p.1 - 1, _⟩ : Fin n) < ⟨p.2 - 1, _⟩
    exact Fin.mk_lt_mk.mpr (by omega)
  · simp only [ofEdge]
    exact Prod.ext (by simp; omega) (by simp; omega)

/-- Edge variables are pairwise distinct and determine edge and colour. -/
lemma evarNum_injective {e e' : Edge n} {c c' : Fin 2} (h : evarNum n e c = evarNum n e' c') :
    e = e' ∧ c = c' := by
  simp only [evarNum, var] at h
  have hc : c = c' := by
    fin_cases c <;> fin_cases c' <;> simp at h ⊢ <;> omega
  subst hc
  have hidx : edgeIdx n (ofEdge e).1 (ofEdge e).2 = edgeIdx n (ofEdge e').1 (ofEdge e').2 := by
    omega
  refine ⟨?_, rfl⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := edgeIdx_lt_of_lt (ofEdge_fst_pos e) (ofEdge_lt e) (ofEdge_snd_le e)
      (ofEdge_lt e') (ofEdge_snd_le e') (ofEdge_lt_of_lt hlt)
    omega
  · have := edgeIdx_lt_of_lt (ofEdge_fst_pos e') (ofEdge_lt e') (ofEdge_snd_le e')
      (ofEdge_lt e) (ofEdge_snd_le e) (ofEdge_lt_of_lt hlt)
    omega

lemma evarNum_pos (e : Edge n) (c : Fin 2) : 0 < evarNum n e c := by
  simp only [evarNum, var]; omega

lemma evarNum_le (e : Edge n) (c : Fin 2) : evarNum n e c ≤ n * (n - 1) / 2 * 2 := by
  simp only [evarNum, var]
  have := edgeIdx_lt_E (ofEdge_fst_pos e) (ofEdge_lt e) (ofEdge_snd_le e)
  have hc : c.val + 1 ≤ 2 := by omega
  omega

/-- The edge part of the assignment reads `a`. -/
lemma edgeAssign_evarNum (a : EColouring n 2) (e : Edge n) (c : Fin 2) :
    edgeAssign a (evarNum n e c) = decide (a e = c) := by
  simp only [edgeAssign]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨e', c', h, hc⟩
    obtain ⟨rfl, rfl⟩ := evarNum_injective h
    exact hc
  · intro h; exact ⟨e, c, rfl, h⟩

lemma edgeOK_init (a : EColouring n 2) : EdgeOK a (edgeAssign a) (n * (n - 1) / 2 * 2) :=
  ⟨le_refl _, edgeAssign_evarNum a⟩

/-- `var` at an sbsound edge, encoder colour `c+1`. -/
lemma var_ofEdge (e : Edge n) (c : Fin 2) :
    var n 2 (ofEdge e).1 (ofEdge e).2 (c.val + 1) = evarNum n e c := rfl

/-- `varU` on a pair of distinct 1-based vertices reads the `mkEdge` of the pair. -/
lemma varU_eq_evarNum {u w : ℕ} (hu : 1 ≤ u) (hun : u ≤ n) (hw : 1 ≤ w) (hwn : w ≤ n)
    (huw : u ≠ w) (c : Fin 2) :
    varU n 2 u w (c.val + 1) =
      evarNum n (mkEdge (⟨u - 1, by omega⟩ : Fin n) ⟨w - 1, by omega⟩
        (by intro h; apply huw; have := Fin.mk.inj_iff.mp h; omega)) c := by
  unfold varU
  by_cases h : u < w
  · rw [if_pos h, mkEdge_pos _ (Fin.mk_lt_mk.mpr (by omega))]
    simp only [evarNum, ofEdge]
    congr 2 <;> simp <;> omega
  · rw [if_neg h, mkEdge_neg _ (Fin.mk_lt_mk.mpr (by omega))]
    simp only [evarNum, ofEdge]
    congr 2 <;> simp <;> omega

/-! ### The edge clauses -/

theorem edgeClauses_sat (a : EColouring n 2) (σ : ℕ → Bool)
    (hσ : ∀ e c, σ (evarNum n e c) = decide (a e = c)) : ListSat σ (edgeClauses n 2) := by
  unfold edgeClauses
  rw [listSat_flatMap]
  intro p hp
  obtain ⟨e, rfl⟩ := exists_ofEdge_eq hp
  have hr : List.range' 1 2 = [1, 2] := rfl
  simp only [hr, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Nat.add_sub_cancel_left, show (2 : ℕ) - 2 = 0 from rfl, List.range'_zero,
    show List.range' (1 + 1) 1 = [2] from rfl, listSat_cons, listSat_nil, and_true]
  have h1 : var n 2 (ofEdge e).1 (ofEdge e).2 1 = evarNum n e 0 := rfl
  have h2 : var n 2 (ofEdge e).1 (ofEdge e).2 2 = evarNum n e 1 := rfl
  rw [h1, h2]
  constructor
  · -- ALO
    rcases Fin.exists_fin_two.mp ⟨a e, rfl⟩ with h | h
    · exact clauseSat_of_mem (List.mem_cons_self) ((litSat_pos (evarNum_pos e 0)).mpr
        (by rw [hσ]; exact decide_eq_true h))
    · exact clauseSat_of_mem (List.mem_cons_of_mem _ List.mem_cons_self)
        ((litSat_pos (evarNum_pos e 1)).mpr (by rw [hσ]; exact decide_eq_true h))
  · -- AMO
    by_cases h : a e = 0
    · exact clauseSat_of_mem (List.mem_cons_of_mem _ List.mem_cons_self)
        ((litSat_neg (evarNum_pos e 1)).mpr (by rw [hσ]; exact decide_eq_false (by rw [h]; decide)))
    · exact clauseSat_of_mem List.mem_cons_self
        ((litSat_neg (evarNum_pos e 0)).mpr (by rw [hσ]; exact decide_eq_false h))

theorem edgeClauses_varsLe : VarsLe (edgeClauses n 2) (n * (n - 1) / 2 * 2) := by
  unfold edgeClauses
  rw [varsLe_flatMap]
  intro p hp
  obtain ⟨e, rfl⟩ := exists_ofEdge_eq hp
  have hr : List.range' 1 2 = [1, 2] := rfl
  simp only [hr, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Nat.add_sub_cancel_left, show (2 : ℕ) - 2 = 0 from rfl, List.range'_zero,
    show List.range' (1 + 1) 1 = [2] from rfl]
  have h1 : var n 2 (ofEdge e).1 (ofEdge e).2 1 = evarNum n e 0 := rfl
  have h2 : var n 2 (ofEdge e).1 (ofEdge e).2 2 = evarNum n e 1 := rfl
  rw [h1, h2]
  intro c hc l hl
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl <;>
    rcases hl with rfl | rfl <;> simp [evarNum_le]


/-! ### `combos`, `verts`, `wsOf`, `SF` -/

lemma combos_sublist_length : ∀ (k : ℕ) (l : List ℕ), ∀ S ∈ combos k l, S.Sublist l ∧ S.length = k
  | 0, l, S, hS => by
    simp only [combos, List.mem_singleton] at hS
    subst hS; exact ⟨List.nil_sublist _, rfl⟩
  | k + 1, [], S, hS => by simp [combos] at hS
  | k + 1, x :: xs, S, hS => by
    simp only [combos, List.mem_append, List.mem_map] at hS
    rcases hS with ⟨T, hT, rfl⟩ | hS
    · obtain ⟨h1, h2⟩ := combos_sublist_length k xs T hT
      exact ⟨h1.cons_cons x, by simp [h2]⟩
    · obtain ⟨h1, h2⟩ := combos_sublist_length (k + 1) xs S hS
      exact ⟨h1.cons x, h2⟩

lemma mem_verts {w : ℕ} : w ∈ verts n ↔ 1 ≤ w ∧ w ≤ n := by
  simp only [verts, List.mem_range'_1]; omega

lemma verts_nodup : (verts n).Nodup := List.nodup_range'

lemma verts_pairwise : (verts n).Pairwise (· < ·) := List.pairwise_lt_range'

lemma mem_wsOf {S : List ℕ} {w : ℕ} : w ∈ wsOf n S ↔ (1 ≤ w ∧ w ≤ n) ∧ w ∉ S := by
  simp only [wsOf, List.mem_filter, mem_verts, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.contains_eq_mem, decide_eq_false_iff_not]

lemma wsOf_pairwise (S : List ℕ) : (wsOf n S).Pairwise (· < ·) :=
  verts_pairwise.filter _

/-- Filtering a nodup list by membership in one of its sublists gives back the sublist. -/
lemma filter_mem_of_sublist {S l : List ℕ} (hS : S.Sublist l) :
    l.Nodup → l.filter (fun w => S.contains w) = S := by
  induction hS with
  | slnil => intro _; rfl
  | @cons l₁ l₂ b h ih =>
    intro hn
    have hb : b ∉ l₁ := fun hb => (List.nodup_cons.mp hn).1 (h.subset hb)
    rw [List.filter_cons_of_neg (by simp [List.contains_eq_mem, hb])]
    exact ih (List.nodup_cons.mp hn).2
  | @cons_cons l₁ l₂ b h ih =>
    intro hn
    have hb : b ∉ l₂ := (List.nodup_cons.mp hn).1
    rw [List.filter_cons_of_pos (by simp [List.contains_eq_mem])]
    congr 1
    have hf : List.filter (fun w => (b :: l₁).contains w) l₂ =
        List.filter (fun w => l₁.contains w) l₂ := by
      apply List.filter_congr
      intro w hw
      have : w ≠ b := fun hwb => hb (hwb ▸ hw)
      simp only [List.contains_eq_mem, List.mem_cons, this, false_or]
    rw [hf]
    exact ih (List.nodup_cons.mp hn).2

lemma wsOf_length {S : List ℕ} (hS : S.Sublist (verts n)) : (wsOf n S).length + S.length = n := by
  have hp := List.filter_append_perm (fun w => S.contains w) (verts n)
  have hl := hp.length_eq
  rw [List.length_append, filter_mem_of_sublist hS verts_nodup] at hl
  have hv : (verts n).length = n := List.length_range'
  unfold wsOf
  omega

lemma wsOf_getD_mem {S : List ℕ} {i : ℕ} (hi : i < (wsOf n S).length) :
    (wsOf n S).getD i 0 ∈ wsOf n S := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

lemma wsOf_getD_lt {S : List ℕ} {i i' : ℕ} (hii : i < i') (hi' : i' < (wsOf n S).length) :
    (wsOf n S).getD i 0 < (wsOf n S).getD i' 0 := by
  rw [List.getD_eq_getElem _ _ (lt_trans hii hi'), List.getD_eq_getElem _ _ hi']
  exact List.pairwise_iff_getElem.mp (wsOf_pairwise S) i i' _ _ hii

lemma mem_SF {S : List ℕ} {v : Fin n} : v ∈ SF n S ↔ (v.val + 1) ∈ S := by
  simp [SF]

lemma SF_card {S : List ℕ} (hS : S.Sublist (verts n)) : (SF n S).card = S.length := by
  have hnd : S.Nodup := verts_nodup.sublist hS
  rw [← List.toFinset_card_of_nodup hnd]
  refine Finset.card_bij (fun v _ => v.val + 1) ?_ ?_ ?_
  · intro v hv; rw [List.mem_toFinset]; exact mem_SF.mp hv
  · intro v _ v' _ h; exact Fin.ext (Nat.succ_injective h)
  · intro w hw
    rw [List.mem_toFinset] at hw
    have := mem_verts.mp (hS.subset hw)
    refine ⟨⟨w - 1, by omega⟩, mem_SF.mpr ?_, ?_⟩
    · show w - 1 + 1 ∈ S
      rw [Nat.sub_add_cancel this.1]; exact hw
    · show w - 1 + 1 = w
      omega

lemma finOf_eq {w : ℕ} (h1 : 1 ≤ w) (hn : w ≤ n) : finOf n w = some ⟨w - 1, by omega⟩ := by
  simp [finOf, show w - 1 < n by omega]

/-- The codegree input at a candidate `w ∉ S` is true iff every `u ∈ S` is joined to `w` in
colour `c`. -/
lemma codegreeInputs_wsOf (a : EColouring n 2) (c : Fin 2) {S : List ℕ} {w : ℕ}
    (hw : w ∈ wsOf n S) :
    codegreeInputs a c (SF n S) ⟨w - 1, by have := (mem_wsOf.mp hw).1; omega⟩ = true ↔
      ∀ u ∈ S, ∀ hu : 1 ≤ u ∧ u ≤ n,
        colourRel a c ⟨u - 1, by omega⟩ ⟨w - 1, by have := (mem_wsOf.mp hw).1; omega⟩ := by
  obtain ⟨⟨hw1, hwn⟩, hwS⟩ := mem_wsOf.mp hw
  rw [codegreeInputs_eq_true, commonNbrs, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩ u hu ⟨hu1, hun⟩
    exact h ⟨u - 1, by omega⟩ (mem_SF.mpr (by simp only; rw [Nat.sub_add_cancel hu1]; exact hu))
  · intro h
    refine ⟨?_, ?_⟩
    · intro hmem
      have := mem_SF.mp hmem
      simp only [Nat.sub_add_cancel hw1] at this
      exact hwS this
    · intro u hu
      have hu' := mem_SF.mp hu
      have := h _ hu' ⟨by omega, by omega⟩
      convert this using 2

/-! ### The Sinz counter read across gaps

`Sinz.Clauses` speaks about consecutive input positions `i, i+1 : Fin n`; the encoder's
counter for `S` only has the positions outside `S`. Monotonicity (clause 3) bridges the gap. -/

section SinzGap
variable {k : ℕ} {y : Fin n → Bool} {R : Fin n → Fin k → Bool}

lemma sinz_chain (hC : Sinz.Clauses y R) :
    ∀ (d : ℕ) (u u' : Fin n) (j : Fin k), u'.val = u.val + d → R u j = true → R u' j = true
  | 0, u, u', j, h, hR => by
    have : u' = u := Fin.ext (by omega)
    rw [this]; exact hR
  | d + 1, u, u', j, h, hR => by
    have hlt : u.val + d + 1 < n := h ▸ u'.isLt
    have hmid := sinz_chain hC d u ⟨u.val + d, by omega⟩ j rfl hR
    have := hC.2.2.1 ⟨u.val + d, by omega⟩ hlt j hmid
    have heq : (⟨u.val + d + 1, hlt⟩ : Fin n) = u' := Fin.ext (by simp; omega)
    rw [heq] at this; exact this

lemma sinz_mono (hC : Sinz.Clauses y R) {w' w : ℕ} (h1 : 1 ≤ w') (hle : w' ≤ w) (hn : w ≤ n)
    (j : Fin k) (hR : R ⟨w' - 1, by omega⟩ j = true) : R ⟨w - 1, by omega⟩ j = true :=
  sinz_chain hC (w - w') _ _ j (by simp; omega) hR

lemma sinz_first (hC : Sinz.Clauses y R) {w : ℕ} (h1 : 1 ≤ w) (hn : w ≤ n) (hk : 0 < k)
    (hy : y ⟨w - 1, by omega⟩ = true) : R ⟨w - 1, by omega⟩ ⟨0, hk⟩ = true :=
  hC.2.1 _ hk hy

lemma sinz_carry (hC : Sinz.Clauses y R) {w' w : ℕ} (h1 : 1 ≤ w') (hlt : w' < w) (hn : w ≤ n)
    {j : ℕ} (hj : j + 1 < k)
    (hy : y ⟨w - 1, by omega⟩ = true) (hR : R ⟨w' - 1, by omega⟩ ⟨j, by omega⟩ = true) :
    R ⟨w - 1, by omega⟩ ⟨j + 1, hj⟩ = true := by
  have hmid : R ⟨w - 2, by omega⟩ ⟨j, by omega⟩ = true :=
    sinz_chain hC (w - 1 - w') _ _ _ (by simp; omega) hR
  have hi : w - 2 + 1 < n := by omega
  have := hC.2.2.2.1 ⟨w - 2, by omega⟩ hi ⟨j, by omega⟩ hj
    (by convert hy using 2; exact Fin.ext (by simp; omega)) hmid
  convert this using 2
  exact Fin.ext (by simp; omega)

lemma sinz_block (hC : Sinz.Clauses y R) {w' w : ℕ} (h1 : 1 ≤ w') (hlt : w' < w) (hn : w ≤ n)
    (hk : 0 < k)
    (hy : y ⟨w - 1, by omega⟩ = true) (hR : R ⟨w' - 1, by omega⟩ ⟨k - 1, by omega⟩ = true) :
    False := by
  have hmid : R ⟨w - 2, by omega⟩ ⟨k - 1, by omega⟩ = true :=
    sinz_chain hC (w - 1 - w') _ _ _ (by simp; omega) hR
  have hi : w - 2 + 1 < n := by omega
  exact hC.2.2.2.2 ⟨w - 2, by omega⟩ hi (by omega)
    ⟨by convert hy using 2; exact Fin.ext (by simp; omega), hmid⟩

end SinzGap

/-! ### The codegree block as a closed-form clause list -/

/-- The inner `y` fold of `codegreeColour`, evaluated. -/
lemma yfold_eq (n r c : ℕ) (S : List ℕ) :
    ∀ (ws : List ℕ) (cs₀ : List (List ℤ)) (ys₀ : List ℕ) (nv₀ : ℕ),
    ws.foldl (fun (st : List (List Int) × List Nat × Nat) w =>
        let (cs, ys, nv) := st
        let y := nv + 1
        let body : List Int := S.map fun v => -(varU n r v w c : Int)
        (cs ++ [body ++ [(y : Int)]], ys ++ [y], y)) (cs₀, ys₀, nv₀)
    = (cs₀ ++ (ws.zip (List.range' (nv₀ + 1) ws.length)).map
          (fun p => (S.map fun v => -(varU n r v p.1 c : ℤ)) ++ [(p.2 : ℤ)]),
       ys₀ ++ List.range' (nv₀ + 1) ws.length, nv₀ + ws.length)
  | [], cs₀, ys₀, nv₀ => by simp
  | w :: ws, cs₀, ys₀, nv₀ => by
    simp only [List.foldl_cons]
    rw [yfold_eq n r c S ws]
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons,
      List.append_assoc, List.singleton_append, Prod.mk.injEq]
    exact ⟨trivial, trivial, by omega⟩

/-- The `y` literal of the encoder's block: `ys.getD (i-1) 0` with `ys = range' (nv+1) m`. -/
def cgY (nv m i : ℕ) : ℤ := (((List.range' (nv + 1) m).getD (i - 1) 0 : ℕ) : ℤ)

/-- The register literal `R(i,j)` of the encoder's block: `nv + m + (i-1)k + j`. -/
def cgReg (nv m k i j : ℕ) : ℤ := ((nv + m + (i - 1) * k + j : ℕ) : ℤ)

/-- The per-`S` clauses of `codegreeColour` (allocated after `nv`), with the inner `y` fold
already evaluated: `y_i = nv + i`, registers from `nv + m`. -/
def cgBlock (n r c k : ℕ) (S : List ℕ) (nv : ℕ) : List (List ℤ) :=
  let ws := wsOf n S
  let m := ws.length
  let yCls : List (List ℤ) :=
    (ws.zip (List.range' (nv + 1) m)).map fun p =>
      (S.map fun v => -(varU n r v p.1 c : ℤ)) ++ [(p.2 : ℤ)]
  let base : List (List ℤ) := [[-(cgY nv m 1), cgReg nv m k 1 1]]
  let mid : List (List ℤ) :=
    (List.range' 2 (if m ≥ 3 then m - 2 else 0)).flatMap fun i =>
      ([[-(cgY nv m i), cgReg nv m k i 1]] : List (List ℤ))
      ++ (List.range' 1 k).map (fun j => [-(cgReg nv m k (i - 1) j), cgReg nv m k i j])
      ++ (List.range' 2 (k - 1)).map
          (fun j => [-(cgY nv m i), -(cgReg nv m k (i - 1) (j - 1)), cgReg nv m k i j])
  let block : List (List ℤ) :=
    (List.range' 2 (m - 1)).map fun i => [-(cgY nv m i), -(cgReg nv m k (i - 1) k)]
  yCls ++ base ++ mid ++ block

/-- `codegreeColour` is the extension fold of `cgBlock`. -/
lemma codegreeColour_eq_fold (n r c s t nv0 : ℕ) :
    codegreeColour n r c s t nv0 =
      (combos s (verts n)).foldl
        (fun acc S => (acc.1 ++ cgBlock n r c (t - 1) S acc.2, cgStepNv n (t - 1) S acc.2))
        ([], nv0) := by
  unfold codegreeColour
  simp only []
  congr 1
  funext acc S
  rcases acc with ⟨cls, nv⟩
  simp only []
  rw [yfold_eq]
  simp only [cgBlock, cgY, cgReg, cgStepNv, wsOf, List.nil_append, List.length_range',
    List.append_assoc]


/-! ### Satisfaction of one codegree block -/

lemma range'_getD {s m i : ℕ} (hi : i < m) : (List.range' s m).getD i 0 = s + i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range', hi]

lemma cgY_eq {nv m i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) : cgY nv m i = ((nv + i : ℕ) : ℤ) := by
  unfold cgY
  rw [range'_getD (by omega)]
  congr 1; omega

lemma wsOf_getD_bounds {S : List ℕ} {i : ℕ} (hi : i < (wsOf n S).length) :
    1 ≤ (wsOf n S).getD i 0 ∧ (wsOf n S).getD i 0 ≤ n ∧ (wsOf n S).getD i 0 ∉ S := by
  have h := mem_wsOf.mp (wsOf_getD_mem hi)
  exact ⟨h.1.1, h.1.2, h.2⟩

lemma wsOf_getD_sub_lt {S : List ℕ} {i : ℕ} (hi : i < (wsOf n S).length) :
    (wsOf n S).getD i 0 - 1 < n := by
  have h := wsOf_getD_bounds (n := n) hi; omega

lemma varU_le {u w : ℕ} (hu : 1 ≤ u) (hun : u ≤ n) (hw : 1 ≤ w) (hwn : w ≤ n) (huw : u ≠ w)
    (c : Fin 2) : varU n 2 u w (c.val + 1) ≤ n * (n - 1) / 2 * 2 := by
  rw [varU_eq_evarNum hu hun hw hwn huw]; exact evarNum_le _ _

lemma varU_pos {u w : ℕ} (hu : 1 ≤ u) (hun : u ≤ n) (hw : 1 ≤ w) (hwn : w ≤ n) (huw : u ≠ w)
    (c : Fin 2) : 0 < varU n 2 u w (c.val + 1) := by
  rw [varU_eq_evarNum hu hun hw hwn huw]; exact evarNum_pos _ _

lemma blockVals_y (a : EColouring n 2) (c : Fin 2) (k : ℕ) (S : List ℕ) (nv : ℕ) {i : ℕ}
    (hi1 : 1 ≤ i) (him : i ≤ (wsOf n S).length) :
    blockVals a c k S nv (nv + i) =
      codegreeInputs a c (SF n S) ⟨(wsOf n S).getD (i - 1) 0 - 1,
        wsOf_getD_sub_lt (n := n) (S := S) (i := i - 1) (by omega)⟩ := by
  have hb := wsOf_getD_bounds (n := n) (S := S) (i := i - 1) (by omega)
  simp only [blockVals]
  rw [if_pos (by omega), show nv + i - nv - 1 = i - 1 by omega, finOf_eq hb.1 hb.2.1]

lemma blockVals_reg (a : EColouring n 2) (c : Fin 2) {k : ℕ} (hk : 0 < k) (S : List ℕ)
    (nv : ℕ) {i j : ℕ} (hi1 : 1 ≤ i) (him : i + 1 ≤ (wsOf n S).length) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) :
    blockVals a c k S nv (nv + (wsOf n S).length + (i - 1) * k + j) =
      Sinz.truthful (k := k) (codegreeInputs a c (SF n S))
        ⟨(wsOf n S).getD (i - 1) 0 - 1,
          wsOf_getD_sub_lt (n := n) (S := S) (i := i - 1) (by omega)⟩
        ⟨j - 1, by omega⟩ := by
  have hb := wsOf_getD_bounds (n := n) (S := S) (i := i - 1) (by omega)
  simp only [blockVals]
  rw [if_neg (by omega)]
  have hd : nv + (wsOf n S).length + (i - 1) * k + j - nv - (wsOf n S).length - 1 =
      (j - 1) + k * (i - 1) := by
    rw [Nat.mul_comm k]; omega
  rw [hd, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (by omega), Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : j - 1 < k), finOf_eq hb.1 hb.2.1]
  simp only [dif_pos (show j - 1 < k by omega)]

/-- Two-literal clause `[-x, z]`. -/
lemma clauseSat_np {σ : ℕ → Bool} {x z : ℕ} (hx : 0 < x) (hz : 0 < z)
    (h : σ x = true → σ z = true) : ClauseSat σ [-(x : ℤ), (z : ℤ)] := by
  by_cases hσ : σ x = true
  · exact clauseSat_of_mem (List.mem_cons_of_mem _ List.mem_cons_self)
      ((litSat_pos hz).mpr (h hσ))
  · exact clauseSat_of_mem List.mem_cons_self
      ((litSat_neg hx).mpr (Bool.eq_false_iff.mpr hσ))

/-- Two-literal clause `[-x, -z]`. -/
lemma clauseSat_nn {σ : ℕ → Bool} {x z : ℕ} (hx : 0 < x) (hz : 0 < z)
    (h : σ x = true → σ z = true → False) : ClauseSat σ [-(x : ℤ), -(z : ℤ)] := by
  by_cases hσ : σ x = true
  · exact clauseSat_of_mem (List.mem_cons_of_mem _ List.mem_cons_self)
      ((litSat_neg hz).mpr (Bool.eq_false_iff.mpr (fun hz' => h hσ hz')))
  · exact clauseSat_of_mem List.mem_cons_self
      ((litSat_neg hx).mpr (Bool.eq_false_iff.mpr hσ))

/-- Three-literal clause `[-x, -z, w]`. -/
lemma clauseSat_nnp {σ : ℕ → Bool} {x z w : ℕ} (hx : 0 < x) (hz : 0 < z) (hw : 0 < w)
    (h : σ x = true → σ z = true → σ w = true) : ClauseSat σ [-(x : ℤ), -(z : ℤ), (w : ℤ)] := by
  by_cases hσ : σ x = true
  · by_cases hσ' : σ z = true
    · exact clauseSat_of_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        ((litSat_pos hw).mpr (h hσ hσ'))
    · exact clauseSat_of_mem (List.mem_cons_of_mem _ List.mem_cons_self)
        ((litSat_neg hz).mpr (Bool.eq_false_iff.mpr hσ'))
  · exact clauseSat_of_mem List.mem_cons_self
      ((litSat_neg hx).mpr (Bool.eq_false_iff.mpr hσ))

lemma mem_range'_mid {m i : ℕ} (h : i ∈ List.range' 2 (if m ≥ 3 then m - 2 else 0)) :
    2 ≤ i ∧ i + 1 ≤ m := by
  rw [List.mem_range'_1] at h
  split_ifs at h <;> omega

theorem cgBlock_sat (a : EColouring n 2) (c : Fin 2) {k : ℕ} (hk : 0 < k) (S : List ℕ)
    (hm : 2 ≤ (wsOf n S).length)
    (hSinz : Sinz.Clauses (codegreeInputs a c (SF n S))
      (Sinz.truthful (k := k) (codegreeInputs a c (SF n S))))
    (σ : ℕ → Bool) (nv : ℕ) (hE : EdgeOK a σ nv) :
    ListSat (extend σ nv (blockVals a c k S nv)) (cgBlock n 2 (c.val + 1) k S nv) := by
  -- values of the extended assignment on this block's variables
  have hyv : ∀ i, ∀ hi1 : 1 ≤ i, ∀ him : i ≤ (wsOf n S).length,
      extend σ nv (blockVals a c k S nv) (nv + i) =
        codegreeInputs a c (SF n S) ⟨(wsOf n S).getD (i - 1) 0 - 1,
          wsOf_getD_sub_lt (n := n) (S := S) (i := i - 1) (by omega)⟩ :=
    fun i h1 h2 => by rw [extend_gt (by omega), blockVals_y a c k S nv h1 h2]
  have hRv : ∀ i j, ∀ hi1 : 1 ≤ i, ∀ him : i + 1 ≤ (wsOf n S).length, ∀ hj1 : 1 ≤ j, ∀ hjk : j ≤ k,
      extend σ nv (blockVals a c k S nv) (nv + (wsOf n S).length + (i - 1) * k + j) =
        Sinz.truthful (k := k) (codegreeInputs a c (SF n S))
          ⟨(wsOf n S).getD (i - 1) 0 - 1,
            wsOf_getD_sub_lt (n := n) (S := S) (i := i - 1) (by omega)⟩
          ⟨j - 1, by omega⟩ :=
    fun i j h1 h2 h3 h4 => by
      rw [extend_gt (by omega), blockVals_reg a c hk S nv h1 h2 h3 h4]
  have hev : ∀ u w, ∀ hu1 : 1 ≤ u, ∀ hun : u ≤ n, ∀ hw1 : 1 ≤ w, ∀ hwn : w ≤ n, ∀ huw : u ≠ w,
      extend σ nv (blockVals a c k S nv) (varU n 2 u w (c.val + 1)) =
        decide (a (mkEdge (⟨u - 1, by omega⟩ : Fin n) ⟨w - 1, by omega⟩
          (by intro h; apply huw; have := Fin.mk.inj_iff.mp h; omega)) = c) :=
    fun u w h1 h2 h3 h4 h5 => by
      rw [extend_le (le_trans (varU_le h1 h2 h3 h4 h5 c) hE.1), varU_eq_evarNum h1 h2 h3 h4 h5,
        hE.2]
  have hwb := fun (i : ℕ) (hi : i < (wsOf n S).length) => wsOf_getD_bounds (n := n) (S := S) hi
  have hwlt := fun (i i' : ℕ) (hii : i < i') (hi' : i' < (wsOf n S).length) =>
    wsOf_getD_lt (n := n) (S := S) hii hi'
  simp only [cgBlock]
  rw [listSat_append, listSat_append, listSat_append]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- y clauses
    rw [listSat_map]
    intro p hp
    obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    have hi' : i < (wsOf n S).length := by simpa using hi
    rw [List.getElem_zip, List.getElem_range'] at hpi
    subst hpi
    simp only
    have hb := hwb i hi'
    have hgd : (wsOf n S)[i] = (wsOf n S).getD i 0 := (List.getD_eq_getElem _ _ hi').symm
    rw [hgd]
    by_cases hy : codegreeInputs a c (SF n S) ⟨(wsOf n S).getD i 0 - 1, by omega⟩ = true
    · refine clauseSat_of_mem (List.mem_append_right _ List.mem_cons_self) ?_
      rw [litSat_pos (by omega)]
      have := hyv (i + 1) (by omega) (by omega)
      rw [show nv + 1 + 1 * i = nv + (i + 1) by omega, this]
      simpa using hy
    · rw [codegreeInputs_wsOf a c (wsOf_getD_mem hi')] at hy
      push_neg at hy
      obtain ⟨u, huS, ⟨hu1, hun⟩, hrel⟩ := hy
      have huw : u ≠ (wsOf n S).getD i 0 := fun h => hb.2.2 (h ▸ huS)
      refine clauseSat_of_mem (List.mem_append_left _ (List.mem_map.mpr ⟨u, huS, rfl⟩)) ?_
      rw [litSat_neg (varU_pos hu1 hun hb.1 hb.2.1 huw c), hev u _ hu1 hun hb.1 hb.2.1 huw]
      apply decide_eq_false
      intro hc
      exact hrel ⟨_, hc⟩
  · -- base clause
    rw [listSat_singleton, cgY_eq (le_refl _) (by omega)]
    unfold cgReg
    refine clauseSat_np (by omega) (by omega) ?_
    rw [hyv 1 (le_refl _) (by omega), hRv 1 1 (le_refl _) (by omega) (le_refl _) hk]
    intro hy
    exact sinz_first hSinz (hwb 0 (by omega)).1 (hwb 0 (by omega)).2.1 hk hy
  · -- mid clauses
    rw [listSat_flatMap]
    intro i hi
    obtain ⟨hi2, him⟩ := mem_range'_mid hi
    have hb := hwb (i - 1) (by omega)
    have hb' := hwb (i - 2) (by omega)
    have hlt := hwlt (i - 2) (i - 1) (by omega) (by omega)
    rw [listSat_append, listSat_append, listSat_singleton, listSat_map, listSat_map]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [cgY_eq (by omega) (by omega)]
      unfold cgReg
      refine clauseSat_np (by omega) (by omega) ?_
      rw [hyv i (by omega) (by omega), hRv i 1 (by omega) him (le_refl _) hk]
      intro hy
      exact sinz_first hSinz hb.1 hb.2.1 hk hy
    · intro j hj
      rw [List.mem_range'_1] at hj
      unfold cgReg
      refine clauseSat_np (by omega) (by omega) ?_
      rw [hRv i j (by omega) him (by omega) (by omega),
        hRv (i - 1) j (by omega) (by omega) (by omega) (by omega)]
      intro hR
      exact sinz_mono hSinz hb'.1 (le_of_lt hlt) hb.2.1 _ hR
    · intro j hj
      rw [List.mem_range'_1] at hj
      rw [cgY_eq (by omega) (by omega)]
      unfold cgReg
      refine clauseSat_nnp (by omega) (by omega) (by omega) ?_
      rw [hyv i (by omega) (by omega), hRv i j (by omega) him (by omega) (by omega),
        hRv (i - 1) (j - 1) (by omega) (by omega) (by omega) (by omega)]
      intro hy hR
      have := sinz_carry hSinz hb'.1 hlt hb.2.1 (j := j - 2) (by omega) hy
        (by convert hR using 2 <;> first | omega | exact Fin.ext (by simp; omega))
      convert this using 2 <;> first | omega | exact Fin.ext (by simp; omega)
  · -- block clauses
    rw [listSat_map]
    intro i hi
    rw [List.mem_range'_1] at hi
    have hb := hwb (i - 1) (by omega)
    have hb' := hwb (i - 2) (by omega)
    have hlt := hwlt (i - 2) (i - 1) (by omega) (by omega)
    rw [cgY_eq (by omega) (by omega)]
    unfold cgReg
    refine clauseSat_nn (by omega) (by omega) ?_
    rw [hyv i (by omega) (by omega), hRv (i - 1) k (by omega) (by omega) hk (le_refl _)]
    intro hy hR
    exact sinz_block hSinz hb'.1 hlt hb.2.1 hk hy hR


/-! ### The vertex-lex block, part 1: the moved list

The encoder's `moved` list of transposition `v` (1-based) is sbsound's `movedList` of
`vswap n (v-1)`, translated by `ofEdge`, paired with the image edge. -/

/-- Row-major order on pairs. -/
def pairLt (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-- Its reflexive closure. -/
def pairLe (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

lemma pairLt_ne {p q : ℕ × ℕ} (h : pairLt p q) : p ≠ q := by
  rintro rfl; rcases h with h | ⟨-, h⟩ <;> exact lt_irrefl _ h

lemma pairLe_antisymm {p q : ℕ × ℕ} (h1 : pairLe p q) (h2 : pairLe q p) : p = q := by
  rcases p with ⟨a, b⟩; rcases q with ⟨a', b'⟩
  simp only [pairLe] at h1 h2
  ext <;> simp <;> omega

lemma edges_pairwise : (edges n).Pairwise pairLt := by
  unfold edges
  rw [List.pairwise_flatMap]
  constructor
  · intro i _
    rw [List.pairwise_map]
    exact (List.pairwise_lt_range').imp fun {a b} h => Or.inr ⟨rfl, h⟩
  · refine verts_pairwise.imp fun {i i'} hii x hx y hy => ?_
    rw [List.mem_map] at hx hy
    obtain ⟨_, -, rfl⟩ := hx
    obtain ⟨_, -, rfl⟩ := hy
    exact Or.inl hii

/-- The encoder's moved list (the `moved` of `lexTransposition`). -/
def movedE (n v : ℕ) : List ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (edges n).filterMap fun e =>
    let f := swapEdge v e
    if f = e then none else some (e, f)

lemma filterMap_ite_none {α β : Type*} (p : α → Prop) [DecidablePred p] (g : α → β) :
    ∀ l : List α, l.filterMap (fun e => if p e then none else some (g e)) =
      (l.filter fun e => !decide (p e)).map g
  | [] => rfl
  | e :: l => by
    by_cases h : p e
    · simp [List.filterMap_cons, h, filterMap_ite_none p g l]
    · simp [List.filterMap_cons, h, filterMap_ite_none p g l]

/-- Commutation of the transposition with the translation. -/
lemma swapEdge_ofEdge {v : ℕ} (hv : 1 ≤ v) (h : v - 1 + 1 < n) (e : Edge n) :
    swapEdge v (ofEdge e) = ofEdge (permEdge (vswap n (v - 1) h) e) := by
  have key : ∀ x : Fin n,
      (if x.val + 1 = v then v + 1 else if x.val + 1 = v + 1 then v else x.val + 1) =
        ((vswap n (v - 1) h) x).val + 1 := by
    intro x
    simp only [vswap, Equiv.swap_apply_def]
    split_ifs with h1 h2 h3 h4 h5 h6 <;> simp_all [Fin.ext_iff] <;> omega
  simp only [swapEdge, ofEdge, permEdge, key]
  set i := (ofLex e.val).1
  set j := (ofLex e.val).2
  set τ := vswap n (v - 1) h
  by_cases hlt : τ i < τ j
  · rw [mkEdge_pos _ hlt, if_pos (Nat.succ_lt_succ (Fin.lt_def.mp hlt))]
    rfl
  · have hgt : τ j < τ i := lt_of_le_of_ne (not_lt.mp hlt)
      (fun heq => (ne_of_lt e.prop) (τ.injective heq).symm)
    rw [mkEdge_neg _ hgt, if_neg (fun hc => hlt (Fin.lt_def.mpr (Nat.lt_of_succ_lt_succ hc)))]
    rfl

lemma movedE_eq {v : ℕ} (hv : 1 ≤ v) (h : v - 1 + 1 < n) :
    movedE n v = (movedList (vswap n (v - 1) h)).map
      (fun e => (ofEdge e, ofEdge (permEdge (vswap n (v - 1) h) e))) := by
  set τ := vswap n (v - 1) h with hτ
  have hfm : movedE n v = ((edges n).filter fun e => !decide (swapEdge v e = e)).map
      (fun e => (e, swapEdge v e)) := by
    unfold movedE
    exact filterMap_ite_none (fun e => swapEdge v e = e) (fun e => (e, swapEdge v e)) _
  have hfilt : ((edges n).filter fun e => !decide (swapEdge v e = e)) = (movedList τ).map ofEdge := by
    have hp1 : ((edges n).filter fun e => !decide (swapEdge v e = e)).Pairwise pairLt :=
      edges_pairwise.filter _
    have hp2 : ((movedList τ).map ofEdge).Pairwise pairLt := by
      rw [List.pairwise_map]
      exact (List.sortedLT_iff_pairwise.mp (movedList_sortedLT τ)).imp fun {a b} hab =>
        ofEdge_lt_of_lt hab
    apply List.Perm.eq_of_pairwise (le := pairLe)
    · intro a b _ _ h1 h2; exact pairLe_antisymm h1 h2
    · exact hp1.imp fun {a b} hab => by
        rcases hab with hab | ⟨h1, h2⟩
        · exact Or.inl hab
        · exact Or.inr ⟨h1, le_of_lt h2⟩
    · exact hp2.imp fun {a b} hab => by
        rcases hab with hab | ⟨h1, h2⟩
        · exact Or.inl hab
        · exact Or.inr ⟨h1, le_of_lt h2⟩
    · rw [List.perm_ext_iff_of_nodup (hp1.imp fun {a b} hab => pairLt_ne hab)
        (hp2.imp fun {a b} hab => pairLt_ne hab)]
      intro p
      rw [List.mem_filter, List.mem_map]
      constructor
      · rintro ⟨hp, hne⟩
        obtain ⟨e, rfl⟩ := exists_ofEdge_eq hp
        refine ⟨e, mem_movedList.mpr ?_, rfl⟩
        intro hfix
        rw [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hne
        exact hne (by rw [swapEdge_ofEdge hv h, hfix])
      · rintro ⟨e, he, rfl⟩
        refine ⟨ofEdge_mem_edges e, ?_⟩
        rw [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
        rw [swapEdge_ofEdge hv h]
        exact fun hc => (mem_movedList.mp he) (ofEdge_injective hc)
  rw [hfm, hfilt, List.map_map]
  apply List.map_congr_left
  intro e _
  simp only [Function.comp]
  rw [swapEdge_ofEdge hv h]


/-! ### The vertex-lex block, part 2: renaming and transport -/

/-- The encoder's per-position step (the `step` of `lexTransposition`, `last` fixed). -/
def lexStep (n r last : ℕ) :
    (List (List ℤ) × Option ℕ × ℕ) → (ℕ × (ℕ × ℕ) × (ℕ × ℕ)) → List (List ℤ) × Option ℕ × ℕ :=
  fun st ie =>
    let (cls, eqch, nv) := st
    let (t, e, f) := ie
    let prem : List Int := match eqch with | none => [] | some q => [-(q : Int)]
    let cmp : List (List Int) :=
      (List.range' 1 r).flatMap fun cf =>
        (List.range' (cf + 1) (r - cf)).map fun ce =>
          prem ++ [-(var n r e.1 e.2 ce : Int), -(var n r f.1 f.2 cf : Int)]
    if t = last then (cls ++ cmp, eqch, nv)
    else
      let q := nv + 1
      let qCls : List (List Int) :=
        (List.range' 1 r).flatMap fun c =>
          [[-(q : Int), -(var n r e.1 e.2 c : Int), (var n r f.1 f.2 c : Int)],
           [(q : Int), -(var n r e.1 e.2 c : Int), -(var n r f.1 f.2 c : Int)]]
      let nch := q + 1
      let chCls : List (List Int) :=
        match eqch with
        | none => [[-(nch : Int), (q : Int)], [(nch : Int), -(q : Int)]]
        | some p => [[-(nch : Int), (p : Int)], [-(nch : Int), (q : Int)],
                     [(nch : Int), -(p : Int), -(q : Int)]]
      (cls ++ cmp ++ qCls ++ chCls, some nch, nch)

lemma lexTransposition_eq (n r v nv0 : ℕ) :
    lexTransposition n r v nv0 =
      match ((movedE n v).zipIdx.map (fun p => (p.2, p.1.1, p.1.2))).foldl
          (lexStep n r ((movedE n v).length - 1)) ([], none, nv0) with
      | (cls, _, nv) => (cls, nv) := rfl

/-- DIMACS numbers of sbsound's vertex-lex variables for the block allocated after `nv`:
`q_t = nv+2t+1`, `ch_t = nv+2t+2` (written `+1+1` to match the encoder's `nch = q + 1`). -/
def lexRen (nv : ℕ) : SVar n 2 → ℕ
  | Sum.inl (e, c) => evarNum n e c
  | Sum.inr (Aux.vq _ t) => nv + 2 * t + 1
  | Sum.inr (Aux.vch _ t) => nv + 2 * t + 1 + 1
  | Sum.inr (Aux.ceq _ _) => 0

/-- The literal renaming. -/
def lexRenLit (nv : ℕ) (l : SLit n 2) : ℤ :=
  if l.2 then (lexRen nv l.1 : ℤ) else -(lexRen nv l.1 : ℤ)

lemma lexRenLit_negL (nv : ℕ) (x : SVar n 2) : lexRenLit nv (negL x) = -(lexRen nv x : ℤ) := rfl

lemma lexRenLit_posL (nv : ℕ) (x : SVar n 2) : lexRenLit nv (posL x) = (lexRen nv x : ℤ) := rfl

/-- Transport of clause satisfaction along the renaming, given agreement on the clause's
variables. -/
lemma clauseSat_transport {σ : ℕ → Bool} {β : SAssign n 2} {nv : ℕ} {C : SClause n 2}
    {D : List ℤ} (hD : D = C.map (lexRenLit nv)) (hβ : satSClause β C = true)
    (hagree : ∀ l ∈ C, 0 < lexRen nv l.1 ∧ σ (lexRen nv l.1) = β l.1) : ClauseSat σ D := by
  subst hD
  obtain ⟨l, hl, hev⟩ := List.any_eq_true.mp hβ
  obtain ⟨hpos, hσ⟩ := hagree l hl
  refine ⟨lexRenLit nv l, List.mem_map.mpr ⟨l, hl, rfl⟩, ?_⟩
  rcases l with ⟨x, b⟩
  cases b
  · have : β x = false := by simpa [evalSLit] using hev
    simp only [lexRenLit, Bool.false_eq_true, if_false]
    exact (litSat_neg hpos).mpr (by rw [hσ, this])
  · have : β x = true := by simpa [evalSLit] using hev
    simp only [lexRenLit, if_true]
    exact (litSat_pos hpos).mpr (by rw [hσ, this])

section LexAgree
variable (a : EColouring n 2) {v : ℕ} (hv : 1 ≤ v) (h : v - 1 + 1 < n) (σ : ℕ → Bool) (nv : ℕ)
  (hE : EdgeOK a σ nv)
include hE

lemma lexAgree_evar (e : Edge n) (c : Fin 2) :
    0 < lexRen nv (evar e c : SVar n 2) ∧
      extend σ nv (lexVals a v nv) (lexRen nv (evar e c : SVar n 2)) =
        canonAssign a [] (evar e c) := by
  refine ⟨evarNum_pos e c, ?_⟩
  simp only [lexRen]
  rw [extend_le (le_trans (evarNum_le e c) hE.1), hE.2]
  rfl

omit hE in
lemma lexAgree_vq (t : ℕ) :
    0 < lexRen nv (qvar (v - 1) t : SVar n 2) ∧
      extend σ nv (lexVals a v nv) (lexRen nv (qvar (v - 1) t : SVar n 2)) =
        canonAssign a [] (qvar (v - 1) t) := by
  refine ⟨by simp [lexRen], ?_⟩
  simp only [lexRen]
  rw [extend_gt (by omega)]
  simp only [lexVals]
  rw [show nv + 2 * t + 1 - nv - 1 = 2 * t by omega, if_pos (by omega),
    show 2 * t / 2 = t by omega]

omit hE in
lemma lexAgree_vch (t : ℕ) :
    0 < lexRen nv (chvar (v - 1) t : SVar n 2) ∧
      extend σ nv (lexVals a v nv) (lexRen nv (chvar (v - 1) t : SVar n 2)) =
        canonAssign a [] (chvar (v - 1) t) := by
  refine ⟨by simp [lexRen], ?_⟩
  simp only [lexRen]
  rw [extend_gt (by omega)]
  simp only [lexVals]
  rw [show nv + 2 * t + 1 + 1 - nv - 1 = 2 * t + 1 by omega, if_neg (by omega),
    show (2 * t + 1) / 2 = t by omega]

end LexAgree


/-! ### The vertex-lex block, part 3: the fold invariant -/

/-- Invariant after processing moved-positions `< t` of one transposition allocated after
`nv`: clauses so far are satisfied and bounded by the current count, the count is
`nv + 2·min(t, last)`, and the chain variable is `ch_{t-1}` while `t ≤ last`. -/
def LexInv (σ' : ℕ → Bool) (nv last t : ℕ) (st : List (List ℤ) × Option ℕ × ℕ) : Prop :=
  ListSat σ' st.1 ∧ VarsLe st.1 st.2.2 ∧ st.2.2 = nv + 2 * min t last ∧
    (t ≤ last → st.2.1 = if t = 0 then none else some (nv + 2 * t))

lemma natAbs_neg_natCast (x : ℕ) : (-(x : ℤ)).natAbs = x := by simp

lemma natAbs_natCast' (x : ℕ) : ((x : ℤ)).natAbs = x := by simp

/-- The encoder's comparison clauses at one position (`r = 2`, edges `E ↦ F`). -/
def cmpE (n : ℕ) (prem : List ℤ) (E F : Edge n) : List (List ℤ) :=
  (List.range' 1 2).flatMap fun cf =>
    (List.range' (cf + 1) (2 - cf)).map fun ce =>
      prem ++ [-(var n 2 (ofEdge E).1 (ofEdge E).2 ce : ℤ), -(var n 2 (ofEdge F).1 (ofEdge F).2 cf : ℤ)]

/-- The encoder's `q`-definition clauses at one position (`r = 2`). -/
def qClsE (n : ℕ) (q : ℕ) (E F : Edge n) : List (List ℤ) :=
  (List.range' 1 2).flatMap fun c =>
    [[-(q : ℤ), -(var n 2 (ofEdge E).1 (ofEdge E).2 c : ℤ), (var n 2 (ofEdge F).1 (ofEdge F).2 c : ℤ)],
     [(q : ℤ), -(var n 2 (ofEdge E).1 (ofEdge E).2 c : ℤ), -(var n 2 (ofEdge F).1 (ofEdge F).2 c : ℤ)]]

lemma vlexPrem_of_ne {v t : ℕ} (ht : t ≠ 0) :
    (vlexPrem v t : List (SLit n 2)) = [negL (chvar v (t - 1))] := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rfl

lemma vlexChClauses_of_eq {v t : ℕ} (ht : t = 0) :
    (vlexChClauses v t : List (SClause n 2)) =
      [[negL (chvar v t), posL (qvar v t)], [posL (chvar v t), negL (qvar v t)]] := by
  subst ht; rfl

lemma vlexChClauses_of_ne {v t : ℕ} (ht : t ≠ 0) :
    (vlexChClauses v t : List (SClause n 2)) =
      [[negL (chvar v t), posL (chvar v (t - 1))], [negL (chvar v t), posL (qvar v t)],
       [posL (chvar v t), negL (chvar v (t - 1)), negL (qvar v t)]] := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rfl

/-- The core of the step: given the premise literals (`prem`) and chain clauses (`chCls`)
in the shapes the invariant guarantees, the step preserves the invariant. -/
lemma lexStep_core (a : EColouring n 2) {v : ℕ} (hv : 1 ≤ v) (h : v - 1 + 1 < n)
    (σ : ℕ → Bool) (nv : ℕ) (hE : EdgeOK a σ nv)
    (hV : lexView a ≤ lexView (actV (vswap n (v - 1) h) a))
    {t : ℕ} (ht : t < (movedList (vswap n (v - 1) h)).length)
    (cls : List (List ℤ)) (prem : List ℤ) (eqch : Option ℕ) (chCls : List (List ℤ))
    (hsat : ListSat (extend σ nv (lexVals a v nv)) cls) (hvars : VarsLe cls (nv + 2 * t))
    (hprem : prem = (vlexPrem (v - 1) t : List (SLit n 2)).map (lexRenLit nv))
    (hpremv : ∀ l ∈ prem, l.natAbs ≤ nv + 2 * t)
    (hchS : t + 1 < (movedList (vswap n (v - 1) h)).length →
      ListSat (extend σ nv (lexVals a v nv)) chCls)
    (hchV : t + 1 < (movedList (vswap n (v - 1) h)).length →
      VarsLe chCls (nv + 2 * t + 1 + 1)) :
    LexInv (extend σ nv (lexVals a v nv)) nv ((movedList (vswap n (v - 1) h)).length - 1) (t + 1)
      (if t = (movedList (vswap n (v - 1) h)).length - 1 then
        (cls ++ cmpE n prem ((movedList (vswap n (v - 1) h))[t]'ht)
          (permEdge (vswap n (v - 1) h) ((movedList (vswap n (v - 1) h))[t]'ht)), eqch, nv + 2 * t)
       else
        (cls ++ cmpE n prem ((movedList (vswap n (v - 1) h))[t]'ht)
            (permEdge (vswap n (v - 1) h) ((movedList (vswap n (v - 1) h))[t]'ht)) ++
          qClsE n (nv + 2 * t + 1) ((movedList (vswap n (v - 1) h))[t]'ht)
            (permEdge (vswap n (v - 1) h) ((movedList (vswap n (v - 1) h))[t]'ht)) ++ chCls,
         some (nv + 2 * t + 1 + 1), nv + 2 * t + 1 + 1)) := by
  set τ := vswap n (v - 1) h with hτ
  set L := movedList τ with hL
  set last := L.length - 1 with hlast
  set σ' := extend σ nv (lexVals a v nv) with hσ'
  set E := L[t]'ht with hEdef
  set F := permEdge τ E with hFdef
  have hβe : ∀ e c, canonAssign a [] (evar e c : SVar n 2) = decide (a e = c) := fun e c => rfl
  have hagE : ∀ (e : Edge n) (c : Fin 2), 0 < lexRen nv (evar e c : SVar n 2) ∧
      σ' (lexRen nv (evar e c : SVar n 2)) = canonAssign a [] (evar e c) :=
    fun e c => lexAgree_evar a (v := v) σ nv hE e c
  have hagQ : ∀ s : ℕ, 0 < lexRen nv (qvar (v - 1) s : SVar n 2) ∧
      σ' (lexRen nv (qvar (v - 1) s : SVar n 2)) = canonAssign a [] (qvar (v - 1) s) :=
    fun s => lexAgree_vq a (v := v) σ nv s
  have hagC : ∀ s : ℕ, 0 < lexRen nv (chvar (v - 1) s : SVar n 2) ∧
      σ' (lexRen nv (chvar (v - 1) s : SVar n 2)) = canonAssign a [] (chvar (v - 1) s) :=
    fun s => lexAgree_vch a (v := v) σ nv s
  have hcmp : ∀ C ∈ vlexCmpClauses (v - 1) t E F, satSClause (canonAssign a []) C = true :=
    fun C hC => sat_vlexCmp a τ (v - 1) (canonAssign a []) hβe (canonAssign_vch a [] h) hV ht hC
  have hCcmp : (vlexPrem (v - 1) t ++ [negL (evar E 1), negL (evar F 0)] : SClause n 2) ∈
      vlexCmpClauses (v - 1) t E F := by
    simp only [vlexCmpClauses, List.mem_flatMap, List.mem_map, List.mem_filter,
      List.mem_finRange, true_and]
    exact ⟨0, 1, by decide, rfl⟩
  have hEle : ∀ e c, evarNum n e c ≤ nv := fun e c => le_trans (evarNum_le e c) hE.1
  have htl : t ≤ last := by omega
  -- the comparison clause
  have hprem_agree : ∀ l ∈ (vlexPrem (v - 1) t : List (SLit n 2)),
      0 < lexRen nv l.1 ∧ σ' (lexRen nv l.1) = canonAssign a [] l.1 := by
    intro l hl
    by_cases ht0 : t = 0
    · rw [ht0] at hl; simp [vlexPrem] at hl
    · rw [vlexPrem_of_ne ht0, List.mem_singleton] at hl
      subst hl
      exact hagC (t - 1)
  have hcmpSat : ListSat σ' (cmpE n prem E F) := by
    unfold cmpE
    rw [listSat_flatMap]
    intro cf hcf
    rw [listSat_map]
    intro ce hce
    rw [List.mem_range'_1] at hcf hce
    have hcf1 : cf = 1 := by omega
    subst hcf1
    have hce2 : ce = 2 := by omega
    subst hce2
    refine clauseSat_transport (nv := nv) (C := vlexPrem (v - 1) t ++ [negL (evar E 1), negL (evar F 0)])
      ?_ (hcmp _ hCcmp) ?_
    · rw [List.map_append, ← hprem]; rfl
    · intro l hl
      rw [List.mem_append] at hl
      rcases hl with hl | hl
      · exact hprem_agree l hl
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact hagE E 1
        · exact hagE F 0
  have hcmpVars : VarsLe (cmpE n prem E F) (nv + 2 * t) := by
    unfold cmpE
    rw [varsLe_flatMap]
    intro cf hcf
    rw [varsLe_map]
    intro ce hce
    rw [List.mem_range'_1] at hcf hce
    have hcf1 : cf = 1 := by omega
    subst hcf1
    have hce2 : ce = 2 := by omega
    subst hce2
    intro l hl
    rw [List.mem_append] at hl
    rcases hl with hl | hl
    · exact hpremv l hl
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · rw [natAbs_neg_natCast]; exact le_trans (hEle E 1) (by omega)
      · rw [natAbs_neg_natCast]; exact le_trans (hEle F 0) (by omega)
  by_cases hlt : t = last
  · rw [if_pos hlt]
    refine ⟨?_, ?_, ?_, fun h' => absurd h' (by omega)⟩
    · rw [listSat_append]; exact ⟨hsat, hcmpSat⟩
    · rw [varsLe_append]; exact ⟨hvars, hcmpVars⟩
    · show nv + 2 * t = nv + 2 * min (t + 1) last
      rw [Nat.min_eq_right (by omega), hlt]
  · have htlt : t < last := lt_of_le_of_ne htl hlt
    have ht1 : t + 1 < L.length := by omega
    rw [if_neg hlt]
    have hq : ∀ C ∈ vlexQClauses (v - 1) t E F, satSClause (canonAssign a []) C = true :=
      fun C hC => sat_vlexQ a τ (v - 1) (canonAssign a []) hβe ht (canonAssign_vq a [] h ht) hC
    have hqmem : ∀ c : Fin 2,
        ([negL (qvar (v - 1) t), negL (evar E c), posL (evar F c)] : SClause n 2) ∈
            vlexQClauses (v - 1) t E F ∧
        ([posL (qvar (v - 1) t), negL (evar E c), negL (evar F c)] : SClause n 2) ∈
            vlexQClauses (v - 1) t E F := by
      intro c
      simp only [vlexQClauses, List.mem_flatMap, List.mem_finRange, true_and]
      exact ⟨⟨c, by simp⟩, ⟨c, by simp⟩⟩
    have hagreeQ : ∀ c : Fin 2, ∀ l ∈ ([negL (qvar (v - 1) t), negL (evar E c), posL (evar F c)] :
        SClause n 2), 0 < lexRen nv l.1 ∧ σ' (lexRen nv l.1) = canonAssign a [] l.1 := by
      intro c l hl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · exact hagQ t
      · exact hagE E c
      · exact hagE F c
    have hagreeQ' : ∀ c : Fin 2, ∀ l ∈ ([posL (qvar (v - 1) t), negL (evar E c), negL (evar F c)] :
        SClause n 2), 0 < lexRen nv l.1 ∧ σ' (lexRen nv l.1) = canonAssign a [] l.1 := by
      intro c l hl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · exact hagQ t
      · exact hagE E c
      · exact hagE F c
    have hqSat : ListSat σ' (qClsE n (nv + 2 * t + 1) E F) := by
      unfold qClsE
      rw [listSat_flatMap]
      intro c hc
      rw [List.mem_range'_1] at hc
      have hc' : c = 1 ∨ c = 2 := by omega
      rw [listSat_cons, listSat_cons]
      rcases hc' with rfl | rfl
      · exact ⟨clauseSat_transport (nv := nv) (C := [negL (qvar (v - 1) t), negL (evar E 0), posL (evar F 0)])
            rfl (hq _ (hqmem 0).1) (hagreeQ 0),
          clauseSat_transport (nv := nv) (C := [posL (qvar (v - 1) t), negL (evar E 0), negL (evar F 0)])
            rfl (hq _ (hqmem 0).2) (hagreeQ' 0), listSat_nil⟩
      · exact ⟨clauseSat_transport (nv := nv) (C := [negL (qvar (v - 1) t), negL (evar E 1), posL (evar F 1)])
            rfl (hq _ (hqmem 1).1) (hagreeQ 1),
          clauseSat_transport (nv := nv) (C := [posL (qvar (v - 1) t), negL (evar E 1), negL (evar F 1)])
            rfl (hq _ (hqmem 1).2) (hagreeQ' 1), listSat_nil⟩
    have hqVars : VarsLe (qClsE n (nv + 2 * t + 1) E F) (nv + 2 * t + 1 + 1) := by
      unfold qClsE
      rw [varsLe_flatMap]
      intro c hc
      rw [List.mem_range'_1] at hc
      have hc' : c = 1 ∨ c = 2 := by omega
      have hE1 : var n 2 (ofEdge E).1 (ofEdge E).2 1 = evarNum n E 0 := rfl
      have hE2 : var n 2 (ofEdge E).1 (ofEdge E).2 2 = evarNum n E 1 := rfl
      have hF1 : var n 2 (ofEdge F).1 (ofEdge F).2 1 = evarNum n F 0 := rfl
      have hF2 : var n 2 (ofEdge F).1 (ofEdge F).2 2 = evarNum n F 1 := rfl
      have hb : ∀ e c, evarNum n e c ≤ nv + 2 * t + 1 + 1 :=
        fun e c => le_trans (hEle e c) (by omega)
      rcases hc' with rfl | rfl <;> simp only [hE1, hE2, hF1, hF2] <;>
        intro C hC l hl <;>
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hC <;>
        rcases hC with rfl | rfl <;>
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl <;>
        rcases hl with rfl | rfl | rfl <;>
        simp only [natAbs_neg_natCast, natAbs_natCast'] <;>
        first | omega | exact hb _ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [listSat_append, listSat_append, listSat_append]
      exact ⟨⟨⟨hsat, hcmpSat⟩, hqSat⟩, hchS ht1⟩
    · rw [varsLe_append, varsLe_append, varsLe_append]
      exact ⟨⟨⟨varsLe_mono hvars (by show nv + 2 * t ≤ nv + 2 * t + 1 + 1; omega),
        varsLe_mono hcmpVars (by show nv + 2 * t ≤ nv + 2 * t + 1 + 1; omega)⟩, hqVars⟩, hchV ht1⟩
    · show nv + 2 * t + 1 + 1 = nv + 2 * min (t + 1) last
      rw [Nat.min_eq_left (by omega)]; omega
    · intro _
      show some (nv + 2 * t + 1 + 1) = if t + 1 = 0 then none else some (nv + 2 * (t + 1))
      rw [if_neg (Nat.succ_ne_zero t)]
      exact congrArg some (by omega)

lemma lexStep_inv (a : EColouring n 2) {v : ℕ} (hv : 1 ≤ v) (h : v - 1 + 1 < n)
    (σ : ℕ → Bool) (nv : ℕ) (hE : EdgeOK a σ nv)
    (hV : lexView a ≤ lexView (actV (vswap n (v - 1) h) a))
    {t : ℕ} (ht : t < (movedList (vswap n (v - 1) h)).length)
    (st : List (List ℤ) × Option ℕ × ℕ)
    (hinv : LexInv (extend σ nv (lexVals a v nv)) nv
      ((movedList (vswap n (v - 1) h)).length - 1) t st) :
    LexInv (extend σ nv (lexVals a v nv)) nv ((movedList (vswap n (v - 1) h)).length - 1) (t + 1)
      (lexStep n 2 ((movedList (vswap n (v - 1) h)).length - 1) st
        (t, ofEdge ((movedList (vswap n (v - 1) h))[t]'ht),
          ofEdge (permEdge (vswap n (v - 1) h) ((movedList (vswap n (v - 1) h))[t]'ht)))) := by
  have hagQ : ∀ s : ℕ, 0 < lexRen nv (qvar (v - 1) s : SVar n 2) ∧
      extend σ nv (lexVals a v nv) (lexRen nv (qvar (v - 1) s : SVar n 2)) =
        canonAssign a [] (qvar (v - 1) s) :=
    fun s => lexAgree_vq a (v := v) σ nv s
  have hagC : ∀ s : ℕ, 0 < lexRen nv (chvar (v - 1) s : SVar n 2) ∧
      extend σ nv (lexVals a v nv) (lexRen nv (chvar (v - 1) s : SVar n 2)) =
        canonAssign a [] (chvar (v - 1) s) :=
    fun s => lexAgree_vch a (v := v) σ nv s
  have hchS : t + 1 < (movedList (vswap n (v - 1) h)).length →
      ∀ C ∈ vlexChClauses (v - 1) t, satSClause (canonAssign a []) C = true :=
    fun ht1 C hC => sat_vlexCh a (vswap n (v - 1) h) (v - 1) (canonAssign a []) ht1
      (canonAssign_vq a [] h ht) (canonAssign_vch a [] h) hC
  rcases st with ⟨cls, eqch, nvc⟩
  obtain ⟨hsat, hvars, hnv, hch⟩ := hinv
  simp only at hsat hvars hnv hch
  have htl : t ≤ (movedList (vswap n (v - 1) h)).length - 1 := by omega
  rw [Nat.min_eq_left htl] at hnv
  have hch' := hch htl
  subst hnv
  unfold lexStep
  simp only []
  rcases eqch with - | p
  · have ht0 : t = 0 := by
      by_contra hne
      rw [if_neg hne] at hch'
      simp at hch'
    refine lexStep_core a hv h σ nv hE hV ht cls _ none _ hsat hvars ?_ ?_ ?_ ?_
    · rw [ht0]; rfl
    · intro l hl; simp at hl
    · intro ht1
      have hS := hchS ht1
      rw [vlexChClauses_of_eq ht0] at hS
      rw [listSat_cons, listSat_cons]
      refine ⟨clauseSat_transport (nv := nv) (C := [negL (chvar (v - 1) t), posL (qvar (v - 1) t)])
          rfl (hS _ (by simp)) ?_,
        clauseSat_transport (nv := nv) (C := [posL (chvar (v - 1) t), negL (qvar (v - 1) t)])
          rfl (hS _ (by simp)) ?_, listSat_nil⟩
      · intro l hl
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact hagC t
        · exact hagQ t
      · intro l hl
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact hagC t
        · exact hagQ t
    · intro _ C hC l hl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl <;>
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl <;>
        rcases hl with rfl | rfl <;> simp only [natAbs_neg_natCast, natAbs_natCast'] <;> omega
  · have ht0 : t ≠ 0 := by
      rintro rfl
      simp at hch'
    have hp : p = nv + 2 * t := by
      rw [if_neg ht0] at hch'
      exact Option.some.inj hch'
    subst hp
    refine lexStep_core a hv h σ nv hE hV ht cls _ (some (nv + 2 * t)) _ hsat hvars ?_ ?_ ?_ ?_
    · rw [vlexPrem_of_ne ht0]
      simp only [List.map_cons, List.map_nil, lexRenLit_negL, lexRen, List.cons.injEq, neg_inj,
        Nat.cast_inj, and_true] <;> omega
    · intro l hl
      simp only [List.mem_singleton] at hl
      subst hl
      rw [natAbs_neg_natCast]
    · intro ht1
      have hS := hchS ht1
      rw [vlexChClauses_of_ne ht0] at hS
      have hp : (nv + 2 * (t - 1) + 1 + 1 : ℕ) = nv + 2 * t := by omega
      have hD1 : ([-((nv + 2 * t + 1 + 1 : ℕ) : ℤ), ((nv + 2 * t : ℕ) : ℤ)] : List ℤ) =
          ([negL (chvar (v - 1) t), posL (chvar (v - 1) (t - 1))] : SClause n 2).map
            (lexRenLit nv) := by
        simp only [List.map_cons, List.map_nil, lexRenLit_negL, lexRenLit_posL, lexRen, hp]
      have hD3 : ([((nv + 2 * t + 1 + 1 : ℕ) : ℤ), -((nv + 2 * t : ℕ) : ℤ),
            -((nv + 2 * t + 1 : ℕ) : ℤ)] : List ℤ) =
          ([posL (chvar (v - 1) t), negL (chvar (v - 1) (t - 1)), negL (qvar (v - 1) t)] :
            SClause n 2).map (lexRenLit nv) := by
        simp only [List.map_cons, List.map_nil, lexRenLit_negL, lexRenLit_posL, lexRen, hp]
      rw [listSat_cons, listSat_cons, listSat_cons]
      refine ⟨clauseSat_transport (nv := nv) (C := [negL (chvar (v - 1) t), posL (chvar (v - 1) (t - 1))])
          hD1 (hS _ (by simp)) ?_,
        clauseSat_transport (nv := nv) (C := [negL (chvar (v - 1) t), posL (qvar (v - 1) t)])
          rfl (hS _ (by simp)) ?_,
        clauseSat_transport (nv := nv)
          (C := [posL (chvar (v - 1) t), negL (chvar (v - 1) (t - 1)), negL (qvar (v - 1) t)])
          hD3 (hS _ (by simp)) ?_, listSat_nil⟩
      · intro l hl
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact hagC t
        · exact hagC (t - 1)
      · intro l hl
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · exact hagC t
        · exact hagQ t
      · intro l hl
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl
        · exact hagC t
        · exact hagC (t - 1)
        · exact hagQ t
    · intro _ C hC l hl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hC
      rcases hC with rfl | rfl | rfl <;>
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl <;>
        rcases hl with rfl | rfl | rfl <;> simp only [natAbs_neg_natCast, natAbs_natCast'] <;> omega

/-- The fold over the remaining positions preserves the invariant. -/
lemma lexFold_inv (a : EColouring n 2) {v : ℕ} (hv : 1 ≤ v) (h : v - 1 + 1 < n)
    (σ : ℕ → Bool) (nv : ℕ) (hE : EdgeOK a σ nv)
    (hV : lexView a ≤ lexView (actV (vswap n (v - 1) h) a)) :
    ∀ (rest : List (Edge n)) (t : ℕ) (st : List (List ℤ) × Option ℕ × ℕ),
      (∀ i (hi : i < rest.length), ∃ hti : t + i < (movedList (vswap n (v - 1) h)).length,
        rest[i] = (movedList (vswap n (v - 1) h))[t + i]) →
      t + rest.length = (movedList (vswap n (v - 1) h)).length →
      LexInv (extend σ nv (lexVals a v nv)) nv ((movedList (vswap n (v - 1) h)).length - 1) t st →
      LexInv (extend σ nv (lexVals a v nv)) nv ((movedList (vswap n (v - 1) h)).length - 1)
        (t + rest.length)
        (((rest.zipIdx t).map fun p =>
            (p.2, ofEdge p.1, ofEdge (permEdge (vswap n (v - 1) h) p.1))).foldl
          (lexStep n 2 ((movedList (vswap n (v - 1) h)).length - 1)) st)
  | [], t, st, _, _, hinv => by simpa using hinv
  | e :: rest, t, st, hidx, hlen, hinv => by
    simp only [List.zipIdx_cons, List.map_cons, List.foldl_cons, List.length_cons]
    obtain ⟨ht, he⟩ := hidx 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at ht he
    subst he
    have hidx' : ∀ i (hi : i < rest.length),
        ∃ hti : t + 1 + i < (movedList (vswap n (v - 1) h)).length,
          rest[i] = (movedList (vswap n (v - 1) h))[t + 1 + i] := by
      intro i hi
      obtain ⟨h1, h2⟩ := hidx (i + 1) (by simpa using hi)
      refine ⟨by omega, ?_⟩
      have : rest[i] = ((movedList (vswap n (v - 1) h))[t]'ht :: rest)[i + 1] := rfl
      rw [this, h2]
      congr 1; omega
    have := lexFold_inv a hv h σ nv hE hV rest (t + 1) _ hidx' (by simp at hlen; omega)
      (lexStep_inv a hv h σ nv hE hV ht st hinv)
    rw [show t + 1 + rest.length = t + (rest.length + 1) by omega] at this
    exact this

/-- **One transposition's clauses are satisfied** by the extended assignment, with variable
bounds and count monotonicity. -/
theorem lexTransposition_sat (a : EColouring n 2) {v : ℕ} (hv : 1 ≤ v) (h : v - 1 + 1 < n)
    (σ : ℕ → Bool) (nv : ℕ) (hE : EdgeOK a σ nv)
    (hV : lexView a ≤ lexView (actV (vswap n (v - 1) h) a)) :
    ListSat (extend σ nv (lexVals a v nv)) (lexTransposition n 2 v nv).1 ∧
    VarsLe (lexTransposition n 2 v nv).1 (lexTransposition n 2 v nv).2 ∧
    nv ≤ (lexTransposition n 2 v nv).2 := by
  rw [lexTransposition_eq, movedE_eq hv h]
  have hlist : ((((movedList (vswap n (v - 1) h)).map fun e =>
        (ofEdge e, ofEdge (permEdge (vswap n (v - 1) h) e))).zipIdx).map
          fun p => (p.2, p.1.1, p.1.2)) =
      ((movedList (vswap n (v - 1) h)).zipIdx 0).map fun p =>
        (p.2, ofEdge p.1, ofEdge (permEdge (vswap n (v - 1) h) p.1)) := by
    rw [List.zipIdx_map, List.map_map]; rfl
  rw [hlist, List.length_map]
  have hinv := lexFold_inv a hv h σ nv hE hV (movedList (vswap n (v - 1) h)) 0 ([], none, nv)
    (fun i hi => ⟨by simpa using hi, by simp⟩) (by simp)
    ⟨listSat_nil, varsLe_nil, by simp, fun _ => rfl⟩
  rw [Nat.zero_add] at hinv
  rcases hres : (((movedList (vswap n (v - 1) h)).zipIdx 0).map fun p =>
      (p.2, ofEdge p.1, ofEdge (permEdge (vswap n (v - 1) h) p.1))).foldl
        (lexStep n 2 ((movedList (vswap n (v - 1) h)).length - 1)) ([], none, nv) with ⟨cls, eqch, nvc⟩
  rw [hres] at hinv
  obtain ⟨hsat, hvars, hnv, -⟩ := hinv
  simp only at hsat hvars hnv
  refine ⟨hsat, hvars, ?_⟩
  show nv ≤ nvc
  omega


/-! ### Variable bounds of a codegree block -/

lemma natAbs_neg_cgY {nv m i : ℕ} (hi1 : 1 ≤ i) (him : i ≤ m) : (-(cgY nv m i)).natAbs = nv + i := by
  rw [cgY_eq hi1 him]; exact natAbs_neg_natCast _

lemma natAbs_cgReg (nv m k i j : ℕ) : (cgReg nv m k i j).natAbs = nv + m + (i - 1) * k + j := by
  unfold cgReg; exact natAbs_natCast' _

lemma natAbs_neg_cgReg (nv m k i j : ℕ) :
    (-(cgReg nv m k i j)).natAbs = nv + m + (i - 1) * k + j := by
  unfold cgReg; exact natAbs_neg_natCast _

theorem cgBlock_varsLe {k : ℕ} (hk : 0 < k) (S : List ℕ) (hS : S.Sublist (verts n))
    (hm : 2 ≤ (wsOf n S).length) (c : Fin 2) (nv : ℕ) (hnv : n * (n - 1) / 2 * 2 ≤ nv) :
    VarsLe (cgBlock n 2 (c.val + 1) k S nv) (cgStepNv n k S nv) := by
  have hmk : ((wsOf n S).length - 1) * k = ((wsOf n S).length - 2) * k + k := by
    obtain ⟨m', hm'⟩ : ∃ m', (wsOf n S).length = m' + 2 := ⟨(wsOf n S).length - 2, by omega⟩
    rw [hm', Nat.add_sub_cancel, show m' + 2 - 1 = m' + 1 by omega, Nat.succ_mul]
  have hreg : ∀ i j, i + 1 ≤ (wsOf n S).length → j ≤ k →
      nv + (wsOf n S).length + (i - 1) * k + j ≤ cgStepNv n k S nv := by
    intro i j hi hj
    simp only [cgStepNv]
    have : (i - 1) * k ≤ ((wsOf n S).length - 2) * k := Nat.mul_le_mul_right _ (by omega)
    omega
  have hvarU : ∀ u ∈ S, ∀ w ∈ wsOf n S, varU n 2 u w (c.val + 1) ≤ cgStepNv n k S nv := by
    intro u hu w hw
    have hu' := mem_verts.mp (hS.subset hu)
    have hw' := mem_wsOf.mp hw
    have huw : u ≠ w := fun h => hw'.2 (h ▸ hu)
    simp only [cgStepNv]
    exact le_trans (varU_le hu'.1 hu'.2 hw'.1.1 hw'.1.2 huw c) (by omega)
  have hstep : nv + (wsOf n S).length ≤ cgStepNv n k S nv := by simp only [cgStepNv]; omega
  simp only [cgBlock]
  rw [varsLe_append, varsLe_append, varsLe_append]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [varsLe_map]
    intro p hp l hl
    obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    have hi' : i < (wsOf n S).length := by simpa using hi
    rw [List.getElem_zip, List.getElem_range'] at hpi
    subst hpi
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hl
    rcases hl with ⟨u, hu, rfl⟩ | rfl
    · rw [natAbs_neg_natCast]; exact hvarU u hu _ (List.getElem_mem hi')
    · rw [natAbs_natCast']; exact le_trans (by omega) hstep
  · intro C hC l hl
    simp only [List.mem_singleton] at hC
    subst hC
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · rw [natAbs_neg_cgY (m := (wsOf n S).length) (i := 1) (le_refl _) (by omega)]
      exact le_trans (by omega) hstep
    · rw [natAbs_cgReg]; exact hreg 1 1 (by omega) (by omega)
  · rw [varsLe_flatMap]
    intro i hi
    obtain ⟨hi2, him⟩ := mem_range'_mid hi
    rw [varsLe_append, varsLe_append]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro C hC l hl
      simp only [List.mem_singleton] at hC
      subst hC
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · rw [natAbs_neg_cgY (m := (wsOf n S).length) (i := i) (by omega) (by omega)]
        exact le_trans (by omega) hstep
      · rw [natAbs_cgReg]; exact hreg i 1 him (by omega)
    · rw [varsLe_map]
      intro j hj l hl
      rw [List.mem_range'_1] at hj
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · rw [natAbs_neg_cgReg]; exact hreg (i - 1) j (by omega) (by omega)
      · rw [natAbs_cgReg]; exact hreg i j him (by omega)
    · rw [varsLe_map]
      intro j hj l hl
      rw [List.mem_range'_1] at hj
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · rw [natAbs_neg_cgY (m := (wsOf n S).length) (i := i) (by omega) (by omega)]
        exact le_trans (by omega) hstep
      · rw [natAbs_neg_cgReg]; exact hreg (i - 1) (j - 1) (by omega) (by omega)
      · rw [natAbs_cgReg]; exact hreg i j him (by omega)
  · rw [varsLe_map]
    intro i hi l hl
    rw [List.mem_range'_1] at hi
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · rw [natAbs_neg_cgY (m := (wsOf n S).length) (i := i) (by omega) (by omega)]
      exact le_trans (by omega) hstep
    · rw [natAbs_neg_cgReg]; exact hreg (i - 1) k (by omega) (le_refl _)

/-! ### One colour's codegree clauses -/

theorem codegreeColour_sat (a : EColouring n 2) (c : Fin 2) {cN s t : ℕ} (hcN : cN = c.val + 1)
    (hs : s + 2 ≤ n) (ht : 2 ≤ t)
    (hS : ∀ S ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)),
      Sinz.Clauses (codegreeInputs a c S) (Sinz.truthful (k := t - 1) (codegreeInputs a c S)))
    (σ₀ : ℕ → Bool) (nv₀ : ℕ) (hE : EdgeOK a σ₀ nv₀) :
    (codegreeColour n 2 cN s t nv₀).2 = (codegreeAssign a c s t σ₀ nv₀).2 ∧
    EdgeOK a (codegreeAssign a c s t σ₀ nv₀).1 (codegreeAssign a c s t σ₀ nv₀).2 ∧
    ListSat (codegreeAssign a c s t σ₀ nv₀).1 (codegreeColour n 2 cN s t nv₀).1 ∧
    VarsLe (codegreeColour n 2 cN s t nv₀).1 (codegreeColour n 2 cN s t nv₀).2 ∧
    nv₀ ≤ (codegreeColour n 2 cN s t nv₀).2 ∧
    ∀ y ≤ nv₀, (codegreeAssign a c s t σ₀ nv₀).1 y = σ₀ y := by
  rw [codegreeColour_eq_fold]
  unfold codegreeAssign
  refine fold_extend a (combos s (verts n)) (fun S nv => cgBlock n 2 cN (t - 1) S nv)
    (fun S nv => cgStepNv n (t - 1) S nv) (fun S nv => blockVals a c (t - 1) S nv) ?_ ?_
    evarNum_le [] σ₀ nv₀ hE listSat_nil varsLe_nil
  · intro S _ nv; simp only [cgStepNv]; omega
  · intro S hSm σ nv hEσ
    obtain ⟨hsub, hlen⟩ := combos_sublist_length s (verts n) S hSm
    have hm : 2 ≤ (wsOf n S).length := by have := wsOf_length (n := n) hsub; omega
    have hk : 0 < t - 1 := by omega
    have hSinz := hS (SF n S) (Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, by rw [SF_card hsub, hlen]⟩)
    subst hcN
    exact ⟨cgBlock_sat a c hk S hm hSinz σ nv hEσ, cgBlock_varsLe hk S hsub hm c nv hEσ.1⟩

/-! ### All vertex-lex clauses -/

lemma lexStep_nv_le (n r last : ℕ) (st : List (List ℤ) × Option ℕ × ℕ)
    (ie : ℕ × (ℕ × ℕ) × (ℕ × ℕ)) : st.2.2 ≤ (lexStep n r last st ie).2.2 := by
  rcases st with ⟨cls, eqch, nvc⟩
  rcases ie with ⟨t, e, f⟩
  unfold lexStep
  simp only []
  by_cases h : t = last
  · rw [if_pos h]
  · rw [if_neg h]; show nvc ≤ nvc + 1 + 1; omega

lemma foldl_lexStep_nv_le (n r last : ℕ) :
    ∀ (l : List (ℕ × (ℕ × ℕ) × (ℕ × ℕ))) (st : List (List ℤ) × Option ℕ × ℕ),
      st.2.2 ≤ (l.foldl (lexStep n r last) st).2.2
  | [], st => le_refl _
  | ie :: l, st => le_trans (lexStep_nv_le n r last st ie) (foldl_lexStep_nv_le n r last l _)

lemma lexTransposition_nv_le (n r v nv0 : ℕ) : nv0 ≤ (lexTransposition n r v nv0).2 := by
  rw [lexTransposition_eq]
  have := foldl_lexStep_nv_le n r ((movedE n v).length - 1)
    ((movedE n v).zipIdx.map fun p => (p.2, p.1.1, p.1.2)) ([], none, nv0)
  rcases hres : ((movedE n v).zipIdx.map fun p => (p.2, p.1.1, p.1.2)).foldl
      (lexStep n r ((movedE n v).length - 1)) ([], none, nv0) with ⟨cls, eqch, nvc⟩
  rw [hres] at this
  exact this

lemma lexClauses_eq_fold (n r nv0 : ℕ) :
    lexClauses n r nv0 = (List.range' 1 (n - 1)).foldl
      (fun acc v => (acc.1 ++ (lexTransposition n r v acc.2).1, (lexTransposition n r v acc.2).2))
      ([], nv0) := by
  unfold lexClauses
  first
  | rfl
  | (congr 1
     funext acc v
     rcases acc with ⟨cls, nv⟩ <;> (rcases hlt : lexTransposition n r v nv with ⟨c2, nv2⟩ <;> rfl))

theorem lexClauses_sat (a : EColouring n 2)
    (hlead : ∀ τ : Equiv.Perm (Fin n), lexView a ≤ lexView (actV τ a))
    (σ₀ : ℕ → Bool) (nv₀ : ℕ) (hE : EdgeOK a σ₀ nv₀) :
    (lexClauses n 2 nv₀).2 = (lexAssign a σ₀ nv₀).2 ∧
    EdgeOK a (lexAssign a σ₀ nv₀).1 (lexAssign a σ₀ nv₀).2 ∧
    ListSat (lexAssign a σ₀ nv₀).1 (lexClauses n 2 nv₀).1 ∧
    VarsLe (lexClauses n 2 nv₀).1 (lexClauses n 2 nv₀).2 ∧
    nv₀ ≤ (lexClauses n 2 nv₀).2 ∧
    ∀ y ≤ nv₀, (lexAssign a σ₀ nv₀).1 y = σ₀ y := by
  rw [lexClauses_eq_fold]
  unfold lexAssign
  refine fold_extend a (List.range' 1 (n - 1)) (fun v nv => (lexTransposition n 2 v nv).1)
    (fun v nv => (lexTransposition n 2 v nv).2) (fun v nv => lexVals a v nv) ?_ ?_
    evarNum_le [] σ₀ nv₀ hE listSat_nil varsLe_nil
  · intro v _ nv; exact lexTransposition_nv_le n 2 v nv
  · intro v hv σ nv hEσ
    rw [List.mem_range'_1] at hv
    have h : v - 1 + 1 < n := by omega
    have := lexTransposition_sat a (v := v) (by omega) h σ nv hEσ (hlead _)
    exact ⟨this.1, this.2.1⟩

/-! ### The whole encoder -/

/-- **The bridge, concretely.** `bridgeAssign a` satisfies every clause of `encodeBip`
whenever `a` is a lex-leader whose truthful codegree counters satisfy `Sinz.Clauses` at
bounds `t₀-1`, `t₁-1` (the conclusion of `EncodeSoundFor`). -/
theorem bridgeAssign_sat (a : EColouring n 2) {s₀ t₀ s₁ t₁ : ℕ}
    (hs₀ : s₀ + 2 ≤ n) (hs₁ : s₁ + 2 ≤ n) (ht₀ : 2 ≤ t₀) (ht₁ : 2 ≤ t₁)
    (hlead : ∀ τ : Equiv.Perm (Fin n), lexView a ≤ lexView (actV τ a))
    (h0 : ∀ S ∈ Finset.powersetCard s₀ (Finset.univ : Finset (Fin n)),
      Sinz.Clauses (codegreeInputs a 0 S) (Sinz.truthful (k := t₀ - 1) (codegreeInputs a 0 S)))
    (h1 : ∀ S ∈ Finset.powersetCard s₁ (Finset.univ : Finset (Fin n)),
      Sinz.Clauses (codegreeInputs a 1 S) (Sinz.truthful (k := t₁ - 1) (codegreeInputs a 1 S))) :
    ListSat (bridgeAssign a s₀ t₀ s₁ t₁) (encodeBip n s₀ t₀ s₁ t₁) := by
  have R0 := codegreeColour_sat a 0 (cN := 1) rfl hs₀ ht₀ h0 (edgeAssign a)
    (n * (n - 1) / 2 * 2) (edgeOK_init a)
  set m1 := codegreeAssign a 0 s₀ t₀ (edgeAssign a) (n * (n - 1) / 2 * 2) with hm1
  have R1 := codegreeColour_sat a 1 (cN := 2) rfl hs₁ ht₁ h1 m1.1 m1.2 R0.2.1
  set m2 := codegreeAssign a 1 s₁ t₁ m1.1 m1.2 with hm2
  have R2 := lexClauses_sat a hlead m2.1 m2.2 R1.2.1
  show ListSat (lexAssign a m2.1 m2.2).1 (encodeBip n s₀ t₀ s₁ t₁)
  unfold encodeBip
  simp only []
  rcases hc0 : codegreeColour n 2 1 s₀ t₀ (n * (n - 1) / 2 * 2) with ⟨cg0, nv1⟩
  rw [hc0] at R0
  obtain ⟨hnv1, -, hs0, hv0, -, -⟩ := R0
  simp only at hnv1 hs0 hv0
  rw [hnv1]
  rcases hc1 : codegreeColour n 2 2 s₁ t₁ m1.2 with ⟨cg1, nv2⟩
  rw [hc1] at R1
  obtain ⟨hnv2, -, hs1, hv1, hle1, hag1⟩ := R1
  simp only at hnv2 hs1 hv1 hle1
  rw [hnv2]
  rcases hl : lexClauses n 2 m2.2 with ⟨lex, nvl⟩
  rw [hl] at R2
  obtain ⟨-, hEf, hsl, -, -, hagl⟩ := R2
  simp only at hsl
  simp only []
  rw [listSat_append, listSat_append, listSat_append]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hsl⟩
  · exact edgeClauses_sat a _ hEf.2
  · refine listSat_of_agree hs0 hv0 (fun x hx => ?_)
    have hle1' : nv1 ≤ m2.2 := by rw [hnv1, ← hnv2]; exact hle1
    have hx1 : x ≤ m1.2 := by rw [← hnv1]; exact hx
    rw [hagl x (le_trans hx hle1'), hag1 x hx1]
  · exact listSat_of_agree hs1 hv1 (fun x hx => hagl x (by rw [← hnv2]; exact hx))

/-- **The generic bridge.** From the conclusion of `SB.Portfolio.EncodeSoundFor n s₀ t₀ s₁ t₁`
(a good lex-leader with truthful counters) to a model of the encoder's clause list. -/
theorem bip_bridge {s₀ t₀ s₁ t₁ : ℕ} (hs₀ : s₀ + 2 ≤ n) (hs₁ : s₁ + 2 ≤ n)
    (ht₀ : 2 ≤ t₀) (ht₁ : 2 ≤ t₁)
    (h : ∃ a : EColouring n 2,
      (NoKst a 0 s₀ t₀ ∧ NoKst a 1 s₁ t₁) ∧
      (∀ τ : Equiv.Perm (Fin n), lexView a ≤ lexView (actV τ a)) ∧
      (∀ S ∈ Finset.powersetCard s₀ (Finset.univ : Finset (Fin n)),
        Sinz.Clauses (codegreeInputs a 0 S)
          (Sinz.truthful (k := t₀ - 1) (codegreeInputs a 0 S))) ∧
      (∀ S ∈ Finset.powersetCard s₁ (Finset.univ : Finset (Fin n)),
        Sinz.Clauses (codegreeInputs a 1 S)
          (Sinz.truthful (k := t₁ - 1) (codegreeInputs a 1 S)))) :
    ∃ σ : ℕ → Bool, ListSat σ (encodeBip n s₀ t₀ s₁ t₁) := by
  obtain ⟨a, -, hlead, h0, h1⟩ := h
  exact ⟨bridgeAssign a s₀ t₀ s₁ t₁, bridgeAssign_sat a hs₀ hs₁ ht₀ ht₁ hlead h0 h1⟩

/-- **Refuting `encodeBip` refutes every good colouring.** -/
theorem no_colouring_of_encodeBip_unsat {s₀ t₀ s₁ t₁ : ℕ} (hs₀ : s₀ + 2 ≤ n) (hs₁ : s₁ + 2 ≤ n)
    (ht₀ : 2 ≤ t₀) (ht₁ : 2 ≤ t₁)
    (hunsat : ∀ σ : ℕ → Bool, ¬ ListSat σ (encodeBip n s₀ t₀ s₁ t₁)) :
    ¬ ∃ a : EColouring n 2, NoKst a 0 s₀ t₀ ∧ NoKst a 1 s₁ t₁ := by
  intro hsat
  have hes : SB.Portfolio.EncodeSoundFor n s₀ t₀ s₁ t₁ :=
    SB.Portfolio.encode_sound_bip s₀ t₀ s₁ t₁ ht₀ ht₁
  unfold SB.Portfolio.EncodeSoundFor at hes
  obtain ⟨σ, hσ⟩ := bip_bridge hs₀ hs₁ ht₀ ht₁ (hes hsat)
  exact hunsat σ hσ

/-! ### Stage-D transfer: `CNF.Unsat` of the DIMACS conversion refutes `ListSat`

`dimacsLitV`/`toCNFV` are verbatim copies of `LRATCatcher.dimacsLit` and
`LRATCatcher.Encoder.toCNF`; the composing file identifies them by `rfl`. -/

/-- Copy of `LRATCatcher.dimacsLit`: variable `|l| - 1` (0-indexed), polarity `l > 0`. -/
def dimacsLitV (l : Int) : Nat × Bool := (l.natAbs - 1, decide (0 < l))

/-- Copy of `LRATCatcher.Encoder.toCNF`. -/
def toCNFV (cs : List (List Int)) : Std.Sat.CNF Nat :=
  { clauses := (cs.map fun c => c.map dimacsLitV).toArray }

theorem toCNFV_eval_of_listSat (σ : ℕ → Bool) (cs : List (List ℤ)) (h : ListSat σ cs) :
    Std.Sat.CNF.eval (fun v => σ (v + 1)) (toCNFV cs) = true := by
  unfold toCNFV Std.Sat.CNF.eval
  rw [Array.all_eq_true']
  intro c hc
  have hc' : c ∈ cs.map (fun c => c.map dimacsLitV) := by simpa using hc
  rw [List.mem_map] at hc'
  obtain ⟨cl, hcl, rfl⟩ := hc'
  obtain ⟨l, hl, hl0, hσ⟩ := h cl hcl
  unfold Std.Sat.CNF.Clause.eval
  rw [List.any_eq_true]
  refine ⟨dimacsLitV l, List.mem_map.mpr ⟨l, hl, rfl⟩, ?_⟩
  have hpos : 0 < l.natAbs := Int.natAbs_pos.mpr hl0
  simp only [dimacsLitV, Nat.sub_add_cancel hpos, hσ, beq_self_eq_true]

theorem not_listSat_of_toCNFV_unsat (cs : List (List ℤ)) (hu : (toCNFV cs).Unsat) :
    ∀ σ : ℕ → Bool, ¬ ListSat σ cs := by
  intro σ hσ
  have h1 := hu (fun v => σ (v + 1))
  rw [toCNFV_eval_of_listSat σ cs hσ] at h1
  exact Bool.noConfusion h1

/-- **Stage D shape.** `CNF.Unsat (toCNFV (encodeBip n s₀ t₀ s₁ t₁))` refutes every good
colouring of `K_n`. The composing file supplies the hypothesis from `encoded_unsat`. -/
theorem no_colouring_of_toCNFV_unsat {s₀ t₀ s₁ t₁ : ℕ} (hs₀ : s₀ + 2 ≤ n) (hs₁ : s₁ + 2 ≤ n)
    (ht₀ : 2 ≤ t₀) (ht₁ : 2 ≤ t₁) (hu : (toCNFV (encodeBip n s₀ t₀ s₁ t₁)).Unsat) :
    ¬ ∃ a : EColouring n 2, NoKst a 0 s₀ t₀ ∧ NoKst a 1 s₁ t₁ :=
  no_colouring_of_encodeBip_unsat hs₀ hs₁ ht₀ ht₁ (not_listSat_of_toCNFV_unsat _ hu)

end SB.BipBridge

#print axioms SB.BipBridge.bridgeAssign_sat
#print axioms SB.BipBridge.bip_bridge
#print axioms SB.BipBridge.no_colouring_of_encodeBip_unsat
#print axioms SB.BipBridge.no_colouring_of_toCNFV_unsat
