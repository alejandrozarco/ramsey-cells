/-
The emitted symmetry-breaking clause families of `gen_ramsey.py`
(`--vertex-lex` and `--swap-break`), with auxiliary variables, and the
soundness deliverable: the canonical auxiliary extension of a lex-leader's
assignment satisfies every emitted SB clause.

Faithfulness conventions (binding spec = gen_ramsey.py; aux-variable style
follows the order-encoding-with-aux-variables approach of arXiv:2511.16637,
whose eq-chain variables carry definitional (bidirectional) semantics, as
the Python's do):

* Vertices: Python is 1-based, here 0-based (`Fin n`).  Python's adjacent
  transposition `v ↔ v+1` (v ∈ 1..n-1) is `vswap n (v-1)` here; the
  `blocks` parameter is the 0-based list of allowed transpositions (Python
  computes it from `--cube`; e.g. no cube ⇒ `[0, …, n-2]`).
* Colours: Python colour `c ∈ 1..r` is `(c-1 : Fin r)`; the value order
  1 < 2 < … matches the `Fin r` order.
* Edge-colour variable `var(e, c)` is `Sum.inl (e, c)`.  Python's
  sequentially numbered aux integers are renamed structurally:
  - vertex-lex `q` at moved-position `t` (0-based, as in the Python
    `enumerate`) of transposition `v` ↦ `Aux.vq v t`;
  - vertex-lex `newch` created at position `t` ↦ `Aux.vch v t`
    (so the premise at position `t+1` is `¬ Aux.vch v t`);
  - swap-break `eq[t]` (t = 1-based prefix length, as in the Python) of
    the p-th adjacent chain pair (0-based) ↦ `Aux.ceq p t`.
  This renaming is a bijection on the aux variables actually mentioned in
  clauses, so the clause sets agree up to it.
* The moved-edge list of a transposition is the strictly sorted list of
  edges `e` with `σ·e ≠ e` in the row-major edge order — exactly the
  Python's `moved` (global edge order restricted to moved edges), with
  `f = permEdge τ e` the paired image edge.
* Under these conventions each family's clause stream is identical to the
  Python's — same clause order, same literal order inside each clause
  (checked against gen_ramsey.py output on small instances; the theorem
  concatenates `vertexLexClauses ++ chainClauses` while the Python emits
  swap-break before vertex-lex, which is immaterial).  Sole deviation: for
  parameters where the Python would crash or never emit (`n ≤ 1` row-1
  chain; an out-of-range `v` in `blocks`; the never-emitted
  `ceqDefClauses _ 0`) we emit no clauses.

The deliverable `sb_clauses_satisfiable_of_leader` constructs the
canonical assignment explicitly: edge variables from `ofColouring a`,
`q`-variables decide value-equality at their position, chain variables
decide prefix equality.  The vertex-lex comparison clauses are discharged
with the first-difference lemma `Pi.apply_le_of_toLex` (the `Pi.Lex`
counterpart of SBChain's technique), the chain clauses likewise.
-/
import Mathlib
import Sbsound.SBCore
import Sbsound.SBGraph
import Sbsound.SBKeystone
import Sbsound.SBChain
import Sbsound.SBEncode

namespace SB

variable {n r : ℕ}

/-! ### Variables, literals, clauses over edge-colour ⊕ auxiliary variables -/

/-- Auxiliary-variable names for the two SB clause families. -/
inductive Aux : Type
  /-- Vertex-lex value-equality variable (`q`) of transposition `v` at
  moved-position `t` (0-based). -/
  | vq (v t : ℕ)
  /-- Vertex-lex eq-chain variable (`newch`) of transposition `v` created at
  moved-position `t` (0-based): positions `0..t` all equal. -/
  | vch (v t : ℕ)
  /-- Swap-break eq-chain variable (`eq[t]`) of the `p`-th adjacent chain
  pair: the first `t` row-1 positions are equal (`t` 1-based). -/
  | ceq (p t : ℕ)
  deriving DecidableEq

/-- Extended variable type: edge-colour variables ⊕ auxiliary variables. -/
abbrev SVar (n r : ℕ) := (Edge n × Fin r) ⊕ Aux

/-- Assignment over the extended variables. -/
abbrev SAssign (n r : ℕ) := SVar n r → Bool

/-- Literal over the extended variables (`true` = positive). -/
abbrev SLit (n r : ℕ) := SVar n r × Bool

/-- Clause over the extended variables. -/
abbrev SClause (n r : ℕ) := List (SLit n r)

/-- The edge-colour variable `var(e, c)`. -/
abbrev evar (e : Edge n) (c : Fin r) : SVar n r := Sum.inl (e, c)

/-- The vertex-lex `q` variable. -/
abbrev qvar (v t : ℕ) : SVar n r := Sum.inr (Aux.vq v t)

/-- The vertex-lex chain variable. -/
abbrev chvar (v t : ℕ) : SVar n r := Sum.inr (Aux.vch v t)

/-- The swap-break eq-chain variable. -/
abbrev ceqvar (p t : ℕ) : SVar n r := Sum.inr (Aux.ceq p t)

/-- Positive literal. -/
abbrev posL (x : SVar n r) : SLit n r := (x, true)

/-- Negative literal. -/
abbrev negL (x : SVar n r) : SLit n r := (x, false)

/-- Literal evaluation (mirrors `evalLit` of SBEncode). -/
def evalSLit (β : SAssign n r) : SLit n r → Bool
  | (x, true) => β x
  | (x, false) => !β x

@[simp] lemma evalSLit_pos (β : SAssign n r) (x : SVar n r) :
    evalSLit β (posL x) = β x := rfl

@[simp] lemma evalSLit_neg (β : SAssign n r) (x : SVar n r) :
    evalSLit β (negL x) = !β x := rfl

/-- A clause is satisfied when some literal evaluates to `true`. -/
def satSClause (β : SAssign n r) (C : SClause n r) : Bool := C.any (evalSLit β)

/-- A CNF is satisfied when every clause is. -/
def satSCNF (β : SAssign n r) (F : List (SClause n r)) : Prop :=
  ∀ C ∈ F, satSClause β C = true

lemma satSCNF_append {β : SAssign n r} {F₁ F₂ : List (SClause n r)} :
    satSCNF β (F₁ ++ F₂) ↔ satSCNF β F₁ ∧ satSCNF β F₂ := by
  simp [satSCNF, List.mem_append, or_imp, forall_and]

lemma satSClause_of_mem {β : SAssign n r} {C : SClause n r} {l : SLit n r}
    (hl : l ∈ C) (he : evalSLit β l = true) : satSClause β C = true :=
  List.any_eq_true.mpr ⟨l, hl, he⟩

/-- Compatibility with SBEncode: embed a base (edge-variable-only) clause. -/
def liftClause (C : Clause n r) : SClause n r := C.map fun l => (Sum.inl l.1, l.2)

/-- A lifted base clause is satisfied by `β` iff the base clause is satisfied
by `β`'s edge-variable restriction. -/
lemma satSClause_liftClause (β : SAssign n r) (C : Clause n r) :
    satSClause β (liftClause C) = satClause (fun e c => β (evar e c)) C := by
  rw [satSClause, satClause, liftClause, List.any_map]
  congr 1
  funext l
  rcases l with ⟨⟨e, c⟩, b⟩
  cases b <;> rfl

/-- `β` agrees with `ofColouring a` on the edge-colour variables. -/
def restrictsTo (β : SAssign n r) (a : EColouring n r) : Prop :=
  ∀ e c, β (evar e c) = ofColouring a e c

/-- Membership in an explicit two-element clause list. -/
private lemma mem_pair {α : Type*} {x a b : α} (h : x ∈ [a, b]) : x = a ∨ x = b := by
  simpa using h

/-- Membership in an explicit three-element clause list. -/
private lemma mem_triple {α : Type*} {x a b c : α} (h : x ∈ [a, b, c]) :
    x = a ∨ x = b ∨ x = c := by
  simpa using h

/-- Membership in an explicit four-element clause list. -/
private lemma mem_quad {α : Type*} {x a b c d : α} (h : x ∈ [a, b, c, d]) :
    x = a ∨ x = b ∨ x = c ∨ x = d := by
  simpa using h

/-- Membership in an explicit five-element clause list. -/
private lemma mem_quint {α : Type*} {x a b c d e : α} (h : x ∈ [a, b, c, d, e]) :
    x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
  simpa using h

/-! ### Sorted edge lists -/

/-- The image of an edge under a vertex permutation (the body of `actV`). -/
def permEdge (τ : Equiv.Perm (Fin n)) (e : Edge n) : Edge n :=
  mkEdge (τ (ofLex e.val).1) (τ (ofLex e.val).2) (τ.injective.ne (ne_of_lt e.prop))

lemma actV_apply (τ : Equiv.Perm (Fin n)) (a : EColouring n r) (e : Edge n) :
    actV τ a e = a (permEdge τ e) := rfl

/-- The moved edges of a vertex permutation, in the row-major edge order:
the Python's `moved` list (each entry paired there with `permEdge τ e`). -/
def movedList (τ : Equiv.Perm (Fin n)) : List (Edge n) :=
  (Finset.univ.filter fun e : Edge n => permEdge τ e ≠ e).sort (· ≤ ·)

lemma mem_movedList {τ : Equiv.Perm (Fin n)} {e : Edge n} :
    e ∈ movedList τ ↔ permEdge τ e ≠ e := by
  simp [movedList]

lemma movedList_sortedLT (τ : Equiv.Perm (Fin n)) : (movedList τ).SortedLT :=
  Finset.sortedLT_sort _

/-- The row-1 edges in the row-major order: the Python's `seq` positions
(edges `(0, j)`, `j = 1..n-1`, ordered by `j`). -/
def row1List (n : ℕ) : List (Row1 n) := (Finset.univ : Finset (Row1 n)).sort (· ≤ ·)

lemma mem_row1List (j : Row1 n) : j ∈ row1List n := by
  simp [row1List]

lemma row1List_sortedLT (n : ℕ) : (row1List n).SortedLT :=
  Finset.sortedLT_sort _

/-- In a strictly sorted list, any member below the `t`-th element lies in the
length-`t` prefix. -/
private lemma mem_take_of_lt {α : Type*} [Preorder α] {l : List α} (hl : l.SortedLT)
    {t : ℕ} (ht : t < l.length) {x : α} (hx : x ∈ l) (hlt : x < l[t]'ht) :
    x ∈ l.take t := by
  obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hx
  have hst : s < t := by
    rcases Nat.lt_or_ge s t with h | h
    · exact h
    · rcases Nat.eq_or_lt_of_le h with rfl | h'
      · exact absurd hlt (lt_irrefl _)
      · exact absurd hlt (asymm (hl.getElem_lt_getElem_of_lt h'))
  have hs' : s < (l.take t).length := by
    rw [List.length_take]; omega
  have hge : (l.take t)[s]'hs' = l[s]'hs := List.getElem_take
  exact hge ▸ List.getElem_mem hs'

/-- The adjacent vertex transposition `v ↔ v+1` (0-based). -/
def vswap (n : ℕ) (v : ℕ) (h : v + 1 < n) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨v, Nat.lt_of_succ_lt h⟩ ⟨v + 1, h⟩

/-! ### The vertex-lex clause family (`--vertex-lex`) -/

/-- Premise literals of the comparison at moved-position `t`:
empty at `t = 0`, else `¬ chvar v (t-1)` (Python's `prem`). -/
def vlexPrem (v t : ℕ) : List (SLit n r) :=
  match t with
  | 0 => []
  | t + 1 => [negL (chvar v t)]

/-- Comparison clauses at moved-position `t` with pair `(e, f)`: under prefix
equality, forbid `val(e) = ce > cf = val(f)`
(Python: `prem + [-var(e, ce), -var(f, cf)]` for `cf < ce`). -/
def vlexCmpClauses (v t : ℕ) (e f : Edge n) : List (SClause n r) :=
  (List.finRange r).flatMap fun cf =>
    ((List.finRange r).filter fun ce => decide (cf < ce)).map fun ce =>
      vlexPrem v t ++ [negL (evar e ce), negL (evar f cf)]

/-- Definitional clauses of `qvar v t ↔ (val(e) = val(f))`
(Python: `[-q, -var(e,c), var(f,c)]` and `[q, -var(e,c), -var(f,c)]`). -/
def vlexQClauses (v t : ℕ) (e f : Edge n) : List (SClause n r) :=
  (List.finRange r).flatMap fun c =>
    [ [negL (qvar v t), negL (evar e c), posL (evar f c)],
      [posL (qvar v t), negL (evar e c), negL (evar f c)] ]

/-- Definitional clauses of the eq-chain variable created at position `t`:
`chvar v 0 ↔ qvar v 0`, and for `t ≥ 1`
`chvar v t ↔ chvar v (t-1) ∧ qvar v t` (Python's `newch` clauses). -/
def vlexChClauses (v t : ℕ) : List (SClause n r) :=
  match t with
  | 0 =>
    [ [negL (chvar v 0), posL (qvar v 0)],
      [posL (chvar v 0), negL (qvar v 0)] ]
  | t + 1 =>
    [ [negL (chvar v (t + 1)), posL (chvar v t)],
      [negL (chvar v (t + 1)), posL (qvar v (t + 1))],
      [posL (chvar v (t + 1)), negL (chvar v t), negL (qvar v (t + 1))] ]

/-- All vertex-lex clauses of one transposition: per moved-position `t`, the
comparison clauses, plus (except at the last position) the `q` and chain
definitional clauses — exactly the Python's per-transposition loop. -/
def transpositionClauses (τ : Equiv.Perm (Fin n)) (v : ℕ) : List (SClause n r) :=
  (List.finRange (movedList τ).length).flatMap fun t =>
    vlexCmpClauses v t.val ((movedList τ)[t.val]'t.isLt)
        (permEdge τ ((movedList τ)[t.val]'t.isLt)) ++
      if t.val + 1 < (movedList τ).length then
        vlexQClauses v t.val ((movedList τ)[t.val]'t.isLt)
            (permEdge τ ((movedList τ)[t.val]'t.isLt)) ++
          vlexChClauses v t.val
      else []

/-- The `--vertex-lex` clause family over the allowed transpositions. -/
def vertexLexClauses (n r : ℕ) (blocks : List ℕ) : List (SClause n r) :=
  blocks.flatMap fun v =>
    if h : v + 1 < n then transpositionClauses (vswap n v h) v else []

/-! ### The swap-break chain clause family (`--swap-break`) -/

/-- Definitional clauses of `ceqvar p t` at prefix length `t ≥ 1`, where `E`
is the `(t-1)`-th row-1 edge (the last position of the prefix):
`t = 1`: `ceq ↔ (var(E,c1) = var(E,c2))`;
`t ≥ 2`: `ceq ↔ ceq' ∧ (var(E,c1) = var(E,c2))` — the Python's `eq_t`
clauses, literal for literal.  (`t = 0` is never emitted.) -/
def ceqDefClauses (p t : ℕ) (E : Edge n) (c1 c2 : Fin r) : List (SClause n r) :=
  match t with
  | 0 => []
  | 1 =>
    [ [negL (ceqvar p 1), negL (evar E c1), posL (evar E c2)],
      [negL (ceqvar p 1), posL (evar E c1), negL (evar E c2)],
      [posL (ceqvar p 1), posL (evar E c1), posL (evar E c2)],
      [posL (ceqvar p 1), negL (evar E c1), negL (evar E c2)] ]
  | t + 2 =>
    [ [negL (ceqvar p (t + 2)), posL (ceqvar p (t + 1))],
      [negL (ceqvar p (t + 2)), negL (evar E c1), posL (evar E c2)],
      [negL (ceqvar p (t + 2)), posL (evar E c1), negL (evar E c2)],
      [posL (ceqvar p (t + 2)), negL (ceqvar p (t + 1)), posL (evar E c1), posL (evar E c2)],
      [posL (ceqvar p (t + 2)), negL (ceqvar p (t + 1)), negL (evar E c1), negL (evar E c2)] ]

/-- Row-1 lex clauses of the `p`-th adjacent chain pair `(c1, c2)`:
`(var((0,j), c1))_j ≥lex (var((0,j), c2))_j` with the eq-chain aux —
first-position clause `[-b1, a1]`, then per `t ≥ 1` the `eq`-definitional
clauses and the step clause `[-eq_t, -b_{t+1}, a_{t+1}]`, as in the Python. -/
def chainPairClauses (p : ℕ) (c1 c2 : Fin r) : List (SClause n r) :=
  (if h : 0 < (row1List n).length then
    [[negL (evar ((row1List n)[0]'h).val c2), posL (evar ((row1List n)[0]'h).val c1)]]
  else []) ++
  (List.finRange (row1List n).length).flatMap fun t =>
    if h1 : 1 ≤ t.val then
      ceqDefClauses p t.val ((row1List n)[t.val - 1]'(by have := t.isLt; omega)).val c1 c2 ++
        [[negL (ceqvar p t.val), negL (evar ((row1List n)[t.val]'t.isLt).val c2),
          posL (evar ((row1List n)[t.val]'t.isLt).val c1)]]
    else []

/-- The `--swap-break` clause family: row-1 lex constraints for each adjacent
pair of the colour chain. -/
def chainClauses (n r : ℕ) (chain : List (Fin r)) : List (SClause n r) :=
  (List.finRange (chain.length - 1)).flatMap fun p =>
    chainPairClauses p.val (chain[p.val]'(by have := p.isLt; omega))
      (chain[p.val + 1]'(by have := p.isLt; omega))

/-! ### The canonical assignment -/

/-- The canonical extension of `ofColouring a`: `q`-variables decide value
equality at their moved-position, vertex chain variables decide prefix
equality through their position, swap-break chain variables decide row-1
indicator prefix equality.  (Out-of-range aux names are unconstrained;
we set them `true`.) -/
def canonAssign (a : EColouring n r) (chain : List (Fin r)) : SAssign n r
  | Sum.inl (e, c) => decide (a e = c)
  | Sum.inr (Aux.vq v t) =>
    if h : v + 1 < n then
      if ht : t < (movedList (vswap n v h)).length then
        decide (a ((movedList (vswap n v h))[t]'ht) =
          a (permEdge (vswap n v h) ((movedList (vswap n v h))[t]'ht)))
      else true
    else true
  | Sum.inr (Aux.vch v t) =>
    if h : v + 1 < n then
      decide (∀ e ∈ (movedList (vswap n v h)).take (t + 1),
        a e = a (permEdge (vswap n v h) e))
    else true
  | Sum.inr (Aux.ceq p t) =>
    if hp : p + 1 < chain.length then
      decide (∀ j ∈ (row1List n).take t,
        decide (a j.val = chain[p]'(Nat.lt_of_succ_lt hp)) =
          decide (a j.val = chain[p + 1]'hp))
    else true

lemma canonAssign_vq (a : EColouring n r) (chain : List (Fin r)) {v t : ℕ}
    (h : v + 1 < n) (ht : t < (movedList (vswap n v h)).length) :
    canonAssign a chain (qvar v t) =
      decide (a ((movedList (vswap n v h))[t]'ht) =
        a (permEdge (vswap n v h) ((movedList (vswap n v h))[t]'ht))) := by
  simp only [canonAssign]
  rw [dif_pos h, dif_pos ht]

lemma canonAssign_vch (a : EColouring n r) (chain : List (Fin r)) {v : ℕ}
    (h : v + 1 < n) (t : ℕ) :
    canonAssign a chain (chvar v t) =
      decide (∀ e ∈ (movedList (vswap n v h)).take (t + 1),
        a e = a (permEdge (vswap n v h) e)) := by
  simp only [canonAssign]
  rw [dif_pos h]

lemma canonAssign_ceq (a : EColouring n r) (chain : List (Fin r)) {p : ℕ}
    (hp : p + 1 < chain.length) (t : ℕ) :
    canonAssign a chain (ceqvar p t) =
      decide (∀ j ∈ (row1List n).take t,
        decide (a j.val = chain[p]'(Nat.lt_of_succ_lt hp)) =
          decide (a j.val = chain[p + 1]'hp)) := by
  simp only [canonAssign]
  rw [dif_pos hp]

/-! ### Satisfaction of the vertex-lex family by a lex-leader -/

/-- Comparison clauses at position `t` are satisfied: if the prefix-equality
premise bites, the leader property forces `val(e_t) ≤ val(f_t)` at the first
possible difference (`Pi.apply_le_of_toLex`). -/
lemma sat_vlexCmp (a : EColouring n r) (τ : Equiv.Perm (Fin n)) (v : ℕ) (β : SAssign n r)
    (hβe : ∀ e c, β (evar e c) = decide (a e = c))
    (hβch : ∀ s, β (chvar v s) =
      decide (∀ e ∈ (movedList τ).take (s + 1), a e = a (permEdge τ e)))
    (hV : lexView a ≤ lexView (actV τ a))
    {t : ℕ} (ht : t < (movedList τ).length) {C : SClause n r}
    (hC : C ∈ vlexCmpClauses v t ((movedList τ)[t]'ht) (permEdge τ ((movedList τ)[t]'ht))) :
    satSClause β C = true := by
  simp only [vlexCmpClauses, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_finRange, true_and, decide_eq_true_eq] at hC
  obtain ⟨cf, ce, hlt, rfl⟩ := hC
  by_cases hpre : ∀ e ∈ (movedList τ).take t, a e = a (permEdge τ e)
  · -- the premise cannot help; the leader property decides the value literals
    have hle : a ((movedList τ)[t]'ht) ≤ a (permEdge τ ((movedList τ)[t]'ht)) := by
      have h2 : ∀ e, e < (movedList τ)[t]'ht → a e = actV τ a e := by
        intro e he
        by_cases hm : permEdge τ e = e
        · change a e = a (permEdge τ e)
          rw [hm]
        · exact hpre e (mem_take_of_lt (movedList_sortedLT τ) ht (mem_movedList.mpr hm) he)
      exact Pi.apply_le_of_toLex hV h2
    by_cases hce : a ((movedList τ)[t]'ht) = ce
    · have hnf : a (permEdge τ ((movedList τ)[t]'ht)) ≠ cf := by
        intro hcf
        rw [hce, hcf] at hle
        exact absurd hle (not_le.mpr hlt)
      exact satSClause_of_mem (l := negL (evar (permEdge τ ((movedList τ)[t]'ht)) cf))
        (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false hnf]; rfl)
    · exact satSClause_of_mem (l := negL (evar ((movedList τ)[t]'ht) ce))
        (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false hce]; rfl)
  · -- the premise literal is true
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hpre (by simp)
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    exact satSClause_of_mem (l := negL (chvar v s))
      (by simp [vlexPrem]) (by rw [evalSLit_neg, hβch, decide_eq_false hpre]; rfl)

/-- The `q`-definitional clauses are satisfied by the canonical values. -/
lemma sat_vlexQ (a : EColouring n r) (τ : Equiv.Perm (Fin n)) (v : ℕ) (β : SAssign n r)
    (hβe : ∀ e c, β (evar e c) = decide (a e = c))
    {t : ℕ} (ht : t < (movedList τ).length)
    (hβq : β (qvar v t) = decide (a ((movedList τ)[t]'ht) =
      a (permEdge τ ((movedList τ)[t]'ht))))
    {C : SClause n r}
    (hC : C ∈ vlexQClauses v t ((movedList τ)[t]'ht) (permEdge τ ((movedList τ)[t]'ht))) :
    satSClause β C = true := by
  simp only [vlexQClauses, List.mem_flatMap, List.mem_finRange, true_and] at hC
  obtain ⟨c, hC⟩ := hC
  rcases mem_pair hC with rfl | rfl
  · -- q → (var(e,c) → var(f,c))
    by_cases h1 : a ((movedList τ)[t]'ht) = c
    · by_cases h2 : a ((movedList τ)[t]'ht) = a (permEdge τ ((movedList τ)[t]'ht))
      · have h3 : a (permEdge τ ((movedList τ)[t]'ht)) = c := h2 ▸ h1
        exact satSClause_of_mem (l := posL (evar (permEdge τ ((movedList τ)[t]'ht)) c))
          (by simp) (by rw [evalSLit_pos, hβe]; exact decide_eq_true h3)
      · exact satSClause_of_mem (l := negL (qvar v t))
          (by simp) (by rw [evalSLit_neg, hβq, decide_eq_false h2]; rfl)
    · exact satSClause_of_mem (l := negL (evar ((movedList τ)[t]'ht) c))
        (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false h1]; rfl)
  · -- var(e,c) ∧ var(f,c) → q
    by_cases h1 : a ((movedList τ)[t]'ht) = c
    · by_cases h2 : a (permEdge τ ((movedList τ)[t]'ht)) = c
      · exact satSClause_of_mem (l := posL (qvar v t))
          (by simp) (by rw [evalSLit_pos, hβq]; exact decide_eq_true (h1.trans h2.symm))
      · exact satSClause_of_mem (l := negL (evar (permEdge τ ((movedList τ)[t]'ht)) c))
          (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false h2]; rfl)
    · exact satSClause_of_mem (l := negL (evar ((movedList τ)[t]'ht) c))
        (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false h1]; rfl)

/-- The chain-definitional clauses are satisfied by the canonical values. -/
lemma sat_vlexCh (a : EColouring n r) (τ : Equiv.Perm (Fin n)) (v : ℕ) (β : SAssign n r)
    {t : ℕ} (ht1 : t + 1 < (movedList τ).length)
    (hβq : β (qvar v t) = decide (a ((movedList τ)[t]'(Nat.lt_of_succ_lt ht1)) =
      a (permEdge τ ((movedList τ)[t]'(Nat.lt_of_succ_lt ht1)))))
    (hβch : ∀ s, β (chvar v s) =
      decide (∀ e ∈ (movedList τ).take (s + 1), a e = a (permEdge τ e)))
    {C : SClause n r} (hC : C ∈ vlexChClauses v t) :
    satSClause β C = true := by
  have ht : t < (movedList τ).length := Nat.lt_of_succ_lt ht1
  have htake : (movedList τ).take (t + 1) =
      (movedList τ).take t ++ [(movedList τ)[t]'ht] := by
    rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some]
  have hsplit : (∀ e ∈ (movedList τ).take (t + 1), a e = a (permEdge τ e)) ↔
      ((∀ e ∈ (movedList τ).take t, a e = a (permEdge τ e)) ∧
        a ((movedList τ)[t]'ht) = a (permEdge τ ((movedList τ)[t]'ht))) := by
    rw [htake, List.forall_mem_append, List.forall_mem_singleton]
  rcases t with - | s
  · -- t = 0 : chvar v 0 ↔ qvar v 0
    have hch0 : β (chvar v 0) = β (qvar v 0) := by
      rw [hβch 0, hβq]
      apply decide_eq_decide.mpr
      rw [hsplit]
      simp
    rcases mem_pair (show C ∈ [_, _] from hC) with rfl | rfl
    · cases hq : β (qvar v 0)
      · exact satSClause_of_mem (l := negL (chvar v 0)) (by simp)
          (by rw [evalSLit_neg, hch0, hq]; rfl)
      · exact satSClause_of_mem (l := posL (qvar v 0)) (by simp)
          (by rw [evalSLit_pos, hq])
    · cases hq : β (qvar v 0)
      · exact satSClause_of_mem (l := negL (qvar v 0)) (by simp)
          (by rw [evalSLit_neg, hq]; rfl)
      · exact satSClause_of_mem (l := posL (chvar v 0)) (by simp)
          (by rw [evalSLit_pos, hch0, hq])
  · -- t = s+1 : chvar v (s+1) ↔ chvar v s ∧ qvar v (s+1)
    by_cases hP : ∀ e ∈ (movedList τ).take (s + 1), a e = a (permEdge τ e)
    · by_cases hQ : a ((movedList τ)[s + 1]'ht) = a (permEdge τ ((movedList τ)[s + 1]'ht))
      · have hcht : β (chvar v (s + 1)) = true := by
          rw [hβch (s + 1)]
          exact decide_eq_true (hsplit.mpr ⟨hP, hQ⟩)
        rcases mem_triple (show C ∈ [_, _, _] from hC) with rfl | rfl | rfl
        · exact satSClause_of_mem (l := posL (chvar v s)) (by simp)
            (by rw [evalSLit_pos, hβch s]; exact decide_eq_true hP)
        · exact satSClause_of_mem (l := posL (qvar v (s + 1))) (by simp)
            (by rw [evalSLit_pos, hβq]; exact decide_eq_true hQ)
        · exact satSClause_of_mem (l := posL (chvar v (s + 1))) (by simp)
            (by rw [evalSLit_pos, hcht])
      · have hcht : β (chvar v (s + 1)) = false := by
          rw [hβch (s + 1)]
          exact decide_eq_false (fun hall => hQ (hsplit.mp hall).2)
        rcases mem_triple (show C ∈ [_, _, _] from hC) with rfl | rfl | rfl
        · exact satSClause_of_mem (l := negL (chvar v (s + 1))) (by simp)
            (by rw [evalSLit_neg, hcht]; rfl)
        · exact satSClause_of_mem (l := negL (chvar v (s + 1))) (by simp)
            (by rw [evalSLit_neg, hcht]; rfl)
        · exact satSClause_of_mem (l := negL (qvar v (s + 1))) (by simp)
            (by rw [evalSLit_neg, hβq, decide_eq_false hQ]; rfl)
    · have hcht : β (chvar v (s + 1)) = false := by
        rw [hβch (s + 1)]
        exact decide_eq_false (fun hall => hP (hsplit.mp hall).1)
      have hchp : β (chvar v s) = false := by
        rw [hβch s]
        exact decide_eq_false hP
      rcases mem_triple (show C ∈ [_, _, _] from hC) with rfl | rfl | rfl
      · exact satSClause_of_mem (l := negL (chvar v (s + 1))) (by simp)
          (by rw [evalSLit_neg, hcht]; rfl)
      · exact satSClause_of_mem (l := negL (chvar v (s + 1))) (by simp)
          (by rw [evalSLit_neg, hcht]; rfl)
      · exact satSClause_of_mem (l := negL (chvar v s)) (by simp)
          (by rw [evalSLit_neg, hchp]; rfl)

/-- All vertex-lex clauses of one transposition are satisfied. -/
lemma sat_transposition (a : EColouring n r) (τ : Equiv.Perm (Fin n)) (v : ℕ)
    (β : SAssign n r)
    (hβe : ∀ e c, β (evar e c) = decide (a e = c))
    (hβq : ∀ t (ht : t < (movedList τ).length), β (qvar v t) =
      decide (a ((movedList τ)[t]'ht) = a (permEdge τ ((movedList τ)[t]'ht))))
    (hβch : ∀ s, β (chvar v s) =
      decide (∀ e ∈ (movedList τ).take (s + 1), a e = a (permEdge τ e)))
    (hV : lexView a ≤ lexView (actV τ a)) :
    ∀ C ∈ transpositionClauses τ v, satSClause β C = true := by
  intro C hC
  simp only [transpositionClauses, List.mem_flatMap, List.mem_append] at hC
  obtain ⟨t, -, hC | hC⟩ := hC
  · exact sat_vlexCmp a τ v β hβe hβch hV t.isLt hC
  · by_cases hlast : t.val + 1 < (movedList τ).length
    · rw [if_pos hlast, List.mem_append] at hC
      rcases hC with hC | hC
      · exact sat_vlexQ a τ v β hβe (Nat.lt_of_succ_lt hlast) (hβq _ _) hC
      · exact sat_vlexCh a τ v β hlast (hβq _ _) hβch hC
    · rw [if_neg hlast] at hC
      exact absurd hC List.not_mem_nil

/-! ### Satisfaction of the swap-break chain family -/

/-- The `eq`-definitional clauses of the chain are satisfied by the canonical
values. -/
lemma sat_ceqDef (a : EColouring n r) (p : ℕ) (c1 c2 : Fin r) (β : SAssign n r)
    (R : List (Row1 n))
    (hβe : ∀ e c, β (evar e c) = decide (a e = c))
    (hβq : ∀ t, β (ceqvar p t) = decide (∀ j ∈ R.take t,
      decide (a j.val = c1) = decide (a j.val = c2)))
    {t : ℕ} (htm : t - 1 < R.length) (ht1 : 1 ≤ t)
    {C : SClause n r}
    (hC : C ∈ ceqDefClauses p t (R[t - 1]'htm).val c1 c2) :
    satSClause β C = true := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at htm hC
  have htake : R.take (s + 1) =
      R.take s ++ [R[s]'htm] := by
    rw [List.take_add_one, List.getElem?_eq_getElem htm, Option.toList_some]
  have hsplit : (∀ j ∈ R.take (s + 1),
      decide (a j.val = c1) = decide (a j.val = c2)) ↔
      ((∀ j ∈ R.take s,
        decide (a j.val = c1) = decide (a j.val = c2)) ∧
        decide (a (R[s]'htm).val = c1) =
          decide (a (R[s]'htm).val = c2)) := by
    rw [htake, List.forall_mem_append, List.forall_mem_singleton]
  have himp12 : (∀ j ∈ R.take (s + 1),
      decide (a j.val = c1) = decide (a j.val = c2)) →
      a (R[s]'htm).val = c1 → a (R[s]'htm).val = c2 := by
    intro hall h1
    exact of_decide_eq_true (((hsplit.mp hall).2).symm.trans (decide_eq_true h1))
  have himp21 : (∀ j ∈ R.take (s + 1),
      decide (a j.val = c1) = decide (a j.val = c2)) →
      a (R[s]'htm).val = c2 → a (R[s]'htm).val = c1 := by
    intro hall h2
    exact of_decide_eq_true (((hsplit.mp hall).2).trans (decide_eq_true h2))
  have hmk : (∀ j ∈ R.take s,
      decide (a j.val = c1) = decide (a j.val = c2)) →
      decide (a (R[s]'htm).val = c1) =
        decide (a (R[s]'htm).val = c2) →
      ∀ j ∈ R.take (s + 1),
        decide (a j.val = c1) = decide (a j.val = c2) :=
    fun h1 h2 => hsplit.mpr ⟨h1, h2⟩
  rcases s with - | s
  · -- t = 1
    have hprev : ∀ j ∈ R.take 0,
        decide (a j.val = c1) = decide (a j.val = c2) := by simp
    rcases mem_quad (show C ∈ [_, _, _, _] from hC) with rfl | rfl | rfl | rfl
    · -- eq → (pa → pb)
      by_cases hall : ∀ j ∈ R.take 1,
          decide (a j.val = c1) = decide (a j.val = c2)
      · by_cases hpa : a (R[0]'htm).val = c1
        · exact satSClause_of_mem (l := posL (evar (R[0]'htm).val c2))
            (by simp) (by rw [evalSLit_pos, hβe]; exact decide_eq_true (himp12 hall hpa))
        · exact satSClause_of_mem (l := negL (evar (R[0]'htm).val c1))
            (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false hpa]; rfl)
      · exact satSClause_of_mem (l := negL (ceqvar p 1))
          (by simp) (by rw [evalSLit_neg, hβq, decide_eq_false hall]; rfl)
    · -- eq → (pb → pa)
      by_cases hall : ∀ j ∈ R.take 1,
          decide (a j.val = c1) = decide (a j.val = c2)
      · by_cases hpb : a (R[0]'htm).val = c2
        · exact satSClause_of_mem (l := posL (evar (R[0]'htm).val c1))
            (by simp) (by rw [evalSLit_pos, hβe]; exact decide_eq_true (himp21 hall hpb))
        · exact satSClause_of_mem (l := negL (evar (R[0]'htm).val c2))
            (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false hpb]; rfl)
      · exact satSClause_of_mem (l := negL (ceqvar p 1))
          (by simp) (by rw [evalSLit_neg, hβq, decide_eq_false hall]; rfl)
    · -- ¬pa ∧ ¬pb → eq
      by_cases hpa : a (R[0]'htm).val = c1
      · exact satSClause_of_mem (l := posL (evar (R[0]'htm).val c1))
          (by simp) (by rw [evalSLit_pos, hβe]; exact decide_eq_true hpa)
      · by_cases hpb : a (R[0]'htm).val = c2
        · exact satSClause_of_mem (l := posL (evar (R[0]'htm).val c2))
            (by simp) (by rw [evalSLit_pos, hβe]; exact decide_eq_true hpb)
        · exact satSClause_of_mem (l := posL (ceqvar p 1))
            (by simp)
            (by rw [evalSLit_pos, hβq]
                exact decide_eq_true (hmk hprev
                  (by rw [decide_eq_false hpa, decide_eq_false hpb])))
    · -- pa ∧ pb → eq
      by_cases hpa : a (R[0]'htm).val = c1
      · by_cases hpb : a (R[0]'htm).val = c2
        · exact satSClause_of_mem (l := posL (ceqvar p 1))
            (by simp)
            (by rw [evalSLit_pos, hβq]
                exact decide_eq_true (hmk hprev
                  (by rw [decide_eq_true hpa, decide_eq_true hpb])))
        · exact satSClause_of_mem (l := negL (evar (R[0]'htm).val c2))
            (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false hpb]; rfl)
      · exact satSClause_of_mem (l := negL (evar (R[0]'htm).val c1))
          (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false hpa]; rfl)
  · -- t = s+2
    rcases mem_quint (show C ∈ [_, _, _, _, _] from hC) with rfl | rfl | rfl | rfl | rfl
    · -- eq → eq'
      by_cases hall : ∀ j ∈ R.take (s + 2),
          decide (a j.val = c1) = decide (a j.val = c2)
      · exact satSClause_of_mem (l := posL (ceqvar p (s + 1)))
          (by simp) (by rw [evalSLit_pos, hβq]; exact decide_eq_true (hsplit.mp hall).1)
      · exact satSClause_of_mem (l := negL (ceqvar p (s + 2)))
          (by simp) (by rw [evalSLit_neg, hβq, decide_eq_false hall]; rfl)
    · -- eq → (pa → pb)
      by_cases hall : ∀ j ∈ R.take (s + 2),
          decide (a j.val = c1) = decide (a j.val = c2)
      · by_cases hpa : a (R[s + 1]'htm).val = c1
        · exact satSClause_of_mem (l := posL (evar (R[s + 1]'htm).val c2))
            (by simp) (by rw [evalSLit_pos, hβe]; exact decide_eq_true (himp12 hall hpa))
        · exact satSClause_of_mem (l := negL (evar (R[s + 1]'htm).val c1))
            (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false hpa]; rfl)
      · exact satSClause_of_mem (l := negL (ceqvar p (s + 2)))
          (by simp) (by rw [evalSLit_neg, hβq, decide_eq_false hall]; rfl)
    · -- eq → (pb → pa)
      by_cases hall : ∀ j ∈ R.take (s + 2),
          decide (a j.val = c1) = decide (a j.val = c2)
      · by_cases hpb : a (R[s + 1]'htm).val = c2
        · exact satSClause_of_mem (l := posL (evar (R[s + 1]'htm).val c1))
            (by simp) (by rw [evalSLit_pos, hβe]; exact decide_eq_true (himp21 hall hpb))
        · exact satSClause_of_mem (l := negL (evar (R[s + 1]'htm).val c2))
            (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false hpb]; rfl)
      · exact satSClause_of_mem (l := negL (ceqvar p (s + 2)))
          (by simp) (by rw [evalSLit_neg, hβq, decide_eq_false hall]; rfl)
    · -- eq' ∧ ¬pa ∧ ¬pb → eq
      by_cases hprev : ∀ j ∈ R.take (s + 1),
          decide (a j.val = c1) = decide (a j.val = c2)
      · by_cases hpa : a (R[s + 1]'htm).val = c1
        · exact satSClause_of_mem (l := posL (evar (R[s + 1]'htm).val c1))
            (by simp) (by rw [evalSLit_pos, hβe]; exact decide_eq_true hpa)
        · by_cases hpb : a (R[s + 1]'htm).val = c2
          · exact satSClause_of_mem (l := posL (evar (R[s + 1]'htm).val c2))
              (by simp) (by rw [evalSLit_pos, hβe]; exact decide_eq_true hpb)
          · exact satSClause_of_mem (l := posL (ceqvar p (s + 2)))
              (by simp)
              (by rw [evalSLit_pos, hβq]
                  exact decide_eq_true (hmk hprev
                    (by rw [decide_eq_false hpa, decide_eq_false hpb])))
      · exact satSClause_of_mem (l := negL (ceqvar p (s + 1)))
          (by simp) (by rw [evalSLit_neg, hβq, decide_eq_false hprev]; rfl)
    · -- eq' ∧ pa ∧ pb → eq
      by_cases hprev : ∀ j ∈ R.take (s + 1),
          decide (a j.val = c1) = decide (a j.val = c2)
      · by_cases hpa : a (R[s + 1]'htm).val = c1
        · by_cases hpb : a (R[s + 1]'htm).val = c2
          · exact satSClause_of_mem (l := posL (ceqvar p (s + 2)))
              (by simp)
              (by rw [evalSLit_pos, hβq]
                  exact decide_eq_true (hmk hprev
                    (by rw [decide_eq_true hpa, decide_eq_true hpb])))
          · exact satSClause_of_mem (l := negL (evar (R[s + 1]'htm).val c2))
              (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false hpb]; rfl)
        · exact satSClause_of_mem (l := negL (evar (R[s + 1]'htm).val c1))
            (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false hpa]; rfl)
      · exact satSClause_of_mem (l := negL (ceqvar p (s + 1)))
          (by simp) (by rw [evalSLit_neg, hβq, decide_eq_false hprev]; rfl)

/-- All clauses of one chain pair are satisfied when the row-1 indicator of
`c2` is lex-≤ that of `c1` (SBChain's conclusion). -/
lemma sat_chainPair (a : EColouring n r) (p : ℕ) (c1 c2 : Fin r) (β : SAssign n r)
    (hβe : ∀ e c, β (evar e c) = decide (a e = c))
    (hβq : ∀ t, β (ceqvar p t) = decide (∀ j ∈ (row1List n).take t,
      decide (a j.val = c1) = decide (a j.val = c2)))
    (hCle : toLex (row1Ind a c2) ≤ toLex (row1Ind a c1)) :
    ∀ C ∈ chainPairClauses p c1 c2, satSClause β C = true := by
  have key : ∀ (t : ℕ) (ht : t < (row1List n).length),
      (∀ j ∈ (row1List n).take t, decide (a j.val = c1) = decide (a j.val = c2)) →
      a ((row1List n)[t]'ht).val = c2 → a ((row1List n)[t]'ht).val = c1 := by
    intro t ht hpre h2
    have hle : row1Ind a c2 ((row1List n)[t]'ht) ≤ row1Ind a c1 ((row1List n)[t]'ht) := by
      refine Pi.apply_le_of_toLex hCle ?_
      intro j hj
      exact (hpre j (mem_take_of_lt (row1List_sortedLT n) ht (mem_row1List j) hj)).symm
    have h2' : row1Ind a c2 ((row1List n)[t]'ht) = true := decide_eq_true h2
    rw [h2'] at hle
    cases h1 : row1Ind a c1 ((row1List n)[t]'ht)
    · rw [h1] at hle
      exact absurd hle (by decide)
    · exact of_decide_eq_true h1
  intro C hC
  rw [chainPairClauses, List.mem_append] at hC
  rcases hC with hC | hC
  · -- first-position clause
    by_cases h0 : 0 < (row1List n).length
    · rw [dif_pos h0, List.mem_singleton] at hC
      subst hC
      by_cases hb : a ((row1List n)[0]'h0).val = c2
      · exact satSClause_of_mem (l := posL (evar ((row1List n)[0]'h0).val c1))
          (by simp)
          (by rw [evalSLit_pos, hβe]
              exact decide_eq_true (key 0 h0 (by simp) hb))
      · exact satSClause_of_mem (l := negL (evar ((row1List n)[0]'h0).val c2))
          (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false hb]; rfl)
    · rw [dif_neg h0] at hC
      exact absurd hC List.not_mem_nil
  · rw [List.mem_flatMap] at hC
    obtain ⟨t, -, hC⟩ := hC
    by_cases h1 : 1 ≤ t.val
    · rw [dif_pos h1, List.mem_append] at hC
      rcases hC with hC | hC
      · exact sat_ceqDef a p c1 c2 β (row1List n) hβe hβq (by have := t.isLt; omega) h1 hC
      · -- step clause
        rw [List.mem_singleton] at hC
        subst hC
        by_cases hpre : ∀ j ∈ (row1List n).take t.val,
            decide (a j.val = c1) = decide (a j.val = c2)
        · by_cases hb : a ((row1List n)[t.val]'t.isLt).val = c2
          · exact satSClause_of_mem (l := posL (evar ((row1List n)[t.val]'t.isLt).val c1))
              (by simp)
              (by rw [evalSLit_pos, hβe]
                  exact decide_eq_true (key t.val t.isLt hpre hb))
          · exact satSClause_of_mem (l := negL (evar ((row1List n)[t.val]'t.isLt).val c2))
              (by simp) (by rw [evalSLit_neg, hβe, decide_eq_false hb]; rfl)
        · exact satSClause_of_mem (l := negL (ceqvar p t.val))
            (by simp) (by rw [evalSLit_neg, hβq, decide_eq_false hpre]; rfl)
    · rw [dif_neg h1] at hC
      exact absurd hC List.not_mem_nil

/-! ### The deliverable -/

/-- **Satisfiability of the emitted SB clauses by a lex-leader.**  If `a` is
lex-led by each allowed adjacent vertex transposition (`hV`) and its row-1
colour indicators are sorted along the chain (`hC`, the conclusion SBChain
extracts from colour-swap leaderhood), then the canonical auxiliary
extension of `ofColouring a` satisfies every emitted `--vertex-lex` and
`--swap-break` clause. -/
theorem sb_clauses_satisfiable_of_leader (a : EColouring n r)
    (blocks : List ℕ) (chain : List (Fin r))
    (hV : ∀ v ∈ blocks, ∀ h : v + 1 < n, lexView a ≤ lexView (actV (vswap n v h) a))
    (hC : ∀ p (hp : p + 1 < chain.length),
      toLex (row1Ind a (chain[p + 1]'hp)) ≤
        toLex (row1Ind a (chain[p]'(Nat.lt_of_succ_lt hp)))) :
    ∃ β : SAssign n r, restrictsTo β a ∧
      satSCNF β (vertexLexClauses n r blocks ++ chainClauses n r chain) := by
  refine ⟨canonAssign a chain, fun e c => rfl, ?_⟩
  rw [satSCNF_append]
  constructor
  · intro C hCm
    simp only [vertexLexClauses, List.mem_flatMap] at hCm
    obtain ⟨v, hv, hCm⟩ := hCm
    by_cases h : v + 1 < n
    · rw [dif_pos h] at hCm
      exact sat_transposition a (vswap n v h) v (canonAssign a chain)
        (fun e c => rfl) (fun t ht => canonAssign_vq a chain h ht)
        (canonAssign_vch a chain h) (hV v hv h) C hCm
    · rw [dif_neg h] at hCm
      exact absurd hCm List.not_mem_nil
  · intro C hCm
    simp only [chainClauses, List.mem_flatMap] at hCm
    obtain ⟨p, -, hCm⟩ := hCm
    have hp : p.val + 1 < chain.length := by have := p.isLt; omega
    exact sat_chainPair a p.val _ _ (canonAssign a chain)
      (fun e c => rfl) (canonAssign_ceq a chain hp) (hC p.val hp) C hCm

end SB

#print axioms SB.sb_clauses_satisfiable_of_leader
#print axioms SB.sat_transposition
#print axioms SB.sat_chainPair
