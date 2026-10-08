/-
# M3: the automorphisms enumerated by `autos` (the auth clauses)

Every array returned by `autos cl Hs` assigns to the vertices of the cells `cl` (in order) distinct
images, each in the vertex's own cell, and passes `ok`: every edge of `Hs` is sent into `Hs`.
Read through the encoder's `img` (identity off the cells) this is a cell-preserving, injective map
sending `Hs` into `Hs` (`autos_img`).
-/
import RootedBridge.Spec

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SB.Rooted
open LRATCatcher.Rooted

/-- What an enumerated assignment extends `asg` by. -/
def ExtOK (rest : List (Nat × Array Nat)) (used : Array Nat) (ext : List (Nat × Nat)) : Prop :=
  ext.length = rest.length ∧
  (∀ i (h : i < ext.length) (h' : i < rest.length), ext[i].1 = rest[i].1 ∧ ext[i].2 ∈ rest[i].2) ∧
  (∀ c ∈ ext.map (·.2), c ∉ used) ∧ (ext.map (·.2)).Nodup

theorem autosGo_mem (ok : Array (Nat × Nat) → Bool) :
    ∀ (rest : List (Nat × Array Nat)) (asg : Array (Nat × Nat)) (used : Array Nat)
      (acc : Array (Array (Nat × Nat))) (out : Array (Nat × Nat)),
      (asg ≠ #[] → ok asg = true) →
      out ∈ autosGo ok rest asg used acc →
      out ∈ acc ∨ (∃ ext, out.toList = asg.toList ++ ext ∧ ExtOK rest used ext ∧ ok out = true)
  | [], asg, used, acc, out, hok, hmem => by
    unfold autosGo at hmem
    split at hmem
    · exact Or.inl hmem
    · next hnot =>
      rcases Array.mem_push.mp hmem with h | rfl
      · exact Or.inl h
      · right
        refine ⟨[], by simp, ⟨rfl, fun i h => absurd h (by simp), by simp, by simp⟩, hok ?_⟩
        intro he; subst he; simp at hnot
  | (v, pool) :: rest, asg, used, acc, out, hok, hmem => by
    unfold autosGo at hmem
    rw [← Array.foldl_toList] at hmem
    -- induction over the candidate pool
    suffices H : ∀ (cands : List Nat) (acc₀ : Array (Array (Nat × Nat))), (∀ c ∈ cands, c ∈ pool) →
        out ∈ cands.foldl (fun acc cand =>
          if used.contains cand = true then acc
          else
            let asg' := asg.push (v, cand)
            if ok asg' = true then autosGo ok rest asg' (used.push cand) acc else acc) acc₀ →
        out ∈ acc₀ ∨ (∃ ext, out.toList = asg.toList ++ ext ∧ ExtOK ((v, pool) :: rest) used ext ∧
          ok out = true) by
      exact H pool.toList acc (fun c hc => by simpa using hc) hmem
    intro cands
    induction cands with
    | nil => intro acc₀ _ h; exact Or.inl h
    | cons c cs ih =>
      intro acc₀ hcs h
      simp only [List.foldl_cons] at h
      rcases ih _ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) h with h1 | h1
      · -- `out` is in the accumulator after the step for `c`
        split at h1
        · exact Or.inl h1
        · next hused =>
          split at h1
          · next hok' =>
            rcases autosGo_mem ok rest (asg.push (v, c)) (used.push c) acc₀ out
              (fun _ => hok') h1 with h2 | ⟨ext, he, ⟨hl, hi, hu, hn⟩, hout⟩
            · exact Or.inl h2
            · right
              refine ⟨(v, c) :: ext, by simp [he], ⟨by simp [hl], ?_, ?_, ?_⟩, hout⟩
              · intro i h h'
                cases i with
                | zero => exact ⟨rfl, hcs c List.mem_cons_self⟩
                | succ i => simpa using hi i (by simpa using h) (by simpa using h')
              · intro c' hc'
                simp only [List.map_cons, List.mem_cons] at hc'
                rcases hc' with rfl | hc'
                · simpa using hused
                · have := hu c' hc'
                  intro h''; exact this (Array.mem_push.mpr (Or.inl h''))
              · simp only [List.map_cons, List.nodup_cons]
                refine ⟨fun hm => ?_, hn⟩
                exact hu c hm (Array.mem_push.mpr (Or.inr rfl))
          · exact Or.inl h1
      · exact Or.inr h1

/-- The encoder's `img` for an enumerated assignment (identity off its domain). -/
def imgA (asg : Array (Nat × Nat)) (v : Nat) : Nat :=
  match Array.find? (fun x => x.fst == v) asg with
  | some p => p.snd
  | none => v

theorem find_key {out : Array (Nat × Nat)} (hnd : (out.toList.map (·.1)).Nodup) (i : Nat)
    (hi : i < out.size) : out.find? (fun x => x.fst == out[i].1) = some out[i] := by
  rw [Array.find?_eq_some_iff_getElem]
  refine ⟨by simp, i, hi, rfl, fun j hj => ?_⟩
  have hne : out[j].1 ≠ out[i].1 := by
    intro heq
    have h1 : (out.toList.map (·.1))[j]'(by simp; omega) = (out.toList.map (·.1))[i]'(by simp; omega) := by
      simp [heq]
    have := (List.getElem_inj hnd).mp h1
    omega
  simp [hne]

theorem find_none {out : Array (Nat × Nat)} {v : Nat} (hv : v ∉ out.toList.map (·.1)) :
    out.find? (fun x => x.fst == v) = none := by
  rw [Array.find?_eq_none]
  intro x hx heq
  apply hv
  simp only [beq_iff_eq] at heq
  exact List.mem_map.mpr ⟨x, by simpa using hx, heq⟩

/-- The vertices of the cells, in order. -/
def cellVerts (cl : Array (Array Nat)) : List Nat := cl.toList.flatMap Array.toList

theorem pos_toList (cl : Array (Array Nat)) :
    (cl.foldl (fun acc c => acc ++ c.map (fun v => (v, c))) #[]).toList =
      cl.toList.flatMap (fun c => c.toList.map (fun v => (v, c))) := by
  rw [← Array.foldl_toList]
  suffices h : ∀ (l : List (Array Nat)) (acc : Array (Nat × Array Nat)),
      (l.foldl (fun acc c => acc ++ c.map (fun v => (v, c))) acc).toList =
        acc.toList ++ l.flatMap (fun c => c.toList.map (fun v => (v, c))) by
    simpa using h cl.toList #[]
  intro l
  induction l with
  | nil => intro acc; simp
  | cons c cs ih => intro acc; rw [List.foldl_cons, ih]; simp

theorem mem_cellVerts {cl : Array (Array Nat)} {v : Nat} : v ∈ cellVerts cl ↔ ∃ c ∈ cl, v ∈ c := by
  unfold cellVerts; simp

/-- **The enumerated automorphisms.** For every array `out` returned by `autos cl Hs` (cells with
distinct vertices), the encoder's `img` maps each cell vertex into a cell containing it, fixes every
other vertex, is injective, and sends every edge of `Hs` into `Hs`. -/
theorem autos_img (cl : Array (Array Nat)) (Hs : Array (Nat × Nat)) (hnd : (cellVerts cl).Nodup)
    (out : Array (Nat × Nat)) (hout : out ∈ autos cl Hs) :
    (∀ v ∈ cellVerts cl, ∃ c ∈ cl, v ∈ c ∧ imgA out v ∈ c) ∧
    (∀ v, v ∉ cellVerts cl → imgA out v = v) ∧
    (∀ v w, imgA out v = imgA out w → v = w) ∧
    (∀ e ∈ Hs, Hs.contains (srt (imgA out e.1) (imgA out e.2)) = true) := by
  unfold autos at hout
  simp only at hout
  have hpos := pos_toList cl
  generalize hP : cl.foldl (fun acc c => acc ++ c.map (fun v => (v, c))) #[] = pos at hpos hout
  rcases autosGo_mem _ pos.toList #[] #[] #[] out (fun h => absurd rfl h) hout with h | ⟨ext, hext, ⟨hl, hi, -, hn⟩, hok⟩
  · simp at h
  simp only [Array.toList_empty, List.nil_append] at hext
  -- keys of `out` are the cell vertices
  have hkeys : out.toList.map (·.1) = cellVerts cl := by
    rw [hext]
    have : pos.toList.map (·.1) = cellVerts cl := by
      rw [hpos]; unfold cellVerts; simp [List.map_flatMap, Function.comp_def]
    rw [← this]
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2
    simp only [List.getElem_map]
    exact (hi i (by simpa using h1) (by simpa using h2)).1
  have hknd : (out.toList.map (·.1)).Nodup := hkeys ▸ hnd
  have hsz : out.size = ext.length := by rw [← Array.length_toList, hext]
  have hent : ∀ i (h : i < out.size), out[i] = ext[i]'(by omega) := by
    intro i h; simp [← Array.getElem_toList, hext]
  -- `img` on a key
  have himg : ∀ i (h : i < out.size), imgA out out[i].1 = out[i].2 := by
    intro i h; unfold imgA; rw [find_key hknd i h]
  have hmemPos : ∀ i (h : i < out.size), ∃ c ∈ cl, out[i].1 ∈ c ∧ out[i].2 ∈ c := by
    intro i h
    have hp : i < pos.toList.length := by rw [← hl, ← hsz]; exact h
    obtain ⟨h1, h2⟩ := hi i (by omega) hp
    have hmem : pos.toList[i] ∈ cl.toList.flatMap (fun c => c.toList.map (fun v => (v, c))) := by
      rw [← hpos]; exact List.getElem_mem hp
    simp only [List.mem_flatMap, List.mem_map] at hmem
    obtain ⟨c, hc, v, hv, hpv⟩ := hmem
    refine ⟨c, by simpa using hc, ?_, ?_⟩
    · rw [hent i h, h1, ← hpv]; simpa using hv
    · rw [hent i h]; rw [← hpv] at h2; simpa using h2
  have hkey_of : ∀ v ∈ cellVerts cl, ∃ i, ∃ h : i < out.size, out[i].1 = v := by
    intro v hv
    rw [← hkeys] at hv
    obtain ⟨i, hi', hiv⟩ := List.getElem_of_mem hv
    exact ⟨i, by simpa using hi', by simpa using hiv⟩
  have hoff : ∀ v, v ∉ cellVerts cl → imgA out v = v := by
    intro v hv; unfold imgA; rw [find_none (by rw [hkeys]; exact hv)]
  refine ⟨fun v hv => ?_, hoff, fun v w hvw => ?_, fun e he => ?_⟩
  · obtain ⟨i, h, rfl⟩ := hkey_of v hv
    obtain ⟨c, hc, h1, h2⟩ := hmemPos i h
    exact ⟨c, hc, h1, by rw [himg i h]; exact h2⟩
  · have hin : ∀ x, x ∈ cellVerts cl → imgA out x ∈ cellVerts cl := by
      intro x hx
      obtain ⟨i, h, rfl⟩ := hkey_of x hx
      obtain ⟨c, hc, -, h2⟩ := hmemPos i h
      rw [himg i h]; exact mem_cellVerts.mpr ⟨c, hc, h2⟩
    by_cases hv : v ∈ cellVerts cl <;> by_cases hw : w ∈ cellVerts cl
    · obtain ⟨i, hi', rfl⟩ := hkey_of v hv
      obtain ⟨j, hj', rfl⟩ := hkey_of w hw
      rw [himg i hi', himg j hj'] at hvw
      have hvals : (out.toList.map (·.2)).Nodup := by
        rw [hext]; exact hn
      have h1 : (out.toList.map (·.2))[i]'(by simp; omega) = (out.toList.map (·.2))[j]'(by simp; omega) := by
        simp [hvw]
      have := (List.getElem_inj hvals).mp h1
      subst this; rfl
    · exfalso; have := hin v hv; rw [hvw, hoff w hw] at this; exact hw this
    · exfalso; have := hin w hw; rw [← hvw, hoff v hv] at this; exact hv this
    · rw [hoff v hv, hoff w hw] at hvw; exact hvw
  · -- `ok out` read through `img`
    rw [Array.all_eq_true'] at hok
    have hdom : ∀ v, (pos.map (·.1)).contains v = true ↔ v ∈ cellVerts cl := by
      intro v
      rw [Array.contains_iff_mem, Array.mem_def, Array.toList_map, hpos]
      unfold cellVerts; simp [List.map_flatMap, Function.comp_def]
    have hio : ∀ v, (match Array.find? (fun x => x.fst == v) out with
        | some p => some p.snd
        | none => if (Array.map (fun x => x.fst) pos).contains v = true then none else some v) =
        some (imgA out v) := by
      intro v
      by_cases hv : v ∈ cellVerts cl
      · obtain ⟨i, h, rfl⟩ := hkey_of v hv
        rw [find_key hknd i h, himg i h]
      · rw [find_none (by rw [hkeys]; exact hv), hoff v hv]
        have : ¬ ((Array.map (fun x => x.fst) pos).contains v = true) := fun h => hv ((hdom v).mp h)
        rw [if_neg this]
    have := hok e he
    split at this
    · next x y h1 h2 =>
      have h1' : some (imgA out e.1) = some x := (hio e.1).symm.trans h1
      have h2' : some (imgA out e.2) = some y := (hio e.2).symm.trans h2
      cases h1'; cases h2'; exact this
    · next x y hne =>
      exfalso
      exact hne (imgA out e.1) (imgA out e.2) (hio e.1) (hio e.2)

end SB.Rooted
#print axioms SB.Rooted.autos_img
