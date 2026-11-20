-- Generated from literate/40-collection.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Archive

namespace OpenSheaf

variable {D : Type} (hash : Hash D)

/-- The head of the first copy of line `l` found at the archives `bs`, with
the hints `hs`. -/
def headIn (w : World D) (hs : List ArchiveId) : List ArchiveId → LineId → Option (Pin D)
  | [], _ => none
  | b :: bs, l =>
    match lookup w b (.line l) with
    | some (.live o) =>
      if o.versions.length = 0 then headIn w hs bs l
      else some ⟨l, o.versions.length, hash (o.inventory o.versions.length), hs⟩
    | _ => headIn w hs bs l

/-- The head of the first copy of line `l` found at the hints `hs`. -/
def headPin (w : World D) (hs : List ArchiveId) (l : LineId) : Option (Pin D) :=
  headIn hash w hs hs l

/-- Update one member of a catalogue. -/
def updateMember (w : World D) (m : Member D) : Member D :=
  if m.follow then
    match headPin hash w m.hints m.line with
    | some p => { m with pins := [p] }
    | none => m
  else m

/-- Update a collection. -/
def collect (w : World D) (c : Members D) : Members D :=
  match c.type with
  | .selection => c
  | .catalogue => { c with members := c.members.map (updateMember hash w) }

/-- **Selections do not move.** Updating a selection leaves it as it is. -/
theorem collect_selection (w : World D) {c : Members D} (h : c.type = .selection) :
    collect hash w c = c := by
  simp [collect, h]

/-- Updating a collection keeps its type. -/
theorem collect_type (w : World D) (c : Members D) : (collect hash w c).type = c.type := by
  unfold collect; split <;> rfl

/-- In a catalogue, a member with `follow` is moved to the head. -/
theorem collect_follow (w : World D) {c : Members D} (h : c.type = .catalogue)
    {m : Member D} (hm : m ∈ c.members) (hf : m.follow = true) {p : Pin D}
    (hp : headPin hash w m.hints m.line = some p) :
    { m with pins := [p] } ∈ (collect hash w c).members := by
  simp only [collect, h]
  refine List.mem_map.mpr ⟨m, hm, ?_⟩
  simp [updateMember, hf, hp]

/-- In a catalogue, a member without `follow` stays. -/
theorem collect_fixed (w : World D) {c : Members D} (h : c.type = .catalogue)
    {m : Member D} (hm : m ∈ c.members) (hf : m.follow = false) :
    m ∈ (collect hash w c).members := by
  simp only [collect, h]
  refine List.mem_map.mpr ⟨m, hm, ?_⟩
  simp [updateMember, hf]

theorem headIn_resolves [DecidableEq D] {w : World D} {hs bs : List ArchiveId}
    {l : LineId} {p : Pin D} (h : headIn hash w hs bs l = some p) :
    p.hints = hs ∧ ∃ b ∈ bs, ∃ o, lookup w b (.line l) = some (.live o) ∧
      ∃ hne : o.versions ≠ [], p.line = l ∧ resolveAt hash w b p = .ok (o.versions.getLast hne) := by
  induction bs with
  | nil => simp [headIn] at h
  | cons b bs ih =>
    unfold headIn at h
    split at h
    · rename_i o hl
      split at h
      · obtain ⟨hh, b', hb', o', h1, h2⟩ := ih h
        exact ⟨hh, b', List.mem_cons_of_mem _ hb', o', h1, h2⟩
      · rename_i hne
        cases h
        have hne' : o.versions ≠ [] := fun he => hne (by simp [he])
        refine ⟨rfl, b, List.mem_cons_self .., o, hl, hne', rfl, ?_⟩
        unfold resolveAt
        simp only [hl]
        apply resolveEntry_live_of
        · simp only [Obj.versionAt, hne, ite_false]
          rw [List.getLast_eq_getElem]
          simp
        · rfl
    · obtain ⟨hh, b', hb', o', h1, h2⟩ := ih h
      exact ⟨hh, b', List.mem_cons_of_mem _ hb', o', h1, h2⟩

/-- The head pin resolves, at one of its hints, to the last version of the copy
kept there; it carries the hints it was looked up with. -/
theorem headPin_resolves [DecidableEq D] {w : World D} {hs : List ArchiveId} {l : LineId}
    {p : Pin D} (h : headPin hash w hs l = some p) :
    p.hints = hs ∧ ∃ b ∈ hs, ∃ o, lookup w b (.line l) = some (.live o) ∧
      ∃ hne : o.versions ≠ [], p.line = l ∧ resolveAt hash w b p = .ok (o.versions.getLast hne) :=
  headIn_resolves hash h

/-- A member obeys the rules of section 8 for its type of collection. -/
def Member.WF (ty : CollectionType) (m : Member D) : Prop :=
  m.hints ≠ [] ∧ m.pins ≠ [] ∧ (∀ p ∈ m.pins, p.line = m.line ∧ p.hints = m.hints) ∧
    (ty = .catalogue → m.pins.length = 1) ∧ (ty = .selection → m.follow = false)

instance (ty : CollectionType) (m : Member D) : Decidable (m.WF ty) := by
  unfold Member.WF; infer_instance

/-- A well-formed member list. -/
def Members.WF (c : Members D) : Prop := ∀ m ∈ c.members, m.WF c.type

instance (c : Members D) : Decidable c.WF := by
  unfold Members.WF; infer_instance

theorem headIn_names {w : World D} {hs bs : List ArchiveId} {l : LineId} {p : Pin D}
    (h : headIn hash w hs bs l = some p) : p.line = l ∧ p.hints = hs := by
  induction bs with
  | nil => simp [headIn] at h
  | cons b bs ih =>
    unfold headIn at h
    split at h
    · split at h
      · exact ih h
      · cases h; exact ⟨rfl, rfl⟩
    · exact ih h

theorem headPin_names {w : World D} {hs : List ArchiveId} {l : LineId} {p : Pin D}
    (h : headPin hash w hs l = some p) : p.line = l ∧ p.hints = hs :=
  headIn_names hash h

/-- **Updating keeps a member list well formed.** -/
theorem collect_wf (w : World D) {c : Members D} (h : c.WF) : (collect hash w c).WF := by
  unfold collect
  split
  · exact h
  · rename_i hty
    intro m' hm'
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hm'
    have hmw := h m hm
    rw [hty] at hmw
    show (updateMember hash w m).WF c.type
    rw [hty]
    unfold updateMember
    split
    · split
      · rename_i p hp
        obtain ⟨hl, hh⟩ := headPin_names hash hp
        refine ⟨hmw.1, by simp, ?_, fun _ => rfl, fun h => nomatch h⟩
        intro q hq
        simp only [List.mem_singleton] at hq
        subst hq
        exact ⟨hl, hh⟩
      · exact hmw
    · exact hmw

end OpenSheaf
