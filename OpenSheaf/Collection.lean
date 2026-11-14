-- Generated from literate/40-collection.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Archive

namespace OpenSheaf

variable {D : Type} (hash : Hash D)

/-- The pin of the head of a live object: its newest object version. -/
def headPin (w : World D) (a : ArchiveId) (oid : ObjectId) : Option (Pin D) :=
  match lookup w a oid with
  | some (.live o) =>
    if o.versions.length = 0 then none
    else some ⟨a, oid, o.versions.length, hash (o.inventory o.versions.length)⟩
  | _ => none

/-- Update one member of a catalogue. -/
def updateMember (w : World D) (m : Member D) : Member D :=
  if m.follow then
    match headPin hash w m.archive m.object with
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
    (hp : headPin hash w m.archive m.object = some p) :
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

/-- The head pin resolves, to the newest object version. -/
theorem headPin_resolves [DecidableEq D] {w : World D} {a : ArchiveId} {oid : ObjectId}
    {p : Pin D} (h : headPin hash w a oid = some p) :
    ∃ o, lookup w a oid = some (.live o) ∧
      ∃ hne : o.versions ≠ [], resolve hash w p = .ok (o.versions.getLast hne) := by
  unfold headPin at h
  split at h
  · rename_i o hl
    split at h
    · contradiction
    · rename_i hne
      cases h
      have hne' : o.versions ≠ [] := fun he => hne (by simp [he])
      refine ⟨o, hl, hne', ?_⟩
      unfold resolve
      simp only [hl]
      apply resolveEntry_live_of
      · simp only [Obj.versionAt, hne, ite_false]
        rw [List.getLast_eq_getElem]
        simp
      · rfl
  · contradiction

/-- A member obeys the rules of section 10.2 for its kind of collection. -/
def Member.WF (ty : CollectionType) (m : Member D) : Prop :=
  m.pins ≠ [] ∧ (∀ p ∈ m.pins, p.archive = m.archive ∧ p.object = m.object) ∧
    (ty = .catalogue → m.pins.length = 1) ∧ (ty = .selection → m.follow = false)

instance (ty : CollectionType) (m : Member D) : Decidable (m.WF ty) := by
  unfold Member.WF; infer_instance

/-- A well-formed member list. -/
def Members.WF (c : Members D) : Prop := ∀ m ∈ c.members, m.WF c.type

instance (c : Members D) : Decidable c.WF := by
  unfold Members.WF; infer_instance

theorem headPin_names {w : World D} {a : ArchiveId} {oid : ObjectId} {p : Pin D}
    (h : headPin hash w a oid = some p) : p.archive = a ∧ p.object = oid := by
  unfold headPin at h
  split at h
  · split at h
    · contradiction
    · cases h; exact ⟨rfl, rfl⟩
  · contradiction

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
        obtain ⟨ha, ho⟩ := headPin_names hash hp
        refine ⟨by simp, ?_, fun _ => rfl, fun h => nomatch h⟩
        intro q hq
        simp only [List.mem_singleton] at hq
        subst hq
        exact ⟨ha, ho⟩
      · exact hmw
    · exact hmw

end OpenSheaf
