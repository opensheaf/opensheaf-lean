-- Generated from literate/45-worlds.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Collection

namespace OpenSheaf

variable {D : Type} [DecidableEq D] (hash : Hash D)

/-- A well-formed object stored under `oid` (sections 7 and 7.4). -/
structure Obj.WF (o : Obj D) (oid : ObjectId) : Prop where
  id : o.id = oid
  nonempty : o.versions ≠ []
  history : WellFormed o.versions
  kinds : ∀ v ∈ o.versions, v.members.isSome = true ↔ o.kind = .collection

/-- Every pin held by a version of a live object resolves. -/
def PinsOk (w : World D) : Prop :=
  ∀ a oid o, lookup w a oid = some (.live o) →
    ∀ v ∈ o.versions, ∀ p ∈ v.pins, ∃ t, resolve hash w p = .ok t

/-- A well-formed world. -/
def WFWorld (w : World D) : Prop :=
  (∀ a oid o, lookup w a oid = some (.live o) → o.WF oid) ∧ PinsOk hash w

theorem WFWorld.empty : WFWorld hash (fun _ => (none : Option (Archive D))) :=
  ⟨fun _ _ _ h => by simp [lookup] at h, fun _ _ _ h => by simp [lookup] at h⟩

/-- The steps that the specification allows. -/
inductive ValidStep : World D → World D → Prop
  | newArchive (w : World D) (a : ArchiveId) (ar : Archive D) (h : w a = none)
      (hempty : ∀ x, ar.entries x = none) :
      ValidStep w (fun b => if b = a then some ar else w b)
  | create (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
      (ha : w a = some ar) (ho : ar.entries oid = none) (hwf : o.WF oid)
      (hpins : ∀ v ∈ o.versions, ∀ p ∈ v.pins, ∃ t, resolve hash w p = .ok t) :
      ValidStep w (setEntry w a oid (.live o))
  | append (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
      (x : Version D) (ha : w a = some ar) (ho : ar.entries oid = some (.live o))
      (hf : Extends o.versions x) (hst : NoReinstatement o.versions x)
      (hk : x.members.isSome = true ↔ o.kind = .collection)
      (hpins : ∀ p ∈ x.pins, ∃ t, resolve hash w p = .ok t) :
      ValidStep w (setEntry w a oid (.live (o.append x)))

/-- Any number of valid steps. -/
inductive ValidSteps : World D → World D → Prop
  | refl (w : World D) : ValidSteps w w
  | tail {w w' w'' : World D} : ValidSteps w w' → ValidStep hash w' w'' → ValidSteps w w''

theorem ValidStep.toStep {w w' : World D} (h : ValidStep hash w w') : Step w w' := by
  cases h with
  | newArchive a ar h _ => exact .newArchive w a ar h
  | create a ar oid o ha ho _ _ => exact .create w a ar oid o ha ho
  | append a ar oid o x ha ho _ _ _ _ => exact .append w a ar oid o x ha ho

theorem ValidSteps.toSteps {w w' : World D} (h : ValidSteps hash w w') : Steps w w' := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact .tail ih (hs.toStep hash)

omit [DecidableEq D] in
theorem Step.lookup_cases {w w' : World D} (hs : Step w w') (b : ArchiveId) (x : ObjectId) :
    lookup w' b x = lookup w b x ∨ lookup w b x = none ∨
    (∃ o v, lookup w b x = some (.live o) ∧ lookup w' b x = some (.live (o.append v))) := by
  cases hs with
  | newArchive a ar ha =>
    by_cases hb : b = a
    · subst hb; exact Or.inr (Or.inl (by simp [lookup, ha]))
    · exact Or.inl (by simp [lookup, hb])
  | create a ar oid o ha ho =>
    rw [lookup_setEntry ha]
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr (Or.inl (by simp [lookup, ha, ho]))
    · exact Or.inl rfl
  | append a ar oid o v ha ho =>
    rw [lookup_setEntry ha]
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr (Or.inr ⟨o, v, by simp [lookup, ha, ho], rfl⟩)
    · exact Or.inl rfl

omit [DecidableEq D] in
/-- **A tombstone stays.** -/
theorem Step.tomb_stays {w w' : World D} (hs : Step w w') {b : ArchiveId} {x : ObjectId}
    {n : Nat} {d : D} (h : lookup w b x = some (.tomb n d)) :
    lookup w' b x = some (.tomb n d) := by
  rcases hs.lookup_cases b x with h1 | h1 | ⟨o, v, h1, _⟩
  · rw [h1, h]
  · rw [h] at h1; cases h1
  · rw [h] at h1; cases h1

omit [DecidableEq D] in
theorem Steps.tomb_stays {w w' : World D} (hs : Steps w w') {b : ArchiveId} {x : ObjectId}
    {n : Nat} {d : D} (h : lookup w b x = some (.tomb n d)) :
    lookup w' b x = some (.tomb n d) := by
  induction hs with
  | refl => exact h
  | tail _ hstep ih => exact hstep.tomb_stays ih

omit [DecidableEq D] in
/-- **Objects only grow.** -/
theorem Step.live_grows {w w' : World D} (hs : Step w w') {b : ArchiveId} {x : ObjectId}
    {o : Obj D} (h : lookup w b x = some (.live o)) :
    ∃ o', lookup w' b x = some (.live o') ∧ o'.id = o.id ∧ o'.kind = o.kind ∧
      ∃ t, o'.versions = o.versions ++ t := by
  rcases hs.lookup_cases b x with h1 | h1 | ⟨o1, v, h1, h2⟩
  · exact ⟨o, by rw [h1, h], rfl, rfl, [], by simp⟩
  · rw [h] at h1; cases h1
  · rw [h] at h1; cases h1
    exact ⟨o.append v, h2, rfl, rfl, [v], rfl⟩

omit [DecidableEq D] in
theorem Steps.live_grows {w w' : World D} (hs : Steps w w') {b : ArchiveId} {x : ObjectId}
    {o : Obj D} (h : lookup w b x = some (.live o)) :
    ∃ o', lookup w' b x = some (.live o') ∧ o'.id = o.id ∧ o'.kind = o.kind ∧
      ∃ t, o'.versions = o.versions ++ t := by
  induction hs with
  | refl => exact ⟨o, h, rfl, rfl, [], by simp⟩
  | tail _ hstep ih =>
    obtain ⟨o1, h1, hid1, hk1, t1, ht1⟩ := ih
    obtain ⟨o2, h2, hid2, hk2, t2, ht2⟩ := hstep.live_grows h1
    exact ⟨o2, h2, hid2.trans hid1, hk2.trans hk1, t1 ++ t2, by rw [ht2, ht1, List.append_assoc]⟩

theorem ValidStep.entry {w w' : World D} (hs : ValidStep hash w w') (hw : WFWorld hash w)
    {b : ArchiveId} {x : ObjectId} {o' : Obj D} (h : lookup w' b x = some (.live o')) :
    o'.WF x ∧ ∀ v ∈ o'.versions, ∀ p ∈ v.pins, ∃ t, resolve hash w p = .ok t := by
  cases hs with
  | newArchive a ar ha hempty =>
    by_cases hb : b = a
    · subst hb; simp [lookup, hempty] at h
    · have hl : lookup w b x = some (.live o') := by simpa [lookup, hb] using h
      exact ⟨hw.1 _ _ _ hl, hw.2 _ _ _ hl⟩
  | create a ar oid o ha ho hwf hpins =>
    rw [lookup_setEntry ha] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h
      exact ⟨hwf, hpins⟩
    · exact ⟨hw.1 _ _ _ h, hw.2 _ _ _ h⟩
  | append a ar oid o y ha ho hf _ hk hpins =>
    rw [lookup_setEntry ha] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h
      have hl : lookup w b x = some (.live o) := by simp [lookup, ha, ho]
      have hwf := hw.1 _ _ _ hl
      refine ⟨⟨hwf.id, by simp [Obj.append], hwf.history.snoc hf, ?_⟩, ?_⟩
      · intro v hv
        simp only [Obj.append, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact hwf.kinds v hv
        · exact hk
      · intro v hv p hp
        simp only [Obj.append, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact hw.2 _ _ _ hl v hv p hp
        · exact hpins p hp
    · exact ⟨hw.1 _ _ _ h, hw.2 _ _ _ h⟩

/-- **Valid steps keep worlds well formed.** -/
theorem ValidStep.wf {w w' : World D} (hs : ValidStep hash w w') (hw : WFWorld hash w) :
    WFWorld hash w' :=
  ⟨fun _ _ _ h => (hs.entry hash hw h).1,
   fun _ _ _ h v hv p hp => by
     obtain ⟨t, ht⟩ := (hs.entry hash hw h).2 v hv p hp
     exact ⟨t, Step.resolve_ok hash (hs.toStep hash) ht⟩⟩

theorem ValidSteps.wf {w w' : World D} (hs : ValidSteps hash w w') (hw : WFWorld hash w) :
    WFWorld hash w' := by
  induction hs with
  | refl => exact hw
  | tail _ hstep ih => exact hstep.wf hash ih

/-- **Nothing dangles.** -/
theorem ValidSteps.pins_ok {w : World D}
    (hs : ValidSteps hash (fun _ => (none : Option (Archive D))) w) : PinsOk hash w :=
  (hs.wf hash (WFWorld.empty hash)).2

end OpenSheaf
