# Catalogues and selections

A collection is an object whose versions hold a member list (section 10).
The two kinds of collection differ in what updating them does (section
10.1, the command `osheaf collect`):

- in a **catalogue**, a member with `follow` is moved to the head of its
  object, the newest object version; the other members stay;
- a **selection** never moves: its revision sets change only by an act of
  its curator, a new version of the collection which they deposit. A tool
  updating a selection may report new versions of its members; it does not
  add them.

This chapter defines the update and proves what it does to each kind,
together with the fact that the pin given to a followed member resolves, to
the newest version. That only the curator changes a selection is not proved
here: the model has no notion of who makes a step (see
[chapter 5](45-worlds.md)).

    -- in OpenSheaf/Collection.lean:
    import OpenSheaf.Archive

    namespace OpenSheaf

    variable {D : Type} (hash : Hash D)

## The head of an object

The pin of the head of a live object names its last version, with the
digest of the inventory of that version. An object with no version, or an
object taken down, has no head.

    /-- The pin of the head of a live object: its newest object version. -/
    def headPin (w : World D) (a : ArchiveId) (oid : ObjectId) : Option (Pin D) :=
      match lookup w a oid with
      | some (.live o) =>
        if o.versions.length = 0 then none
        else some ⟨a, oid, o.versions.length, hash (o.inventory o.versions.length)⟩
      | _ => none

## Updating a collection

A member of a catalogue with `follow` gets the pin of the head of its
object, when there is one; a member whose object has disappeared keeps its
pin, which verification will then report. A selection is returned as it is.

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

The new member list is deposited as a new version of the collection, a step
of [chapter 3](30-archive.md); the pins of the earlier versions of the
collection are therefore kept, by immutability. The history of a catalogue
is the history of what it pinned.

## What updating does

For a selection, nothing, whatever the state of the archives. The theorem
holds by the definition of `collect`: it records the rule of section 10.2
that tools "MUST NOT change revision sets on their own", rather than prove
something about it.

    /-- **Selections do not move.** Updating a selection leaves it as it is. -/
    theorem collect_selection (w : World D) {c : Members D} (h : c.type = .selection) :
        collect hash w c = c := by
      simp [collect, h]

    /-- Updating a collection keeps its type. -/
    theorem collect_type (w : World D) (c : Members D) : (collect hash w c).type = c.type := by
      unfold collect; split <;> rfl

For a catalogue, members with `follow` move to the head, and the others
stay.

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

## The head pin resolves

The pin given to a followed member is valid: it resolves, in the world in
which it was computed, to the last version of the object. With
immutability, it stays valid as the object grows; it then no longer names
the head, until the catalogue is updated again.

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

## Well-formed member lists

Section 10.2 sets rules on member lists. Every member is pinned: a member of
a catalogue has exactly one pin (`version` and `inventorySha512`), a member
of a selection a non-empty revision set and no `follow`. The model adds what
the specification takes for granted: the pins of a member name the
member's own archive and object.

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

The pin of a head names the object it is the head of.

    theorem headPin_names {w : World D} {a : ArchiveId} {oid : ObjectId} {p : Pin D}
        (h : headPin hash w a oid = some p) : p.archive = a ∧ p.object = oid := by
      unfold headPin at h
      split at h
      · split at h
        · contradiction
        · cases h; exact ⟨rfl, rfl⟩
      · contradiction

So updating a well-formed member list gives a well-formed one: the tools
cannot break the rules by following members.

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
