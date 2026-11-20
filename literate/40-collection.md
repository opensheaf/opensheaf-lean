# Catalogues and selections

A collection is a line whose versions hold a member list (section 8). The
two types of collection differ in what updating them does (sections 8.3
and 8.4, the command `osheaf collect`):

- in a **catalogue**, a member with `follow` is moved to the latest version
  of its line; the other members stay;
- a **selection** never moves: its revision sets change only by an act of
  its curator, a new version of the collection, which its owner signs. A
  tool updating a selection may report new versions of its members; it does
  not add them.

This chapter defines the update and proves what it does to each type,
together with the fact that the pin given to a followed member resolves, to
the head of the first copy found. That only the curator changes a
selection follows from [chapter 8](47-acts.md), which says who signs a
step: every version of a selection is signed with its curator's keys
(`forgery_needs_owner_key`, applied to the selection's line).

The model simplifies the member of a selection: section 8.4 gives each
revision its `documentVersion`, beside the pin of the object version vetted,
in the order of the document's history. The model keeps only the pins, so
it neither records nor checks those document versions
([model issue 2](https://github.com/opensheaf/opensheaf-lean/issues/2)).

    -- in OpenSheaf/Collection.lean:
    import OpenSheaf.Archive

    namespace OpenSheaf

    variable {D : Type} (hash : Hash D)

## The latest version of a line

"A followed member pins the latest signed version of its line (section
7.3) when the collection version was made" (section 8.3); a tool "reads the
member's archive (its discovery document or feed)". The model's tool looks
at the member's hints in order, and takes the head of the first copy of the
line it finds: the pin of its last version, with the digest of the
inventory of that version, and the member's hints. Whether that head is
signed is a matter of the copy: in worlds built by valid steps, the head of
every copy was signed when it was added ([chapter 7](45-worlds.md)). A
line with no copy at the hints, or only tombstones, has no head there.

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

## Updating a collection

A member of a catalogue with `follow` gets the pin of the head of its
line, when there is one; a member whose line has disappeared from its hints
keeps its pin, which verification will then report. A selection is
returned as it is.

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

The new member list is deposited as a new version of the collection, a step
of [chapter 3](30-archive.md), signed by its curator; the pins of the
earlier versions of the collection are therefore kept, by immutability. The
history of a catalogue is the history of what it pinned.

## What updating does

For a selection, nothing, whatever the state of the archives. The theorem
holds by the definition of `collect`: it records the rule of section 8.4
that tools "MUST NOT change revision sets on their own", rather than prove
something about it.

    /-- **Selections do not move.** Updating a selection leaves it as it is. -/
    theorem collect_selection (w : World D) {c : Members D} (h : c.type = .selection) :
        collect hash w c = c := by
      simp [collect, h]

For a catalogue, members with `follow` move to the head, and the others
stay.

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

## The head pin resolves

The pin given to a followed member is valid: it resolves, in the world in
which it was computed, at one of its hints, to the last version of the
copy kept there. With immutability, it stays valid as the line grows; it
then no longer names the head, until the catalogue is updated again.

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

## Well-formed member lists

Section 8 sets rules on member lists. Every member is pinned (section 8.5)
and has a non-empty `at` (section 8.2): a member of a catalogue has exactly
one pin (`version` and `inventorySha512`, section 8.3), a member of a
selection a non-empty revision set and no `follow` (section 8.4). The model
adds what the specification takes for granted: the pins of a member name
the member's line, and carry its hints.

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

So updating a well-formed member list gives a well-formed one: the tools
cannot break the rules by following members. The pin of a head names the
line it is the head of, and carries the hints it was looked up with
(`headPin_resolves`, above).

    /-- **Updating keeps a member list well formed.** -/
    theorem collect_wf [DecidableEq D] (w : World D) {c : Members D} (h : c.WF) : (collect hash w c).WF := by
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
            obtain ⟨hh, _, _, _, _, _, hl, _⟩ := headPin_resolves hash hp
            refine ⟨hmw.1, by simp, ?_, fun _ => rfl, fun h => nomatch h⟩
            intro q hq
            simp only [List.mem_singleton] at hq
            subst hq
            exact ⟨hl, hh⟩
          · exact hmw
        · exact hmw

    end OpenSheaf
