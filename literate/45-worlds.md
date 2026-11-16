# Well-formed worlds

The steps of [chapter 3](30-archive.md) accept anything: an object with no
version, a version whose document version jumps from 2 to 5, a collection
version without a member list, a pin of a version that does not exist.
Immutability holds all the same, and it is worth knowing that it does not
depend on good behaviour. But the specification asks for more, and this
chapter says what: it defines **valid steps**, which check what the
specification requires of each new object and object version, and proves
that they keep the archives **well formed**:

- every object is stored under its own identifier, has at least one
  version, and has a well-formed history of document versions
  ([chapter 2](20-object.md));
- the versions of a collection, and only those, have member lists
  (section 7.4), and these lists obey the rules of section 10.2
  ([chapter 4](40-collection.md));
- and, proved in [chapter 6](48-copies.md) rather than part of the
  definition: an object kept by an archive other than its own is a mirror,
  whose history is a prefix of the original's (section 10.4);
- every pin held by any version resolves, so that, without takedowns,
  nothing ever dangles.

Valid steps check the last condition on every pin they write: it resolves,
or reports `removed`. This is a **modelling choice**, stronger than the
specification. Section 10.2 asks that every member be pinned, not that every
pin resolve when it is made: section 14 reports pins as "unavailable", and
issue #29 discusses pins of objects that readers cannot reach. The model
asks that a tool resolve every pin it writes, as the reference tools do.
A pin that reports `removed` is accepted only when it is carried over,
held already by a version of the world: after a takedown, a collection
keeps the pins of the object taken down in its later versions (a
withdrawal, a description, an update), and a mirror copies them (sections
10.2 and 11.3). A pin made afresh into an object taken down is refused.
Such a pin names an object that never comes back, so it never resolves
again. The freedom from cycles of
[chapter 10](65-impossible.md) rests on the first half of this choice, that
a pin resolves, or reports `removed`, when it is made; for pins of versions
that cannot be reached, it would rest on the hashes, which the model does
not use there.

The chapter also proves two facts about all steps, valid or not: an
identifier taken down is never reused, and an object only grows, so that
every earlier version of a collection, with its member list, is kept.
Finally it adds takedowns to the valid steps, as **events**, and proves
what remains true: every pin held resolves to a version or reports
`removed`, and tombstones stay.

    -- in OpenSheaf/Worlds.lean:
    import OpenSheaf.Collection

    namespace OpenSheaf

    variable {D : Type} [DecidableEq D] (hash : Hash D)

## Well-formed objects and worlds

    omit [DecidableEq D] in
    /-- The member list of a version, if any, is well formed. -/
    def Version.membersOk (v : Version D) : Prop :=
      match v.members with
      | none => True
      | some c => c.WF

    omit [DecidableEq D] in
    instance (v : Version D) : Decidable v.membersOk := by
      unfold Version.membersOk; split <;> infer_instance

    /-- A well-formed object stored under `oid` (sections 7, 7.4 and 10.2). -/
    structure Obj.WF (o : Obj D) (oid : ObjectId) : Prop where
      id : o.id = oid
      nonempty : o.versions ≠ []
      history : WellFormed o.versions
      kinds : ∀ v ∈ o.versions, v.members.isSome = true ↔ o.kind = .collection
      members : ∀ v ∈ o.versions, v.membersOk
      statuses : StatusOk o.versions

    /-- Every pin held by a version of a live object resolves. -/
    def PinsOk (w : World D) : Prop :=
      ∀ a oid o, lookup w a oid = some (.live o) →
        ∀ v ∈ o.versions, ∀ p ∈ v.pins, ∃ t, resolve hash w p = .ok t

    omit [DecidableEq D] in
    /-- No object has been taken down. -/
    def NoTombs (w : World D) : Prop := ∀ a oid n d, lookup w a oid ≠ some (.tomb n d)

A world is well formed when its objects are, its pins resolve, and, since
it is built without takedowns, it holds no tombstone.

    /-- A well-formed world. -/
    def WFWorld (w : World D) : Prop :=
      (∀ a oid o, lookup w a oid = some (.live o) → o.WF oid) ∧ PinsOk hash w ∧ NoTombs w

The empty world, with no archive, is well formed.

    theorem WFWorld.empty : WFWorld hash (fun _ => (none : Option (Archive D))) :=
      ⟨fun _ _ _ h => by simp [lookup] at h, fun _ _ _ h => by simp [lookup] at h,
        fun _ _ _ _ h => by simp [lookup] at h⟩

## Valid steps

A valid step is a step with the checks of the specification:

- a new archive is empty;
- a new object is well formed (its history does not reinstate a withdrawn
  object, the choice of [chapter 2](20-object.md) on issue #25), and the
  pins of its versions resolve, or report `removed` and are carried over,
  at the time it is created, so that it pins only versions that already
  exist;
- a new object version extends the history (section 7.3, with the choice
  of chapter 2), does not make a withdrawn object active again, has a
  member list exactly if the object is a collection, and then a
  well-formed one, and pins only versions that resolve, or report
  `removed` and are carried over;
- a version that records the version it copies (an accepted copy, section
  10.5) holds exactly its files, when the source resolves;
- in a version that an archive makes of its own catalogue (a new object
  version, or the head of a new object), every member with `follow` pins
  the head of its object, when the object has one: "A followed member pins
  the head of the object when the collection version was made" (section
  10.2). Mirrors are exempt: they copy versions made earlier;
- an object is created in its own archive, or else is a mirror: a copy of a
  prefix of the history of a live object of another archive, under the same
  identifier (section 10.4); a version is appended to a mirror only if the
  mirror stays such a copy, that is, by copying the next version of the
  original.

The check on pins is what a tool does when it writes a collection version:
it resolves each member before pinning it.

One predicate says what a mirror is, for both checks: the object is a copy
of a prefix of its original, the live object of the same identifier in the
object's own archive. A step that is not in the object's own archive must
keep it so. This is a **modelling choice**: section 10.4 asks a mirror to
copy "the whole object, every version"; the model accepts at creation a
copy of any prefix, as issue #13 of the specification discusses (copies up
to the pinned version) ([model issue 6](https://github.com/opensheaf/opensheaf-lean/issues/6)).

    omit [DecidableEq D] in
    /-- `o` is a copy of a prefix of its original: the live object of the same
    identifier in `o`'s own archive, which belongs to that archive. -/
    def MirrorOf (w : World D) (o : Obj D) : Prop :=
      ∃ orig, lookup w o.archive o.id = some (.live orig) ∧
        orig.archive = o.archive ∧ ∃ t, orig.versions = o.versions ++ t

A pin held by a version resolves, or reports `removed`:

    /-- The pin resolves, or reports `removed`. -/
    abbrev Held (w : World D) (p : Pin D) : Prop :=
      (∃ t, resolve hash w p = .ok t) ∨ resolve hash w p = .removed

The check on followed members. A member whose object has no head (it was
taken down) keeps its pin, as `collect` does ([chapter 4](40-collection.md)).
The check applies to every new version of an archive's own catalogue, as
section 10.2 reads ("when the collection version was made"). So once a
followed member has moved, the catalogue can get no description-only
version, nor a withdrawal: the new version would have to pin the new head,
which changes its member list, its content. The specification has the same
tension, raised as
[issue #45](https://github.com/opensheaf/opensheaf.github.io/issues/45).

    /-- A followed member pins the head of its object in `w`, if any. -/
    def Member.FollowsHead (w : World D) (m : Member D) : Prop :=
      match headPin hash w m.archive m.object with
      | some p => m.pins = [p]
      | none => True

    instance (w : World D) (m : Member D) : Decidable (m.FollowsHead hash w) := by
      unfold Member.FollowsHead; split <;> infer_instance

    /-- In a catalogue version, the followed members pin the heads of their
    objects in `w` (section 10.2). -/
    def Version.FollowsHeads (w : World D) (v : Version D) : Prop :=
      match v.members with
      | some c => c.type = .catalogue → ∀ m ∈ c.members, m.follow = true → m.FollowsHead hash w
      | none => True

    instance (w : World D) (v : Version D) : Decidable (v.FollowsHeads hash w) := by
      unfold Version.FollowsHeads; split <;> infer_instance

    /-- The last version of a history, if any, follows heads. -/
    def HeadFollows (w : World D) (l : List (Version D)) : Prop :=
      match l.getLast? with
      | some x => x.FollowsHeads hash w
      | none => True

    instance (w : World D) (l : List (Version D)) : Decidable (HeadFollows hash w l) := by
      unfold HeadFollows; split <;> infer_instance

A new version may hold a pin that reports `removed`, but only one that the
world already holds: a description-only version of a collection after one of
its members was taken down keeps that member's pin, and a mirror copies the
pins of its original. A pin made afresh must resolve. Without this rule a
step could write a pin, with any number and any digest, into an object taken
down, which no verifier could ever check.

    omit [DecidableEq D] in
    /-- Some version of a live object of the world holds the pin. -/
    def HeldBy (w : World D) (p : Pin D) : Prop :=
      ∃ b i c v, lookup w b i = some (.live c) ∧ v ∈ c.versions ∧ p ∈ v.pins

    /-- A pin a new version may hold: it resolves, or it reports `removed` and
    is carried over from a version the world already holds. -/
    def PinOk (w : World D) (p : Pin D) : Prop :=
      (∃ t, resolve hash w p = .ok t) ∨ (resolve hash w p = .removed ∧ HeldBy w p)

    theorem PinOk.held {w : World D} {p : Pin D} (h : PinOk hash w p) : Held hash w p :=
      h.elim Or.inl fun h => Or.inr h.1

A version that records the version it copies (an accepted copy, section
10.5) holds exactly that version's files, when the source resolves. Section
14 asks the verifier to check this "when the source is available"; the
model asks the step to, and goes further than the specification in three
ways, each a **modelling choice**:

- the files are compared as lists, path, digest and order, where content
  is elsewhere compared as a set; a copy made by the tools lists them in
  the same order;
- the check applies to every version that records a source, not only to
  the first document version of an accepted copy (sections 10.5 and 14); a
  later version of the copy that keeps the field must keep the files too;
- the source must resolve when the version is made, or report `removed`
  and be recorded already by a version of the world, as for pins; a source
  that is unavailable is refused, where section 14 would skip the check.

    /-- The source a version records, if any, is checked (sections 10.5, 14). -/
    def SourceOk (w : World D) (x : Version D) : Prop :=
      ∀ src, x.source = some src →
        (∃ u, resolve hash w src = .ok u ∧ x.files = u.files) ∨
        (resolve hash w src = .removed ∧
          ∃ b i c y, lookup w b i = some (.live c) ∧ y ∈ c.versions ∧ y.source = some src)

    theorem sourceOk_none {w : World D} {x : Version D} (h : x.source = none) :
        SourceOk hash w x := by
      intro src hs; rw [h] at hs; cases hs

    theorem sourceOk_all_none {w : World D} {l : List (Version D)}
        (h : (l.all fun v => v.source.isNone) = true) : ∀ v ∈ l, SourceOk hash w v := by
      intro v hv
      apply sourceOk_none
      have := List.all_eq_true.mp h v hv
      simpa using this

    /-- The steps that the specification allows. -/
    inductive ValidStep : World D → World D → Prop
      | newArchive (w : World D) (a : ArchiveId) (ar : Archive D) (h : w a = none)
          (hempty : ∀ x, ar.entries x = none) :
          ValidStep w (fun b => if b = a then some ar else w b)
      | create (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
          (ha : w a = some ar) (ho : ar.entries oid = none) (hwf : o.WF oid)
          (hpins : ∀ v ∈ o.versions, ∀ p ∈ v.pins, PinOk hash w p)
          (hhome : o.archive = a ∨ MirrorOf w o)
          (hfollow : o.archive = a → HeadFollows hash w o.versions)
          (hsrc : ∀ v ∈ o.versions, SourceOk hash w v) :
          ValidStep w (setEntry w a oid (.live o))
      | append (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
          (x : Version D) (ha : w a = some ar) (ho : ar.entries oid = some (.live o))
          (hf : Extends o.versions x) (hst : NoReinstatement o.versions x)
          (hk : x.members.isSome = true ↔ o.kind = .collection) (hm : x.membersOk)
          (hpins : ∀ p ∈ x.pins, PinOk hash w p)
          (hhome : o.archive = a ∨ MirrorOf w (o.append x))
          (hfollow : o.archive = a → x.FollowsHeads hash w)
          (hsrc : SourceOk hash w x) :
          ValidStep w (setEntry w a oid (.live (o.append x)))

    /-- Any number of valid steps. -/
    abbrev ValidSteps : World D → World D → Prop := Star (ValidStep hash)

A valid step is a step, so everything proved about steps holds of valid
steps, immutability first.

    theorem ValidStep.toStep {w w' : World D} (h : ValidStep hash w w') : Step w w' := by
      cases h with
      | newArchive a ar h _ => exact .newArchive w a ar h
      | create a ar oid o ha ho => exact .create w a ar oid o ha ho
      | append a ar oid o x ha ho => exact .append w a ar oid o x ha ho

    theorem ValidSteps.toSteps {w w' : World D} (h : ValidSteps hash w w') : Steps w w' :=
      h.mono (·.toStep hash)

## What a step does to an entry

Every proof below asks what a step did to the entry of one object. There
are three answers: nothing; the entry was empty before (a new object, or an
object of a new archive); a version was appended to the object.

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

Two consequences: an entry that is not empty stays so, and a live entry
after a step is the one before, or it with one more version.

    omit [DecidableEq D] in
    theorem Step.ne_none {w w' : World D} (hs : Step w w') {b : ArchiveId} {x : ObjectId}
        (h : lookup w b x ≠ none) : lookup w' b x ≠ none := by
      rcases hs.lookup_cases b x with h1 | h1 | ⟨o, v, _, h2⟩
      · rw [h1]; exact h
      · exact absurd h1 h
      · rw [h2]; simp

    omit [DecidableEq D] in
    theorem Step.live_back {w w' : World D} (hs : Step w w') {b : ArchiveId} {x : ObjectId}
        {o' : Obj D} (h : lookup w' b x = some (.live o')) (hne : lookup w b x ≠ none) :
        lookup w b x = some (.live o') ∨
          ∃ o v, lookup w b x = some (.live o) ∧ o' = o.append v := by
      rcases hs.lookup_cases b x with h1 | h1 | ⟨o, v, h1, h2⟩
      · left; rw [← h1]; exact h
      · exact absurd h1 hne
      · right
        rw [h2] at h
        exact ⟨o, v, h1, (Entry.live.inj (Option.some.inj h)).symm⟩

## Identifiers are not reused

A tombstone stays: no step replaces it, since a new object needs an empty
entry and a new version a live one. An identifier taken down (section 11.3)
can therefore never name another object, and a pin of the object taken down
can never resolve to something else.

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
        lookup w' b x = some (.tomb n d) :=
      hs.invariant (fun w => lookup w b x = some (.tomb n d)) (·.tomb_stays) h

## Objects only grow

A live object stays live, keeps its identifier and kind, and its history
only grows. For a collection: every change of its member list is a new
version, which records who deposited it and why (the depositor and the
message), and every earlier member list is kept, as a prefix of the
history. This is half of section 10.2's "the selection changes only by an
explicit act of its curator, which is a new version of the selection". The
other half, that only the curator may make that version, needs to know who
makes a step: it is proved in [chapter 7](49-acts.md).

    omit [DecidableEq D] in
    /-- **Objects only grow.** -/
    theorem Step.live_grows {w w' : World D} (hs : Step w w') {b : ArchiveId} {x : ObjectId}
        {o : Obj D} (h : lookup w b x = some (.live o)) :
        ∃ o', lookup w' b x = some (.live o') ∧ o'.archive = o.archive ∧ o'.id = o.id ∧
          o'.kind = o.kind ∧ ∃ t, o'.versions = o.versions ++ t := by
      rcases hs.lookup_cases b x with h1 | h1 | ⟨o1, v, h1, h2⟩
      · exact ⟨o, by rw [h1, h], rfl, rfl, rfl, [], by simp⟩
      · rw [h] at h1; cases h1
      · rw [h] at h1; cases h1
        exact ⟨o.append v, h2, rfl, rfl, rfl, [v], rfl⟩

    omit [DecidableEq D] in
    theorem Steps.live_grows {w w' : World D} (hs : Steps w w') {b : ArchiveId} {x : ObjectId}
        {o : Obj D} (h : lookup w b x = some (.live o)) :
        ∃ o', lookup w' b x = some (.live o') ∧ o'.id = o.id ∧ o'.kind = o.kind ∧
          ∃ t, o'.versions = o.versions ++ t := by
      refine hs.invariant (fun w => ∃ o', lookup w b x = some (.live o') ∧ o'.id = o.id ∧
        o'.kind = o.kind ∧ ∃ t, o'.versions = o.versions ++ t) ?_ ⟨o, h, rfl, rfl, [], by simp⟩
      rintro _ _ hstep ⟨o1, h1, hid1, hk1, t1, ht1⟩
      obtain ⟨o2, h2, _, hid2, hk2, t2, ht2⟩ := hstep.live_grows h1
      exact ⟨o2, h2, hid2.trans hid1, hk2.trans hk1, t1 ++ t2, by rw [ht2, ht1, List.append_assoc]⟩

## Valid steps keep worlds well formed

The main theorem of the chapter. An entry after a valid step is either an
entry of before, or the object just created, or an object with a version
just appended; in each case it is well formed. The pins of its versions are
either pins held before the step, or pins checked by it, which resolved
before it. The lemma is stated for any property `Q` of the pins held
before, so that it serves twice: here, and for takedowns below.

    theorem ValidStep.entry {w w' : World D} (hs : ValidStep hash w w')
        (hobj : ∀ a oid o, lookup w a oid = some (.live o) → o.WF oid)
        {Q : Pin D → Prop} (hq : ∀ a oid o, lookup w a oid = some (.live o) →
          ∀ v ∈ o.versions, ∀ p ∈ v.pins, Q p)
        {b : ArchiveId} {x : ObjectId} {o' : Obj D} (h : lookup w' b x = some (.live o')) :
        o'.WF x ∧ ∀ v ∈ o'.versions, ∀ p ∈ v.pins, Q p ∨ Held hash w p := by
      cases hs with
      | newArchive a ar ha hempty =>
        rw [lookup_newArchive ha hempty] at h
        exact ⟨hobj _ _ _ h, fun v hv p hp => Or.inl (hq _ _ _ h v hv p hp)⟩
      | create a ar oid o ha ho hwf hpins _ =>
        rw [lookup_setEntry ha] at h
        split at h
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases h
          exact ⟨hwf, fun v hv p hp => Or.inr (hpins v hv p hp).held⟩
        · exact ⟨hobj _ _ _ h, fun v hv p hp => Or.inl (hq _ _ _ h v hv p hp)⟩
      | append a ar oid o y ha ho hf hst hk hm hpins _ =>
        rw [lookup_setEntry ha] at h
        split at h
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases h
          have hl : lookup w b x = some (.live o) := by simp [lookup, ha, ho]
          have hwf := hobj _ _ _ hl
          refine ⟨⟨hwf.id, by simp [Obj.append], hwf.history.snoc hf, ?_, ?_,
            hwf.statuses.snoc hst⟩, ?_⟩
          · simpa [Obj.append, or_imp, forall_and] using ⟨hwf.kinds, hk⟩
          · simpa [Obj.append, or_imp, forall_and] using ⟨hwf.members, hm⟩
          · simpa [Obj.append, or_imp, forall_and] using
              ⟨fun v hv p hp => Or.inl (hq _ _ _ hl v hv p hp), fun p hp => Or.inr (hpins p hp).held⟩
        · exact ⟨hobj _ _ _ h, fun v hv p hp => Or.inl (hq _ _ _ h v hv p hp)⟩

Valid steps create no tombstone: a new archive is empty, and the other
steps write live objects.

    theorem ValidStep.noTombs {w w' : World D} (hs : ValidStep hash w w') (h : NoTombs w) :
        NoTombs w' := by
      intro b x n d hl
      cases hs with
      | newArchive a ar ha hempty => rw [lookup_newArchive ha hempty] at hl; exact h _ _ _ _ hl
      | create a ar oid o ha =>
        rw [lookup_setEntry ha] at hl
        split at hl
        · cases hl
        · exact h _ _ _ _ hl
      | append a ar oid o y ha =>
        rw [lookup_setEntry ha] at hl
        split at hl
        · cases hl
        · exact h _ _ _ _ hl

So, without takedowns, a pin written by a valid step resolves: none reports
`removed`.

    /-- **Valid steps keep worlds well formed.** -/
    theorem ValidStep.wf {w w' : World D} (hs : ValidStep hash w w') (hw : WFWorld hash w) :
        WFWorld hash w' :=
      ⟨fun _ _ _ h => (hs.entry hash hw.1 hw.2.1 h).1,
       fun _ _ _ h v hv p hp => by
         rcases (hs.entry hash hw.1 hw.2.1 h).2 v hv p hp with ⟨t, ht⟩ | ⟨t, ht⟩ | hr
         · exact ⟨t, Step.resolve_ok hash (hs.toStep hash) ht⟩
         · exact ⟨t, Step.resolve_ok hash (hs.toStep hash) ht⟩
         · obtain ⟨n, d, hl⟩ := (resolve_removed_iff hash).mp hr
           exact absurd hl (hw.2.2 _ _ _ _),
       hs.noTombs hash hw.2.2⟩

    theorem ValidSteps.wf {w w' : World D} (hs : ValidSteps hash w w') (hw : WFWorld hash w) :
        WFWorld hash w' :=
      hs.invariant _ (·.wf hash) hw

The consequence: in archives built by valid steps from nothing, every pin
held by any version resolves. Takedowns are not steps; what they do to this
property is the subject of the next section.

    /-- **Nothing dangles.** -/
    theorem ValidSteps.pins_ok {w : World D}
        (hs : ValidSteps hash (fun _ => (none : Option (Archive D))) w) : PinsOk hash w :=
      (hs.wf hash (WFWorld.empty hash)).2.1

In such worlds every member of every collection is pinned, as section 10.2
asks, and its pins resolve.

    /-- **Every member is pinned.** -/
    theorem ValidSteps.members_pinned {w : World D}
        (hs : ValidSteps hash (fun _ => (none : Option (Archive D))) w)
        {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
        {v : Version D} (hv : v ∈ o.versions) {c : Members D} (hc : v.members = some c)
        {m : Member D} (hm : m ∈ c.members) :
        m.pins ≠ [] ∧ ∀ p ∈ m.pins, ∃ t, resolve hash w p = .ok t := by
      have hw := hs.wf hash (WFWorld.empty hash)
      have hmo := (hw.1 _ _ _ hl).members v hv
      unfold Version.membersOk at hmo
      rw [hc] at hmo
      refine ⟨(hmo m hm).1, fun p hp => hw.2.1 _ _ _ hl v hv p ?_⟩
      simp only [Version.pins, hc, Members.pins]
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨m, hm, hp⟩)

## Takedowns among the steps

Takedowns are not steps: they remove versions, against which pins were
made. They happen all the same, by law, and the model must say what they do
to the rest. An **event** is a valid step or a takedown of a live object.

    /-- A valid step, or a takedown (section 11.2). -/
    inductive Event : World D → World D → Prop
      | step {w w' : World D} : ValidStep hash w w' → Event w w'
      | takedown (w : World D) (a : ArchiveId) (oid : ObjectId) (o : Obj D)
          (hl : lookup w a oid = some (.live o)) : Event w (takedown hash w a oid o)

    /-- Any number of events. -/
    abbrev Events : World D → World D → Prop := Star (Event hash)

After a takedown, pins of the object taken down no longer resolve; they
report `removed`. A pin reports `removed` exactly when its object has a
tombstone (`resolve_removed_iff`, [chapter 3](30-archive.md)), and
tombstones stay, so `removed` stays too.

    theorem Step.resolve_removed {w w' : World D} (hs : Step w w') {p : Pin D}
        (h : resolve hash w p = .removed) : resolve hash w' p = .removed := by
      obtain ⟨n, d, hl⟩ := (resolve_removed_iff hash).mp h
      exact (resolve_removed_iff hash).mpr ⟨n, d, hs.tomb_stays hl⟩

The property that events keep: objects are well formed, and every pin held
resolves to a version or reports `removed`.

    /-- Every pin held resolves, or reports `removed`. -/
    def PinsHeld (w : World D) : Prop :=
      ∀ a oid o, lookup w a oid = some (.live o) →
        ∀ v ∈ o.versions, ∀ p ∈ v.pins, Held hash w p

    /-- A sound world: well-formed objects, and pins held resolve or report removed. -/
    def SoundWorld (w : World D) : Prop :=
      (∀ a oid o, lookup w a oid = some (.live o) → o.WF oid) ∧ PinsHeld hash w

    theorem SoundWorld.empty : SoundWorld hash (fun _ => (none : Option (Archive D))) :=
      ⟨(WFWorld.empty hash).1, fun _ _ _ h => by simp [lookup] at h⟩

    theorem ValidStep.sound {w w' : World D} (hs : ValidStep hash w w') (hw : SoundWorld hash w) :
        SoundWorld hash w' :=
      ⟨fun _ _ _ h => (hs.entry hash hw.1 hw.2 h).1,
       fun _ _ _ h v hv p hp => by
         rcases (hs.entry hash hw.1 hw.2 h).2 v hv p hp with (⟨t, ht⟩ | hr) | (⟨t, ht⟩ | hr)
         · exact Or.inl ⟨t, Step.resolve_ok hash (hs.toStep hash) ht⟩
         · exact Or.inr (Step.resolve_removed hash (hs.toStep hash) hr)
         · exact Or.inl ⟨t, Step.resolve_ok hash (hs.toStep hash) ht⟩
         · exact Or.inr (Step.resolve_removed hash (hs.toStep hash) hr)⟩

A takedown leaves every other object as it was (`lookup_takedown`,
[chapter 3](30-archive.md)). The pins of the others resolve as before,
except those of the object taken down, which report `removed`.

    theorem takedown_sound {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl : lookup w a oid = some (.live o)) (hw : SoundWorld hash w) :
        SoundWorld hash (takedown hash w a oid o) := by
      refine ⟨fun b x o' h => hw.1 _ _ _ (lookup_takedown hash hl h).2, ?_⟩
      intro b x o' h v hv p hp
      by_cases hpa : p.archive = a ∧ p.object = oid
      · exact Or.inr (takedown_removed hash hl hpa)
      · simp only [Held]; rw [takedown_other hash hl hpa]
        exact hw.2 _ _ _ (lookup_takedown hash hl h).2 v hv p hp

    theorem Event.sound {w w' : World D} (he : Event hash w w') (hw : SoundWorld hash w) :
        SoundWorld hash w' := by
      cases he with
      | step hs => exact hs.sound hash hw
      | takedown a oid o hl => exact takedown_sound hash hl hw

    /-- **Only a takedown stops a pin from resolving, and then it reports
    removed.** In a world built by events from nothing, every pin held by any
    version resolves or reports `removed`. -/
    theorem Events.sound {w : World D}
        (hs : Events hash (fun _ => (none : Option (Archive D))) w) : SoundWorld hash w :=
      hs.invariant _ (·.sound hash) (SoundWorld.empty hash)

Tombstones stay through events too: a takedown leaves other entries as they
were, and the entry it changes was live.

    theorem Event.tomb_stays {w w' : World D} (he : Event hash w w') {b : ArchiveId}
        {x : ObjectId} {n : Nat} {d : D} (h : lookup w b x = some (.tomb n d)) :
        lookup w' b x = some (.tomb n d) := by
      cases he with
      | step hs => exact (hs.toStep hash).tomb_stays h
      | takedown a oid o hl =>
        rw [lookup_takedown_eq hash hl, if_no (by rintro ⟨rfl, rfl⟩; simp [hl] at h)]
        exact h

    theorem Events.tomb_stays {w w' : World D} (hs : Events hash w w') {b : ArchiveId}
        {x : ObjectId} {n : Nat} {d : D} (h : lookup w b x = some (.tomb n d)) :
        lookup w' b x = some (.tomb n d) :=
      hs.invariant (fun w => lookup w b x = some (.tomb n d)) (·.tomb_stays hash) h

    end OpenSheaf
