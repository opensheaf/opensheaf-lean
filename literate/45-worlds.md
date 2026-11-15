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
- an object kept by an archive other than its own is a mirror, whose history
  is a prefix of the original's (section 10.4; [chapter 6](48-copies.md));
- every pin held by any version resolves, so that, without takedowns,
  nothing ever dangles.

The last condition is a **modelling choice**, stronger than the
specification. Section 10.2 asks that every member be pinned, not that every
pin resolve when it is made: section 14 reports pins as "unavailable", and
issue #29 discusses pins of objects that readers cannot reach. The model
asks that a tool resolve every pin it writes, as the reference tools do.
The freedom from cycles of [chapter 10](65-impossible.md) rests on this
choice; for pins of versions that cannot be reached, it rests on the
hashes, which the model does not use there.

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

    /-- Every pin held by a version of a live object resolves. -/
    def PinsOk (w : World D) : Prop :=
      ∀ a oid o, lookup w a oid = some (.live o) →
        ∀ v ∈ o.versions, ∀ p ∈ v.pins, ∃ t, resolve hash w p = .ok t

    /-- A well-formed world. -/
    def WFWorld (w : World D) : Prop :=
      (∀ a oid o, lookup w a oid = some (.live o) → o.WF oid) ∧ PinsOk hash w

The empty world, with no archive, is well formed.

    theorem WFWorld.empty : WFWorld hash (fun _ => (none : Option (Archive D))) :=
      ⟨fun _ _ _ h => by simp [lookup] at h, fun _ _ _ h => by simp [lookup] at h⟩

## Valid steps

A valid step is a step with the checks of the specification:

- a new archive is empty;
- a new object is well formed, and the pins of its versions resolve at the
  time it is created, so that it pins only versions that already exist;
- a new object version extends the history (section 7.3, with the choice
  of [chapter 2](20-object.md)), does not make a withdrawn object active
  again (the choice of chapter 2 on issue #25), has a member list exactly if
  the object is a collection, and then a well-formed one, and pins only
  versions that resolve;
- an object is created in its own archive, or else is a mirror: a copy of a
  prefix of the history of a live object of another archive, under the same
  identifier (section 10.4); a version is appended to a mirror only by
  copying the next version of the original.

The check on pins is what a tool does when it writes a collection version:
it resolves each member before pinning it.

    omit [DecidableEq D] in
    /-- `o`, to be kept by archive `a`, is a mirror: it belongs to another
    archive, whose live object of the same identifier, its original, belongs to
    that archive and extends its history. -/
    def MirrorOf (w : World D) (a : ArchiveId) (o : Obj D) : Prop :=
      o.archive ≠ a ∧ ∃ orig, lookup w o.archive o.id = some (.live orig) ∧
        orig.archive = o.archive ∧ ∃ t, orig.versions = o.versions ++ t

    omit [DecidableEq D] in
    /-- `x` is the next version of the original of the mirror `o`. -/
    def MirrorNext (w : World D) (o : Obj D) (x : Version D) : Prop :=
      ∃ orig, lookup w o.archive o.id = some (.live orig) ∧ orig.archive = o.archive ∧
        ∃ t, orig.versions = o.versions ++ x :: t

    /-- The steps that the specification allows. -/
    inductive ValidStep : World D → World D → Prop
      | newArchive (w : World D) (a : ArchiveId) (ar : Archive D) (h : w a = none)
          (hempty : ∀ x, ar.entries x = none) :
          ValidStep w (fun b => if b = a then some ar else w b)
      | create (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
          (ha : w a = some ar) (ho : ar.entries oid = none) (hwf : o.WF oid)
          (hpins : ∀ v ∈ o.versions, ∀ p ∈ v.pins, ∃ t, resolve hash w p = .ok t)
          (hhome : o.archive = a ∨ MirrorOf w a o) :
          ValidStep w (setEntry w a oid (.live o))
      | append (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
          (x : Version D) (ha : w a = some ar) (ho : ar.entries oid = some (.live o))
          (hf : Extends o.versions x) (hst : NoReinstatement o.versions x)
          (hk : x.members.isSome = true ↔ o.kind = .collection) (hm : x.membersOk)
          (hpins : ∀ p ∈ x.pins, ∃ t, resolve hash w p = .ok t)
          (hhome : o.archive = a ∨ MirrorNext w o x) :
          ValidStep w (setEntry w a oid (.live (o.append x)))

    /-- Any number of valid steps. -/
    inductive ValidSteps : World D → World D → Prop
      | refl (w : World D) : ValidSteps w w
      | tail {w w' w'' : World D} : ValidSteps w w' → ValidStep hash w' w'' → ValidSteps w w''

A valid step is a step, so everything proved about steps holds of valid
steps, immutability first.

    theorem ValidStep.toStep {w w' : World D} (h : ValidStep hash w w') : Step w w' := by
      cases h with
      | newArchive a ar h _ => exact .newArchive w a ar h
      | create a ar oid o ha ho _ _ _ => exact .create w a ar oid o ha ho
      | append a ar oid o x ha ho _ _ _ _ _ _ => exact .append w a ar oid o x ha ho

    theorem ValidSteps.toSteps {w w' : World D} (h : ValidSteps hash w w') : Steps w w' := by
      induction h with
      | refl => exact .refl _
      | tail _ hs ih => exact .tail ih (hs.toStep hash)

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
        lookup w' b x = some (.tomb n d) := by
      induction hs with
      | refl => exact h
      | tail _ hstep ih => exact hstep.tomb_stays ih

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
        o'.WF x ∧ ∀ v ∈ o'.versions, ∀ p ∈ v.pins, Q p ∨ ∃ t, resolve hash w p = .ok t := by
      cases hs with
      | newArchive a ar ha hempty =>
        by_cases hb : b = a
        · subst hb; simp [lookup, hempty] at h
        · have hl : lookup w b x = some (.live o') := by simpa [lookup, hb] using h
          exact ⟨hobj _ _ _ hl, fun v hv p hp => Or.inl (hq _ _ _ hl v hv p hp)⟩
      | create a ar oid o ha ho hwf hpins _ =>
        rw [lookup_setEntry ha] at h
        split at h
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases h
          exact ⟨hwf, fun v hv p hp => Or.inr (hpins v hv p hp)⟩
        · exact ⟨hobj _ _ _ h, fun v hv p hp => Or.inl (hq _ _ _ h v hv p hp)⟩
      | append a ar oid o y ha ho hf _ hk hm hpins _ =>
        rw [lookup_setEntry ha] at h
        split at h
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases h
          have hl : lookup w b x = some (.live o) := by simp [lookup, ha, ho]
          have hwf := hobj _ _ _ hl
          refine ⟨⟨hwf.id, by simp [Obj.append], hwf.history.snoc hf, ?_, ?_⟩, ?_⟩
          · intro v hv
            simp only [Obj.append, List.mem_append, List.mem_singleton] at hv
            rcases hv with hv | rfl
            · exact hwf.kinds v hv
            · exact hk
          · intro v hv
            simp only [Obj.append, List.mem_append, List.mem_singleton] at hv
            rcases hv with hv | rfl
            · exact hwf.members v hv
            · exact hm
          · intro v hv p hp
            simp only [Obj.append, List.mem_append, List.mem_singleton] at hv
            rcases hv with hv | rfl
            · exact Or.inl (hq _ _ _ hl v hv p hp)
            · exact Or.inr (hpins p hp)
        · exact ⟨hobj _ _ _ h, fun v hv p hp => Or.inl (hq _ _ _ h v hv p hp)⟩

    /-- **Valid steps keep worlds well formed.** -/
    theorem ValidStep.wf {w w' : World D} (hs : ValidStep hash w w') (hw : WFWorld hash w) :
        WFWorld hash w' :=
      ⟨fun _ _ _ h => (hs.entry hash hw.1 hw.2 h).1,
       fun _ _ _ h v hv p hp => by
         obtain ⟨t, ht⟩ := ((hs.entry hash hw.1 hw.2 h).2 v hv p hp).elim id id
         exact ⟨t, Step.resolve_ok hash (hs.toStep hash) ht⟩⟩

    theorem ValidSteps.wf {w w' : World D} (hs : ValidSteps hash w w') (hw : WFWorld hash w) :
        WFWorld hash w' := by
      induction hs with
      | refl => exact hw
      | tail _ hstep ih => exact hstep.wf hash ih

The consequence: in archives built by valid steps from nothing, every pin
held by any version resolves. Takedowns are not steps; what they do to this
property is the subject of the next section.

    /-- **Nothing dangles.** -/
    theorem ValidSteps.pins_ok {w : World D}
        (hs : ValidSteps hash (fun _ => (none : Option (Archive D))) w) : PinsOk hash w :=
      (hs.wf hash (WFWorld.empty hash)).2

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
      refine ⟨(hmo m hm).1, fun p hp => hw.2 _ _ _ hl v hv p ?_⟩
      unfold Version.pins
      rw [hc]
      exact List.mem_flatMap.mpr ⟨m, hm, hp⟩

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
    inductive Events : World D → World D → Prop
      | refl (w : World D) : Events w w
      | tail {w w' w'' : World D} : Events w w' → Event hash w' w'' → Events w w''

After a takedown, pins of the object taken down no longer resolve; they
report `removed`. A pin reports `removed` exactly when its object has a
tombstone, and tombstones stay, so `removed` stays too.

    theorem resolve_removed_iff {w : World D} {p : Pin D} :
        resolve hash w p = .removed ↔ ∃ n d, lookup w p.archive p.object = some (.tomb n d) := by
      unfold resolve
      constructor
      · intro h
        match he : lookup w p.archive p.object, h with
        | some (.tomb n d), _ => exact ⟨n, d, rfl⟩
        | none, h => simp [resolveEntry] at h
        | some (.live o), h =>
          simp only [resolveEntry] at h
          split at h
          · cases h
          · split at h <;> cases h
      · rintro ⟨n, d, h⟩
        rw [h]; rfl

    theorem Step.resolve_removed {w w' : World D} (hs : Step w w') {p : Pin D}
        (h : resolve hash w p = .removed) : resolve hash w' p = .removed := by
      obtain ⟨n, d, hl⟩ := (resolve_removed_iff hash).mp h
      exact (resolve_removed_iff hash).mpr ⟨n, d, hs.tomb_stays hl⟩

The property that events keep: objects are well formed, and every pin held
resolves to a version or reports `removed`.

    /-- Every pin held resolves, or reports `removed`. -/
    def PinsHeld (w : World D) : Prop :=
      ∀ a oid o, lookup w a oid = some (.live o) →
        ∀ v ∈ o.versions, ∀ p ∈ v.pins, (∃ t, resolve hash w p = .ok t) ∨ resolve hash w p = .removed

    /-- A sound world: well-formed objects, and pins held resolve or report removed. -/
    def SoundWorld (w : World D) : Prop :=
      (∀ a oid o, lookup w a oid = some (.live o) → o.WF oid) ∧ PinsHeld hash w

    theorem ValidStep.sound {w w' : World D} (hs : ValidStep hash w w') (hw : SoundWorld hash w) :
        SoundWorld hash w' :=
      ⟨fun _ _ _ h => (hs.entry hash hw.1 hw.2 h).1,
       fun _ _ _ h v hv p hp => by
         rcases (hs.entry hash hw.1 hw.2 h).2 v hv p hp with (⟨t, ht⟩ | hr) | ⟨t, ht⟩
         · exact Or.inl ⟨t, Step.resolve_ok hash (hs.toStep hash) ht⟩
         · exact Or.inr (Step.resolve_removed hash (hs.toStep hash) hr)
         · exact Or.inl ⟨t, Step.resolve_ok hash (hs.toStep hash) ht⟩⟩

A takedown leaves every other object as it was. The pins of the others
resolve as before, except those of the object taken down, which report
`removed`.

    omit [DecidableEq D] in
    theorem lookup_takedown {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl : lookup w a oid = some (.live o)) {b : ArchiveId} {x : ObjectId} {o' : Obj D}
        (h : lookup (takedown hash w a oid o) b x = some (.live o')) :
        ¬ (b = a ∧ x = oid) ∧ lookup w b x = some (.live o') := by
      obtain ⟨ar, ha⟩ := lookup_some_archive hl
      unfold takedown tombstone at h
      rw [lookup_setEntry ha] at h
      split at h
      · cases h
      · rename_i hc; exact ⟨hc, h⟩

    theorem takedown_sound {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl : lookup w a oid = some (.live o)) (hw : SoundWorld hash w) :
        SoundWorld hash (takedown hash w a oid o) := by
      refine ⟨fun b x o' h => hw.1 _ _ _ (lookup_takedown hash hl h).2, ?_⟩
      intro b x o' h v hv p hp
      by_cases hpa : p.archive = a ∧ p.object = oid
      · exact Or.inr (takedown_removed hash hl hpa)
      · rw [takedown_other hash hl hpa]
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
        (hs : Events hash (fun _ => (none : Option (Archive D))) w) : SoundWorld hash w := by
      induction hs with
      | refl => exact ⟨(WFWorld.empty hash).1, fun _ _ _ h => by simp [lookup] at h⟩
      | tail _ he ih => exact he.sound hash ih

Tombstones stay through events too: a takedown leaves other entries as they
were, and the entry it changes was live.

    theorem Event.tomb_stays {w w' : World D} (he : Event hash w w') {b : ArchiveId}
        {x : ObjectId} {n : Nat} {d : D} (h : lookup w b x = some (.tomb n d)) :
        lookup w' b x = some (.tomb n d) := by
      cases he with
      | step hs => exact (hs.toStep hash).tomb_stays h
      | takedown a oid o hl =>
        obtain ⟨ar, ha⟩ := lookup_some_archive hl
        unfold OpenSheaf.takedown tombstone
        rw [lookup_setEntry ha]
        split
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          rw [hl] at h; cases h
        · exact h

    theorem Events.tomb_stays {w w' : World D} (hs : Events hash w w') {b : ArchiveId}
        {x : ObjectId} {n : Nat} {d : D} (h : lookup w b x = some (.tomb n d)) :
        lookup w' b x = some (.tomb n d) := by
      induction hs with
      | refl => exact h
      | tail _ he ih => exact he.tomb_stays hash ih

    end OpenSheaf
