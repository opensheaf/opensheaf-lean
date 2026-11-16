# What cannot happen

The previous chapters prove what the protocol does. This one proves what it
prevents: for each way of breaking it, an attempt is modelled and shown to
be impossible, or, where it can be made outside the protocol, to be
detected. These are the negative tests of the model.

| The break | Why it cannot happen |
|---|---|
| A pin changes its meaning | immutability: once a pin resolves to a version, no step changes that version |
| An archive rewrites the history of an object | no sequence of steps can; outside the protocol, every pin of a rewritten version stops resolving (unless the inventories collide) |
| An identifier taken down names another object | tombstones stay |
| One document version number for two contents, two numbers for one content, or a gap in the numbering | the counting rule of section 7.3 |
| Pins form a cycle (a version pins itself, or two collections pin each other) | valid steps pin only versions that exist already |
| A withdrawn object becomes active again | valid steps forbid it (the model's choice on issue #25) |

The fifth is stated in section 10.2 ("Pins cannot form cycles"), where
it is justified by the hashes. The model proves it from the protocol alone,
with no assumption on the digest function.

    -- in OpenSheaf/Impossible.lean:
    import OpenSheaf.Copies

    namespace OpenSheaf

    variable {D : Type} [DecidableEq D] (hash : Hash D)

## A pin cannot change its meaning

Immutability, stated as an impossibility: once a pin resolves to a version,
no sequence of steps makes it resolve to another.

    /-- **A pin cannot change its meaning.** -/
    theorem pin_meaning_fixed {w w' : World D} (hs : Steps w w') {p : Pin D} {v u : Version D}
        (hp : resolve hash w p = .ok v) (hne : u ≠ v) : resolve hash w' p ≠ .ok u := by
      rw [Steps.resolve_ok hash hs hp]
      intro h
      cases h
      exact hne rfl

## History cannot be rewritten

Within the protocol, an object only grows ([chapter 5](45-worlds.md)): its
history in a later world extends its history in an earlier one. A world in
which an archive has replaced, removed or reordered versions of an object
is therefore not reachable by any sequence of steps.

    omit [DecidableEq D] in
    /-- **History cannot be rewritten by any steps.** -/
    theorem history_not_rewritten {w w' : World D} (hs : Steps w w') {a : ArchiveId}
        {oid : ObjectId} {o o' : Obj D} (hl : lookup w a oid = some (.live o))
        (hl' : lookup w' a oid = some (.live o'))
        (hrew : o'.versions.take o.versions.length ≠ o.versions) : False := by
      obtain ⟨o2, h2, _, _, _, t, ht⟩ := Steps.live_grows hs hl
      rw [hl'] at h2
      cases h2
      apply hrew
      rw [ht, List.take_append_of_le_length (Nat.le_refl _), List.take_length]

An archive can still rewrite its files outside the protocol: nothing stops
the owner of a disk. Then every pin of a rewritten version, made before,
stops resolving: the digest in the pin is that of the original inventory,
and the rewritten inventory has another, unless the two collide
([chapter 6](48-copies.md)). Tampering is not prevented, it is detected, by
anyone holding a pin.

    /-- **Tampering is detected.** If an archive replaces an object by one whose
    history differs up to version `p.version`, a pin of that version made
    before resolves to no version at all. -/
    theorem tamper_detected {w : World D}
        {a : ArchiveId} {oid : ObjectId} {o o' : Obj D} (hl : lookup w a oid = some (.live o))
        {p : Pin D} {v : Version D} (hpa : p.archive = a ∧ p.object = oid)
        (hp : resolve hash w p = .ok v) (hdiff : o'.inventory p.version ≠ o.inventory p.version)
        (hcol : NoCollision hash (o'.inventory p.version) (o.inventory p.version))
        (u : Version D) : resolve hash (setEntry w a oid (.live o')) p ≠ .ok u := by
      obtain ⟨ar, ha⟩ := lookup_some_archive hl
      intro h
      unfold resolve at h hp
      rw [lookup_setEntry ha] at h
      simp only [hpa, and_self, ite_true] at h
      rw [hpa.1, hpa.2, hl] at hp
      obtain ⟨_, hd⟩ := resolveEntry_live_ok hash hp
      obtain ⟨_, hd'⟩ := resolveEntry_live_ok hash h
      exact hdiff (hcol (hd'.trans hd.symm))

## A tombstoned identifier cannot be reused

Section 11.3: "Identifiers of tombstoned objects MUST NOT be reused". In the
model it is not a rule that archives must remember: no step can do it.

    omit [DecidableEq D] in
    /-- **A tombstoned identifier is never reused.** -/
    theorem no_reuse {w w' : World D} (hs : Steps w w') {a : ArchiveId} {oid : ObjectId}
        {n : Nat} {d : D} (h : lookup w a oid = some (.tomb n d)) (o : Obj D) :
        lookup w' a oid ≠ some (.live o) := by
      rw [Steps.tomb_stays hs h]
      intro h'
      cases h'

## Document versions are unambiguous

Citations name document versions, so a number must mean one content, and
section 7.3 asks for numbers "from 1, without gaps". The counting rule of
[chapter 2](20-object.md) guarantees both. The proofs go along the history
from the end, with `snoc_induction` and `WellFormed.init` of chapter 2.

One number, one content: two versions of a well-formed history with the
same document version have the same content. The last version either holds
earlier content, and takes its number, or new content, and a number above
all the others.

    /-- **One document version, one content.** -/
    theorem one_number_one_content {l : List (Version D)} (h : WellFormed l)
        {v u : Version D} (hv : v ∈ l) (hu : u ∈ l)
        (heq : v.documentVersion = u.documentVersion) : sameContent v u = true := by
      induction l using snoc_induction generalizing v u with
      | nil => cases hv
      | snoc l x ih =>
        obtain ⟨hwf, hx⟩ := h.init
        have key : ∀ y ∈ l, y.documentVersion = x.documentVersion → sameContent y x = true := by
          intro y hy hyx
          rcases hx with ⟨z, hz, hzx, hxz⟩ | ⟨_, hxn⟩
          · have hyz := ih hwf hy hz (hyx.trans hxz)
            rw [sameContent_iff] at hyz hzx ⊢
            exact ⟨fun f => (hyz.1 f).trans (hzx.1 f), hyz.2.trans hzx.2⟩
          · have := le_docCount hy; omega
        simp only [List.mem_append, List.mem_singleton] at hv hu
        rcases hv with hv | rfl <;> rcases hu with hu | rfl
        · exact ih hwf hv hu heq
        · exact key v hv heq
        · have := key u hu heq.symm
          rw [sameContent_iff] at this ⊢
          exact ⟨fun f => (this.1 f).symm, this.2.symm⟩
        · exact sameContent_self _

The converse holds too. Two versions with the same content hold the same
number: a new number is given only to content not deposited before, and
earlier content takes the number it already had. So within one history,
numbers and contents correspond one to one.

    theorem sameContent_symm {v u : Version D} (h : sameContent v u = true) :
        sameContent u v = true := by
      rw [sameContent_iff] at *
      exact ⟨fun f => (h.1 f).symm, h.2.symm⟩

    theorem sameContent_trans {v u t : Version D} (h1 : sameContent v u = true)
        (h2 : sameContent u t = true) : sameContent v t = true := by
      rw [sameContent_iff] at *
      exact ⟨fun f => (h1.1 f).trans (h2.1 f), h1.2.trans h2.2⟩

    /-- **One content, one document version.** -/
    theorem one_content_one_number {l : List (Version D)} (h : WellFormed l)
        {v u : Version D} (hv : v ∈ l) (hu : u ∈ l) (heq : sameContent v u = true) :
        v.documentVersion = u.documentVersion := by
      induction l using snoc_induction generalizing v u with
      | nil => cases hv
      | snoc l x ih =>
        obtain ⟨hwf, hx⟩ := h.init
        have key : ∀ y ∈ l, sameContent y x = true → y.documentVersion = x.documentVersion := by
          intro y hy hyx
          rcases hx with ⟨z, hz, hzx, hxz⟩ | ⟨hnew, _⟩
          · exact (ih hwf hy hz (sameContent_trans hyx (sameContent_symm hzx))).trans hxz.symm
          · rw [hnew y hy] at hyx; cases hyx
        simp only [List.mem_append, List.mem_singleton] at hv hu
        rcases hv with hv | rfl <;> rcases hu with hu | rfl
        · exact ih hwf hv hu heq
        · exact key v hv heq
        · exact (key u hu (sameContent_symm heq)).symm
        · rfl

No gaps: every number from 1 to the highest is held by some version, and
none is below 1.

    /-- **Document versions have no gaps.** -/
    theorem no_gaps {l : List (Version D)} (h : WellFormed l) {k : Nat} (hk1 : 1 ≤ k)
        (hk : k ≤ docCount l) : ∃ v ∈ l, v.documentVersion = k := by
      induction l using snoc_induction generalizing k with
      | nil => simp [docCount] at hk; omega
      | snoc l x ih =>
        obtain ⟨hwf, hx⟩ := h.init
        rw [docCount_append] at hk
        by_cases hkl : k ≤ docCount l
        · obtain ⟨v, hv, hvk⟩ := ih hwf hk1 hkl
          exact ⟨v, by simp [hv], hvk⟩
        · rcases hx with ⟨z, hz, _, hxz⟩ | ⟨_, hxn⟩
          · have := le_docCount hz; omega
          · exact ⟨x, by simp, by omega⟩

    /-- Document versions are numbered from 1. -/
    theorem doc_pos {l : List (Version D)} (h : WellFormed l) {v : Version D} (hv : v ∈ l) :
        1 ≤ v.documentVersion := by
      induction l using snoc_induction generalizing v with
      | nil => cases hv
      | snoc l x ih =>
        obtain ⟨hwf, hx⟩ := h.init
        simp only [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · exact ih hwf hv
        · rcases hx with ⟨z, hz, _, hxz⟩ | ⟨_, hxn⟩
          · rw [hxz]; exact ih hwf hz
          · omega

## Pins cannot form cycles

A version is named by a **site**: an archive, an object, and an object
version number. A site *pins* another when the version there holds a pin
that resolves, and names the other.

    /-- Version `n` of object `oid` of archive `a`. -/
    abbrev Site := ArchiveId × ObjectId × Nat

    /-- A version exists at the site. -/
    def Live (w : World D) (s : Site) : Prop :=
      ∃ o v, lookup w s.1 s.2.1 = some (.live o) ∧ o.versionAt s.2.2 = some v

    /-- The version at `s` holds a pin that resolves, to the version at `t`. -/
    def PinsTo (w : World D) (s t : Site) : Prop :=
      ∃ o v p, lookup w s.1 s.2.1 = some (.live o) ∧ o.versionAt s.2.2 = some v ∧
        p ∈ v.pins ∧ (∃ u, resolve hash w p = .ok u) ∧ t = (p.archive, p.object, p.version)

    /-- A chain of one or more steps of a relation. -/
    inductive Chain {α : Type} (r : α → α → Prop) : α → α → Prop
      | single {a b : α} : r a b → Chain r a b
      | cons {a b c : α} : r a b → Chain r b c → Chain r a c

A pin that resolves names a site where a version exists.

    theorem live_of_resolve {w : World D} {p : Pin D} {u : Version D}
        (h : resolve hash w p = .ok u) : Live w (p.archive, p.object, p.version) := by
      unfold resolve at h
      obtain ⟨c, hc⟩ := resolveEntry_ok_live hash h
      rw [hc] at h
      exact ⟨c, u, hc, (resolveEntry_live_ok hash h).1⟩

The idea of the proof: number the versions in the order in which they were
made. Every valid step pins only versions that exist before it, so a pin
always goes from a later version to an earlier one, and a chain of pins
cannot come back to where it started. `Ranked` says that such a numbering
exists: every existing version has a rank below `N`, and pins go down.

    /-- A numbering of the versions in which pins go down. -/
    def Ranked (w : World D) : Prop :=
      ∃ (rank : Site → Nat) (N : Nat), (∀ s, Live w s → rank s < N) ∧
        ∀ s t, PinsTo hash w s t → rank t < rank s

In a ranked world there is no cycle: along a chain of pins the rank goes
down, so it cannot come back.

    theorem Ranked.chain_lt {w : World D} {rank : Site → Nat}
        (hr : ∀ s t, PinsTo hash w s t → rank t < rank s) {s t : Site}
        (h : Chain (PinsTo hash w) s t) : rank t < rank s := by
      induction h with
      | single h => exact hr _ _ h
      | cons h _ ih => exact Nat.lt_trans ih (hr _ _ h)

    theorem Ranked.no_cycle {w : World D} (hr : Ranked hash w) (s : Site) :
        ¬ Chain (PinsTo hash w) s s := by
      obtain ⟨rank, _, _, hdown⟩ := hr
      intro h
      exact Nat.lt_irrefl _ (Ranked.chain_lt hash hdown h)

In a sound world ([chapter 5](45-worlds.md)), a version that exists holds
only pins that resolve or report `removed`; `removed` stays `removed`
through a step. So a pin that resolves after a step, held by a version that
existed before it, already resolved before it.

    theorem pinsTo_old {w w' : World D} (hw : SoundWorld hash w) (hstep : Step w w')
        {s t : Site} {o : Obj D} {v : Version D} {p : Pin D}
        (hl : lookup w s.1 s.2.1 = some (.live o)) (hv : o.versionAt s.2.2 = some v)
        (hp : p ∈ v.pins) (ht : t = (p.archive, p.object, p.version)) {u : Version D}
        (hu : resolve hash w' p = .ok u) : PinsTo hash w s t := by
      rcases hw.2 _ _ _ hl v (versionAt_mem hv) p hp with ⟨u', hu'⟩ | hr
      · exact ⟨o, v, p, hl, hv, hp, ⟨u', hu'⟩, ht⟩
      · rw [Step.resolve_removed hash hstep hr] at hu; cases hu

A version that did not exist before a valid step was made by it, so its
pins were checked by the step: they resolved before it, or reported
`removed`. This is the only place where the proof looks at the kind of
step.

    /-- After a valid step, a version is one the world had, at the same number,
    or its pins were checked by the step. -/
    theorem ValidStep.old_or_checked {w w' : World D} (hs : ValidStep hash w w')
        {b : ArchiveId} {x : ObjectId} {n : Nat} {o' : Obj D} {v : Version D}
        (hl' : lookup w' b x = some (.live o')) (hv : o'.versionAt n = some v) :
        (∃ o, lookup w b x = some (.live o) ∧ o.versionAt n = some v) ∨
          ∀ p ∈ v.pins, Held hash w p := by
      cases hs with
      | newArchive a ar ha hempty =>
        rw [lookup_newArchive ha hempty] at hl'
        exact Or.inl ⟨o', hl', hv⟩
      | create a ar oid o ha ho _ hpins _ =>
        rw [lookup_setEntry ha] at hl'
        split at hl'
        · cases hl'; exact Or.inr fun p hp => (hpins v (versionAt_mem hv) p hp).held
        · exact Or.inl ⟨o', hl', hv⟩
      | append a ar oid o y ha ho _ _ _ _ hpins _ =>
        rw [lookup_setEntry ha] at hl'
        split at hl'
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases hl'
          rcases versionAt_append hv with hv | ⟨_, rfl⟩
          · exact Or.inl ⟨o, by simp [lookup, ha, ho], hv⟩
          · exact Or.inr fun p hp => (hpins p hp).held
        · exact Or.inl ⟨o', hl', hv⟩

    theorem ValidStep.new_pins {w w' : World D} (hs : ValidStep hash w w') {b : ArchiveId}
        {x : ObjectId} {n : Nat} {o' : Obj D} {v : Version D}
        (hl' : lookup w' b x = some (.live o')) (hv : o'.versionAt n = some v)
        (hnew : ¬ Live w (b, x, n)) {p : Pin D} (hp : p ∈ v.pins) :
        Held hash w p := by
      rcases hs.old_or_checked hash hl' hv with ⟨o, ho, hvo⟩ | h
      · exact absurd ⟨o, v, ho, hvo⟩ hnew
      · exact h p hp

The main lemma: a valid step keeps a numbering in which pins go down. The
versions that existed before the step keep their numbers, and the new ones
get the number `N`, above all the others. A pin held by a new version that
resolves after the step resolved before it (if it reported `removed`, it
still does), so it names a version that existed, numbered below `N`. An old version is unchanged by the step (objects only grow), and
its pins that resolve after the step already resolved before it
(`pinsTo_old`), so the old numbering already sent them down.

    theorem ValidStep.ranked {w w' : World D} (hs : ValidStep hash w w') (hw : SoundWorld hash w)
        (hr : Ranked hash w) : Ranked hash w' := by
      classical
      obtain ⟨rank, N, hlive, hdown⟩ := hr
      have hstep := hs.toStep hash
      refine ⟨fun s => if Live w s then rank s else N, N + 1, fun s _ => ?_, ?_⟩
      · dsimp only; split
        · exact Nat.lt_succ_of_lt (hlive s ‹_›)
        · exact Nat.lt_succ_self N
      · rintro ⟨b, x, n⟩ t ⟨o', v, p, hl', hv, hp, ⟨u, hu⟩, ht⟩
        dsimp only
        by_cases hold : Live w (b, x, n)
        · obtain ⟨o, v0, hl, hv0⟩ := hold
          obtain ⟨o2, h2, _, _, _, t2, ht2⟩ := hstep.live_grows hl
          rw [hl'] at h2; cases h2
          have := versionAt_prefix (t := []) (by simp) ht2 (Obj.versionAt_bounds hv0).2 hv0
          rw [hv] at this; cases this
          have hpt := pinsTo_old hash hw hstep hl hv0 hp ht hu
          have htl : Live w t := by
            obtain ⟨_, _, q, _, _, _, ⟨u', hu'⟩, hq⟩ := hpt
            rw [hq]; exact live_of_resolve hash hu'
          rw [if_yes htl, if_yes (show Live w (b, x, n) from ⟨o, v, hl, hv0⟩)]
          exact hdown _ _ hpt
        · rcases hs.new_pins hash hl' hv hold hp with ⟨u0, hu0⟩ | hr0
          · have htl : Live w t := ht ▸ live_of_resolve hash hu0
            rw [if_yes htl, if_no hold]
            exact hlive t htl
          · rw [Step.resolve_removed hash hstep hr0] at hu; cases hu

A takedown keeps the numbering: it removes versions, and the pins that still
resolve after it resolved before it, to the same versions.

    theorem takedown_ranked {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl : lookup w a oid = some (.live o)) (hr : Ranked hash w) :
        Ranked hash (takedown hash w a oid o) := by
      obtain ⟨rank, N, hlive, hdown⟩ := hr
      refine ⟨rank, N, fun s ⟨o', v, h, hv⟩ =>
        hlive s ⟨o', v, (lookup_takedown hash hl h).2, hv⟩, ?_⟩
      rintro s t ⟨o', v, p, h, hv, hp, ⟨u, hu⟩, ht⟩
      have hpa : ¬ (p.archive = a ∧ p.object = oid) := by
        intro hpa; rw [takedown_removed hash hl hpa] at hu; cases hu
      rw [takedown_other hash hl hpa] at hu
      exact hdown s t ⟨o', v, p, (lookup_takedown hash hl h).2, hv, hp, ⟨u, hu⟩, ht⟩

The empty world is ranked, trivially, and so, by induction, is every world
built from it by events: valid steps and takedowns.

    theorem Events.ranked {w : World D}
        (hs : Events hash (fun _ => (none : Option (Archive D))) w) :
        SoundWorld hash w ∧ Ranked hash w := by
      refine hs.invariant (fun w => SoundWorld hash w ∧ Ranked hash w) ?_
        ⟨SoundWorld.empty hash, fun _ => 0, 0, ?_, ?_⟩
      · intro _ _ he ih
        cases he with
        | step hs => exact ⟨hs.sound hash ih.1, hs.ranked hash ih.1 ih.2⟩
        | takedown a oid o hl => exact ⟨takedown_sound hash hl ih.1, takedown_ranked hash hl ih.2⟩
      · rintro s ⟨o, v, hl, _⟩; simp [lookup] at hl
      · rintro s t ⟨o, v, p, hl, _⟩; simp [lookup] at hl

    /-- **Pins cannot form cycles** (section 10.2), in any world built by events
    (valid steps and takedowns), whatever the digest function. -/
    theorem no_cycles_events {w : World D}
        (hs : Events hash (fun _ => (none : Option (Archive D))) w) (s : Site) :
        ¬ Chain (PinsTo hash w) s s :=
      (hs.ranked hash).2.no_cycle hash s

Valid steps are events, so the same holds of worlds built by valid steps
alone.

    theorem ValidSteps.toEvents {w w' : World D} (hs : ValidSteps hash w w') :
        Events hash w w' :=
      hs.mono .step

    /-- **Pins cannot form cycles**, in any world built by valid steps. -/
    theorem no_cycles {w : World D}
        (hs : ValidSteps hash (fun _ => (none : Option (Archive D))) w) (s : Site) :
        ¬ Chain (PinsTo hash w) s s :=
      no_cycles_events hash hs.toEvents s

In particular a version cannot pin itself, and two collections cannot pin
each other: both would be cycles. Section 10.2 attributes this to the
hashes ("collections are hash trees"); the reason, in the model's reading,
is that a pin names a digest, which cannot be known before the version
exists. The model shows that the protocol is enough: a valid step pins
only what already exists. The hashes make it hold also for copies that come
from outside the protocol.

## A withdrawal cannot be undone

Section 11.1 makes the status a property of the object, and issue #25 asks
whether a withdrawal can be undone. The model's choice
([chapter 2](20-object.md)) is that it cannot, and valid steps enforce it:
once the head of an object is withdrawn, it stays withdrawn.

    /-- The head of a live object is withdrawn. -/
    def HeadWithdrawn (w : World D) (a : ArchiveId) (oid : ObjectId) : Prop :=
      ∃ o, lookup w a oid = some (.live o) ∧ headStatus o.versions = .withdrawn

    /-- **A withdrawal cannot be undone** by valid steps. -/
    theorem ValidStep.withdrawn_stays {w w' : World D} (hs : ValidStep hash w w')
        {a : ArchiveId} {oid : ObjectId} (h : HeadWithdrawn w a oid) : HeadWithdrawn w' a oid := by
      obtain ⟨o, hl, hst⟩ := h
      cases hs with
      | newArchive b ar hb hempty =>
        exact ⟨o, by rw [lookup_newArchive hb hempty]; exact hl, hst⟩
      | create b ar c o' hb hc _ _ =>
        refine ⟨o, ?_, hst⟩
        rw [lookup_setEntry hb]
        split
        · rename_i hbc
          obtain ⟨rfl, rfl⟩ := hbc
          simp [lookup, hb, hc] at hl
        · exact hl
      | append b ar c o' y hb hc _ hst' _ _ =>
        by_cases hbc : a = b ∧ oid = c
        · obtain ⟨rfl, rfl⟩ := hbc
          have hoo : some (Entry.live o') = some (Entry.live o) := by
            rw [← hl]; simp [lookup, hb, hc]
          have := Entry.live.inj (Option.some.inj hoo)
          subst this
          refine ⟨o'.append y, by rw [lookup_setEntry hb]; simp, ?_⟩
          simp [headStatus, Obj.append, hst' hst]
        · exact ⟨o, by rw [lookup_setEntry hb, if_no hbc]; exact hl, hst⟩

    theorem ValidSteps.withdrawn_stays {w w' : World D} (hs : ValidSteps hash w w')
        {a : ArchiveId} {oid : ObjectId} (h : HeadWithdrawn w a oid) : HeadWithdrawn w' a oid :=
      hs.invariant _ (·.withdrawn_stays hash) h

    end OpenSheaf
