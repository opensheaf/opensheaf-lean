# What cannot happen

The previous chapters prove what the protocol does. This one proves what it
prevents: for each way of breaking it, an attempt is modelled and shown to
be impossible, or, where it can be made outside the protocol, to be
detected. These are the negative tests of the model; the chapters on key
logs and on owners ([chapters 4](35-owners.md) and [8](47-acts.md)) have
those about keys.

| The break | Why it cannot happen |
|---|---|
| A pin changes its meaning | immutability: once a pin resolves to a version at an archive, no step changes that version; and through its hints, as long as the owner signs one history |
| An archive rewrites the history of a copy | no sequence of steps can; outside the protocol, every pin of a rewritten version stops resolving there (unless the inventories collide) |
| An identifier taken down names another object | tombstones stay |
| One document version number for two contents, a new number for the content of the version before it, or a gap in the numbering | the counting rule of section 4.2 (a revert to an earlier content is a new number, and allowed) |
| Pins form a cycle (a version pins itself, or two collections pin each other) | valid steps pin only versions that exist already, and copies of a line agree |
| A pin names a key log | valid steps check it, and it stays so |
| A withdrawn line becomes active again | valid steps forbid it (the model's choice on issue #25) |

The fifth is stated in section 8.5 ("collections are hash trees, and pins
cannot form cycles"), where it is justified by the hashes. The model proves
it from the protocol, with one hypothesis: that each owner signs one
history, which no copy the world holds collides with (`OneHistory`). It
assumes nothing of the digest beyond those pairs of inventories.

    -- in OpenSheaf/Impossible.lean:
    import OpenSheaf.Patterns

    namespace OpenSheaf

    variable {D : Type} [DecidableEq D] (E : Env D)

## A pin cannot change its meaning

Immutability, stated as an impossibility: once a pin resolves to a version
at an archive, no sequence of steps makes it resolve there to another; and
through its hints, the same holds when the owner signs one history.

    /-- **A pin cannot change its meaning** at an archive. -/
    theorem pin_meaning_fixed {w w' : World D} (hs : Steps w w') {b : ArchiveId} {p : Pin D}
        {v u : Version D} (hp : resolveAt E.hash w b p = .ok v) (hne : u ≠ v) :
        resolveAt E.hash w' b p ≠ .ok u := by
      rw [Steps.resolveAt_ok E.hash hs hp]
      intro h
      cases h
      exact hne rfl

    /-- **A pin cannot change its meaning** through its hints, when its owner signs
    one history. -/
    theorem pin_meaning_fixed_hints {w w' : World D}
        (hw' : Events E (fun _ => (none : Option (Archive D))) w') (hs : Steps w w') {p : Pin D}
        (h1 : OneHistory E w' p.line) (hnk : p.line ≠ keyLogLine p.line.owner) {v u : Version D}
        (hp : resolve E.hash w p = .ok v) (hne : u ≠ v) : resolve E.hash w' p ≠ .ok u := by
      rw [Steps.resolve_ok E hw' hs h1 hnk hp]
      intro h
      cases h
      exact hne rfl

## History cannot be rewritten

Within the protocol, an object only grows ([chapter 7](45-worlds.md)): its
history in a later world extends its history in an earlier one. A world in
which an archive has replaced, removed or reordered versions of an object
is therefore not reachable by any sequence of steps.

    omit [DecidableEq D] in
    /-- **History cannot be rewritten by any steps.** -/
    theorem history_not_rewritten {w w' : World D} (hs : Steps w w') {a : ArchiveId}
        {oid : ObjectId} {o o' : Obj D} (hl : lookup w a oid = some (.live o))
        (hl' : lookup w' a oid = some (.live o'))
        (hrew : o'.versions.take o.versions.length ≠ o.versions) : False := by
      obtain ⟨o2, h2, hg⟩ := Steps.live_grows hs hl
      obtain ⟨t, ht⟩ := hg.versions
      rw [hl'] at h2
      cases h2
      apply hrew
      rw [ht, List.take_append_of_le_length (Nat.le_refl _), List.take_length]

An archive can still rewrite its files outside the protocol: nothing stops
the owner of a disk. Then every pin of a rewritten version, made before,
stops resolving there: the digest in the pin is that of the original
inventory, and the rewritten inventory has another, unless the two collide
([chapter 9](48-copies.md)). Tampering is not prevented, it is detected, by
anyone holding a pin; and the rewritten version is signed by nobody, so
section 7.3 would report it as not a version.

    /-- **Tampering is detected.** If an archive replaces a copy by one whose
    history differs up to version `p.version`, a pin of that version made before
    resolves there to no version at all. -/
    theorem tamper_detected {w : World D}
        {a : ArchiveId} {o o' : Obj D} {p : Pin D} (hl : lookup w a (.line p.line) = some (.live o))
        {v : Version D} (hp : resolveAt E.hash w a p = .ok v)
        (hdiff : o'.inventory p.version ≠ o.inventory p.version)
        (hcol : NoCollision E (o'.inventory p.version) (o.inventory p.version))
        (u : Version D) : resolveAt E.hash (setEntry w a (.line p.line) (.live o')) a p ≠ .ok u := by
      obtain ⟨ar, ha⟩ := lookup_some_archive hl
      intro h
      unfold resolveAt at h hp
      rw [lookup_setEntry ha] at h
      simp only [and_self, ite_true] at h
      rw [hl] at hp
      obtain ⟨_, hd⟩ := resolveEntry_live_ok E.hash hp
      obtain ⟨_, hd'⟩ := resolveEntry_live_ok E.hash h
      exact hdiff (hcol (hd'.trans hd.symm))

## A tombstoned identifier cannot be reused

Section 4: the identifier "of a sealed object MUST NOT be reused there,
also after a takedown". In the model it is not a rule that archives must
remember: no step can do it. (A line taken down may return, as the same
line, from a copy holding the version its tombstone pins, section 13.2,
which the model leaves out.)

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
section 4.2 asks for numbers "from 1, without gaps". The counting rule of
[chapter 2](20-object.md) guarantees both. The proofs go along the history
from the end, with `snoc_induction` and `WellFormed.init` of chapter 2.

One number, one content: two versions of a well-formed history with the
same document version have the same content. The last version either holds
earlier content, and takes its number, or a number above all the others.

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

The converse does not hold: a revert (section 4.2) gives the content of an
earlier version a new number, so a content may have several numbers. What
holds is that a new number is new content as against the version before it:
two document versions with consecutive numbers have different content. The
version holding the higher number was, when it was made, either a new
document version, whose content differs from that of the current version,
which held the number below; or it holds the content of an earlier version
with that number, and the induction applies to that one.

    theorem sameContent_symm {v u : Version D} (h : sameContent v u = true) :
        sameContent u v = true := by
      rw [sameContent_iff] at *
      exact ⟨fun f => (h.1 f).symm, h.2.symm⟩

    theorem sameContent_trans {v u t : Version D} (h1 : sameContent v u = true)
        (h2 : sameContent u t = true) : sameContent v t = true := by
      rw [sameContent_iff] at *
      exact ⟨fun f => (h1.1 f).trans (h2.1 f), h1.2.trans h2.2⟩

    /-- **Consecutive document versions differ.** -/
    theorem next_number_new_content {l : List (Version D)} (h : WellFormed l)
        {v u : Version D} (hv : v ∈ l) (hu : u ∈ l)
        (hn : u.documentVersion = v.documentVersion + 1) : sameContent v u = false := by
      induction l using snoc_induction generalizing v u with
      | nil => cases hv
      | snoc l x ih =>
        obtain ⟨hwf, hx⟩ := h.init
        simp only [List.mem_append, List.mem_singleton] at hv hu
        rcases hv with hv | hv <;> rcases hu with hu | hu
        · exact ih hwf hv hu hn
        · rw [hu] at hn ⊢
          rcases hx with ⟨z, hz, hzx, hxz⟩ | ⟨hnew, hxn⟩
          · cases hc : sameContent v x
            · rfl
            · have h1 := ih hwf hv hz (by omega)
              rw [sameContent_trans hc (sameContent_symm hzx)] at h1
              cases h1
          · exact hnew v hv (by omega)
        · rw [hv] at hn ⊢
          rcases hx with ⟨z, hz, hzx, hxz⟩ | ⟨_, hxn⟩
          · cases hc : sameContent x u
            · rfl
            · have h1 := ih hwf hz hu (by omega)
              rw [sameContent_trans hzx hc] at h1
              cases h1
          · have := le_docCount hu; omega
        · rw [hv, hu] at hn; omega

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

In version 0.1 of the specification a pin named an archive, and a version
was a place: the model numbered the versions of each archive in the order
in which they were made, and a pin, which named a version that existed
already, always went down. Version 0.2 pins lines, not places, and a line
may be copied anywhere, so the version a pin names may also be found in a
copy made after the pin. The model therefore names a version by its
**site**, a line and a version number, wherever it is kept, and the
argument becomes: a valid step pins only sites that exist already, and a
site, once it exists, holds the same version in every copy, as long as
the owner signs one history (`Events.copiesAgree`, [chapter
9](48-copies.md)). Drafts never lie on a cycle, since nothing pins them,
nor key logs, since no pin names them ([chapter 7](45-worlds.md)).

    /-- A version of the line `l` at number `n` exists, in some archive. -/
    def Live (w : World D) (s : LineId × Nat) : Prop :=
      ∃ b o v, lookup w b (.line s.1) = some (.live o) ∧ o.versionAt s.2 = some v

    /-- A version at the site `s`, kept somewhere, holds a pin of the site `t`; the
    line of `s` is not a key log. -/
    def PinsTo (w : World D) (s t : LineId × Nat) : Prop :=
      s.1 ≠ keyLogLine s.1.owner ∧ ∃ b o v p, lookup w b (.line s.1) = some (.live o) ∧
        o.versionAt s.2 = some v ∧ p ∈ v.pins ∧ t = (p.line, p.version)

    /-- A chain of one or more steps of a relation. -/
    inductive Chain {α : Type} (r : α → α → Prop) : α → α → Prop
      | single {a b : α} : r a b → Chain r a b
      | cons {a b c : α} : r a b → Chain r b c → Chain r a c

A pin found names a site where a version exists.

    theorem live_of_found {w : World D} {p : Pin D} (h : Found E.hash w p) :
        Live w (p.line, p.version) := by
      obtain ⟨b, _, u, hu⟩ := h
      unfold resolveAt at hu
      obtain ⟨c, hc⟩ := resolveEntry_ok_live E.hash hu
      rw [hc] at hu
      exact ⟨b, c, u, hc, (resolveEntry_live_ok E.hash hu).1⟩

`Ranked` says that the sites can be numbered so that every existing site
has a number below `N`, and pins go down.

    /-- A numbering of the sites in which pins go down. -/
    def Ranked (w : World D) : Prop :=
      ∃ (rank : LineId × Nat → Nat) (N : Nat), (∀ s, Live w s → rank s < N) ∧
        ∀ s t, PinsTo w s t → rank t < rank s

In a ranked world there is no cycle: along a chain of pins the rank goes
down, so it cannot come back.

    omit [DecidableEq D] in
    theorem Ranked.chain_lt {w : World D} {rank : LineId × Nat → Nat}
        (hr : ∀ s t, PinsTo w s t → rank t < rank s) {s t : LineId × Nat}
        (h : Chain (PinsTo w) s t) : rank t < rank s := by
      induction h with
      | single h => exact hr _ _ h
      | cons h _ ih => exact Nat.lt_trans ih (hr _ _ h)

    omit [DecidableEq D] in
    theorem Ranked.no_cycle {w : World D} (hr : Ranked w) (s : LineId × Nat) :
        ¬ Chain (PinsTo w) s s := by
      obtain ⟨rank, _, _, hdown⟩ := hr
      intro h
      exact Nat.lt_irrefl _ (Ranked.chain_lt hdown h)

After a valid step, a version is one the world had, in the same copy at the
same number, or one the step made, whose pins it checked. This is the only
place where the proof looks at the kind of step.

    /-- After a valid step, a version is one the copy had, at the same number, or
    its pins were checked by the step. -/
    theorem ValidStep.old_or_checked {w w' : World D} (hs : ValidStep E w w')
        {b : ArchiveId} {x : ObjectId} {n : Nat} {o' : Obj D} {v : Version D}
        (hl' : lookup w' b x = some (.live o')) (hv : o'.versionAt n = some v) :
        (∃ o, lookup w b x = some (.live o) ∧ o.versionAt n = some v) ∨
          ∀ p ∈ v.pins, PinOk E w p := by
      rcases hs.live_cases E hl' with hl0 | ⟨_, _, _, ⟨_, hpins⟩ | ⟨o, y, ss, hlo, rfl, hpins⟩⟩ |
          ⟨o, ss, hlo, rfl, _⟩
      · exact Or.inl ⟨o', hl0, hv⟩
      · exact Or.inr fun p hp => hpins v (versionAt_mem hv) p hp
      · rcases versionAt_append hv with hv | ⟨_, rfl⟩
        · exact Or.inl ⟨o, hlo, hv⟩
        · exact Or.inr hpins
      · exact Or.inl ⟨o, hlo, hv⟩

In a world built by valid steps alone there is no tombstone, so every pin
held is found, and names a site that exists.

    theorem WFWorld.pinOk_found {w : World D} (hw : WFWorld E w) {p : Pin D}
        (h : PinOk E w p) : Found E.hash w p := by
      rcases h.2 with hf | ⟨⟨b, _, hr⟩, _⟩
      · exact hf
      · obtain ⟨n, d, hl⟩ := (resolveAt_removed_iff E.hash).mp hr
        exact absurd hl (hw.2.2 _ _ _ _)

The main lemma: a valid step keeps a numbering in which pins go down. Sites
that existed before the step keep their numbers, and new sites get the
number `N`, above all the others. A version at a new site was made by the
step, so its pins are found before it, at sites that existed. A version at
an old site is either old, in its copy, and its pins went down already; or
new in its copy, and then, the copies of its line agreeing, it is the
version that the site already held elsewhere, with the same pins.

    theorem ValidStep.ranked {w w' : World D} (hs : ValidStep E w w') (hw : WFWorld E w)
        (hw' : Events E (fun _ => (none : Option (Archive D))) w')
        (hh : ∀ l, l ≠ keyLogLine l.owner → OneHistory E w' l) (hr : Ranked w) : Ranked w' := by
      classical
      obtain ⟨rank, N, hlive, hdown⟩ := hr
      have hstep := hs.toStep E
      refine ⟨fun s => if Live w s then rank s else N, N + 1, fun s _ => ?_, ?_⟩
      · dsimp only; split
        · exact Nat.lt_succ_of_lt (hlive s ‹_›)
        · exact Nat.lt_succ_self N
      · rintro ⟨l, n⟩ t ⟨hnk, b, o', v, p, hl', hv, hp, ht⟩
        dsimp only
        have htl : ∀ q ∈ v.pins, PinOk E w q → Live w (q.line, q.version) :=
          fun q _ hq => live_of_found E (hw.pinOk_found E hq)
        rcases hs.old_or_checked E hl' hv with ⟨o, hl, hvo⟩ | hchk
        · -- an old version, in its copy: its pin went down already
          have hpt : PinsTo w (l, n) t := ⟨hnk, b, o, v, p, hl, hvo, hp, ht⟩
          have hold : Live w (l, n) := ⟨b, o, v, hl, hvo⟩
          have htl' : Live w t := by
            rw [ht]
            exact live_of_found E (hw.2.1 _ _ _ hl v (versionAt_mem hvo) p hp)
          rw [if_yes htl', if_yes hold]
          exact hdown _ _ hpt
        · have htl' : Live w t := by rw [ht]; exact htl p hp (hchk p hp)
          by_cases hold : Live w (l, n)
          · -- a new version at an old site: the site's version elsewhere
            obtain ⟨b0, o0, v0, hl0, hv0⟩ := hold
            obtain ⟨o0', hl0', hg0⟩ := hstep.live_grows hl0
            obtain ⟨t0, ht0⟩ := hg0.versions
            have hv0' : o0'.versionAt n = some v0 :=
              versionAt_prefix (t := []) (by simp) ht0 (Obj.versionAt_bounds hv0).2 hv0
            have hk1 : o'.kind ≠ .owner := fun hk => hnk (Events.keyLog_line E hw' hl' hk)
            have hk0 : o0'.kind ≠ .owner := fun hk => hnk (Events.keyLog_line E hw' hl0' hk)
            have heq : v0 = v := (Events.copiesAgree E hw' (hh l hnk) b0 b o0' o' hl0' hl' hk0 hk1).versionAt
              hv0' hv
            subst heq
            have hpt : PinsTo w (l, n) t := ⟨hnk, b0, o0, v0, p, hl0, hv0, hp, ht⟩
            rw [if_yes htl', if_yes ⟨b0, o0, v0, hl0, hv0⟩]
            exact hdown _ _ hpt
          · rw [if_yes htl', if_no hold]
            exact hlive t htl'

The empty world is ranked, trivially, and so, by induction, is every world
built from it by valid steps, when every owner signs one history. Only the
lines that pins can name matter: the hypothesis is asked of every line that
is not a key log, since a key log is never pinned.

    theorem ValidSteps.ranked {w : World D}
        (hs : ValidSteps E (fun _ => (none : Option (Archive D))) w)
        (hh : ∀ l, l ≠ keyLogLine l.owner → OneHistory E w l) :
        WFWorld E w ∧ Ranked w := by
      induction hs with
      | refl => exact ⟨WFWorld.empty E, fun _ => 0, 0, by
          rintro s ⟨b, o, v, hl, _⟩; simp [lookup] at hl, by
          rintro s t ⟨_, b, o, v, p, hl, _⟩; simp [lookup] at hl⟩
      | tail hprev hstep ih =>
        have ih' := ih fun l hl => (hh l hl).back E (.tail (.refl _) (hstep.toStep E))
        exact ⟨hstep.wf E ih'.1, hstep.ranked E ih'.1
          ((Star.tail hprev hstep).mono .step) hh ih'.2⟩

    /-- **Pins cannot form cycles** (section 8.5), in any world built by valid steps
    in which every owner signs one history of each line that is not a key log,
    which no copy held collides with. -/
    theorem no_cycles {w : World D}
        (hs : ValidSteps E (fun _ => (none : Option (Archive D))) w)
        (hh : ∀ l, l ≠ keyLogLine l.owner → OneHistory E w l)
        (s : LineId × Nat) : ¬ Chain (PinsTo w) s s :=
      (hs.ranked E hh).2.no_cycle s

In particular a version cannot pin itself, and two collections cannot pin
each other: both would be cycles. Section 8.5 attributes this to the
hashes ("collections are hash trees"); the reason, in the model's reading,
is that a pin names a digest, which cannot be known before the version
exists. The model shows that the protocol is enough: a valid step pins only
what already exists, and honest owners keep one version at each site.

Two cases are left out. An owner whose keys sign two histories of a line
could, in principle, deposit at a site that exists elsewhere a version with
other pins; the cycle would then be made with its keys, and attributable to
it (`Events.fork_signed`). And with takedowns among the events, a line
whose every copy was taken down may come back, from a copy elsewhere or
deposited again by its owner, and the numbering above, which forgets the
sites that no longer exist, does not cover it: the proof would need the
history of the world, not only its state. Version 0.1 of the model, where
a pin named a place that never came back, proved the case with takedowns;
for version 0.2 it is an open point of the model.

## No pin names a key log

Valid steps check of every pin they write that it names no key log
(`PinOk`, [chapter 7](45-worlds.md)). With `ValidStep.old_or_checked`, the check holds
of every pin held, in every world built by events: a version is one its
copy had, or one whose pins the step checked; and a takedown only removes.

    /-- No pin held by a version of a live object names a key log. -/
    def PinsNoKeyLog (w : World D) : Prop :=
      ∀ b i c, lookup w b i = some (.live c) → ∀ v ∈ c.versions, ∀ p ∈ v.pins,
        p.line ≠ keyLogLine p.line.owner

    theorem ValidStep.pinsNoKeyLog {w w' : World D} (hs : ValidStep E w w')
        (hw : PinsNoKeyLog w) : PinsNoKeyLog w' := by
      intro b i c hl v hv p hp
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
      have hva : c.versionAt (k + 1) = some c.versions[k] := by
        rw [Obj.versionAt_succ, List.getElem?_eq_getElem hk]
      rcases hs.old_or_checked E hl hva with ⟨o, ho, hvo⟩ | h
      · exact hw _ _ _ ho _ (versionAt_mem hvo) p hp
      · exact (h p hp).1

    /-- **No pin names a key log**, in every world built by events. -/
    theorem Events.pinsNoKeyLog {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) : PinsNoKeyLog w :=
      hs.invariant _ (fun he hw => by
          cases he with
          | step h => exact h.pinsNoKeyLog E hw
          | takedown a oid o _ hl =>
            exact fun b i c h => hw b i c (lookup_takedown E.hash hl h).2)
        (fun _ _ _ h => by simp [lookup] at h)

So a pin held names a line whose copies are documents or collections: the
copies of a key log sit at its line `(X, X)` (`Events.keyLog_line`,
[chapter 9](48-copies.md)), which no pin held names.

    /-- In a world built by events, no copy of the line of a pin held is a key log. -/
    theorem Events.pinned_not_owner {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {b : ArchiveId} {i : ObjectId}
        {c : Obj D} (hl : lookup w b i = some (.live c)) {v : Version D} (hv : v ∈ c.versions)
        {p : Pin D} (hp : p ∈ v.pins) {b' : ArchiveId} {o : Obj D}
        (ho : lookup w b' (.line p.line) = some (.live o)) : o.kind ≠ .owner :=
      fun hk => Events.pinsNoKeyLog E hs b i c hl v hv p hp (Events.keyLog_line E hs ho hk)

## A withdrawal cannot be undone

Section 13.1 makes the status a property of the line, and issue #25 asks
whether a withdrawal can be undone. The model's choice
([chapter 2](20-object.md)) is that it cannot, and valid steps enforce it:
once the head of a copy is withdrawn, it stays withdrawn.

    /-- The head of a live object is withdrawn. -/
    def HeadWithdrawn (w : World D) (a : ArchiveId) (oid : ObjectId) : Prop :=
      ∃ o, lookup w a oid = some (.live o) ∧ headStatus o.versions = .withdrawn

    /-- **A withdrawal cannot be undone** by valid steps. -/
    theorem ValidStep.withdrawn_stays {w w' : World D} (hs : ValidStep E w w')
        {a : ArchiveId} {oid : ObjectId} (h : HeadWithdrawn w a oid) : HeadWithdrawn w' a oid := by
      obtain ⟨o, hl, hst⟩ := h
      cases hs with
      | newArchive b ar hb hempty =>
        exact ⟨o, by rw [lookup_newArchive hb hempty]; exact hl, hst⟩
      | create b ar c o' hb hc =>
        refine ⟨o, ?_, hst⟩
        rw [lookup_setEntry hb]
        split
        · rename_i hbc
          obtain ⟨rfl, rfl⟩ := hbc
          simp [lookup, hb, hc] at hl
        · exact hl
      | append b ar c o' y ss hb hc _ hst' =>
        by_cases hbc : a = b ∧ oid = c
        · obtain ⟨rfl, rfl⟩ := hbc
          have hoo : some (Entry.live o') = some (Entry.live o) := by
            rw [← hl]; simp [lookup, hb, hc]
          have := Entry.live.inj (Option.some.inj hoo)
          subst this
          refine ⟨o'.append y ss, by rw [lookup_setEntry hb]; simp, ?_⟩
          simp [headStatus, Obj.append, hst' hst]
        · exact ⟨o, by rw [lookup_setEntry hb, if_no hbc]; exact hl, hst⟩
      | witness b ar c o' ss hb hc =>
        by_cases hbc : a = b ∧ oid = c
        · obtain ⟨rfl, rfl⟩ := hbc
          have hoo : some (Entry.live o') = some (Entry.live o) := by
            rw [← hl]; simp [lookup, hb, hc]
          have := Entry.live.inj (Option.some.inj hoo)
          subst this
          exact ⟨{ o' with sigs := o'.sigs ++ ss }, by rw [lookup_setEntry hb]; simp, hst⟩
        · exact ⟨o, by rw [lookup_setEntry hb, if_no hbc]; exact hl, hst⟩

    theorem ValidSteps.withdrawn_stays {w w' : World D} (hs : ValidSteps E w w')
        {a : ArchiveId} {oid : ObjectId} (h : HeadWithdrawn w a oid) : HeadWithdrawn w' a oid :=
      hs.invariant _ (·.withdrawn_stays E) h

    end OpenSheaf
