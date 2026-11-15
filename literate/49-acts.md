# Who may act

The previous chapters let anyone make any step. The specification does not:
an archive is "kept by one owner" (section 3); "the owner of the object
decides what its versions are" (section 10.1); a selection "changes only by
an explicit act of its curator, which is a new version of the selection",
recorded "in the inventory (who and when)" (section 10.2); a mirror is
brought up to date "only by copying the new versions of the original"
(section 10.4). Issue #13 names the rule: a **single writer** per object,
which in version 0.1 is the archive that holds it.

This chapter models it. Every change is an **act** of one agent. An agent
may act on an archive only if it is one of its writers
([chapter 3](30-archive.md)), and the versions an archive adds to its own
objects record the agent as their depositor. Copies are the exception that
proves the rule: a custodian's agents act on the custodian's archive, but
the versions of a mirror are the original's, byte for byte, with the
original's depositors.

The chapter proves three things. An agent who is not a writer of an
archive cannot change anything in it. In every world built by acts, every
version of every object, mirrors included, was deposited by a writer of the
object's own archive, so a custodian cannot add versions in an author's
name. And so a selection, kept in its curator's archive, holds only versions
deposited by the curator: the half of section 10.2 that
[chapter 5](45-worlds.md) could not prove.

The model does not say how writers are authorised, nor how a reader checks
it: the specification does not either. PR #30 of the specification proposes
owners named by keys, whose signatures would make the check possible; the
model's writers are the place where that would plug in.

    -- in OpenSheaf/Acts.lean:
    import OpenSheaf.Worlds

    namespace OpenSheaf

    variable {D : Type} [DecidableEq D] (hash : Hash D)

## Writers

The writers of an archive, if it exists. Replacing an entry does not change
them.

    omit [DecidableEq D] in
    /-- The writers of archive `a`. -/
    def writersOf (w : World D) (a : ArchiveId) : Option (List Agent) :=
      (w a).map (·.writers)

    omit [DecidableEq D] in
    theorem writersOf_setEntry (w : World D) (a : ArchiveId) (oid : ObjectId) (e : Entry D)
        (c : ArchiveId) : writersOf (setEntry w a oid e) c = writersOf w c := by
      unfold writersOf setEntry
      by_cases hc : c = a
      · subst hc; cases w c <;> simp
      · simp [hc]

## Acts

An act is a valid step or a takedown ([chapter 5](45-worlds.md)), made by
an agent `u`, with two more checks: `u` is a writer of the archive it
changes; and a version that an archive adds to one of its own objects
records `u` as its depositor. An object created with a history of its own
(imported, for instance) may have several depositors, all writers. A
mirror's versions are exempt: they are copies, whose depositors are the
original's.

Steps and takedowns are kept apart, as in [chapter 5](45-worlds.md): a
`StepBy u` is a valid step made by `u`, and an `Act u` is such a step or a
takedown made by `u`.

    /-- A valid step made by the agent `u`. -/
    inductive StepBy (u : Agent) : World D → World D → Prop
      | newArchive (w : World D) (a : ArchiveId) (ar : Archive D) (h : w a = none)
          (hempty : ∀ x, ar.entries x = none) (hu : u ∈ ar.writers) :
          StepBy u w (fun b => if b = a then some ar else w b)
      | create (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
          (ha : w a = some ar) (ho : ar.entries oid = none) (hwf : o.WF oid)
          (hpins : ∀ v ∈ o.versions, ∀ p ∈ v.pins, Held hash w p)
          (hhome : o.archive = a ∨ MirrorOf w o) (hu : u ∈ ar.writers)
          (hdep : o.archive = a → ∀ v ∈ o.versions, v.depositor ∈ ar.writers)
          (hfollow : o.archive = a → HeadFollows hash w o.versions) :
          StepBy u w (setEntry w a oid (.live o))
      | append (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
          (x : Version D) (ha : w a = some ar) (ho : ar.entries oid = some (.live o))
          (hf : Extends o.versions x) (hst : NoReinstatement o.versions x)
          (hk : x.members.isSome = true ↔ o.kind = .collection) (hm : x.membersOk)
          (hpins : ∀ p ∈ x.pins, Held hash w p)
          (hhome : o.archive = a ∨ MirrorOf w (o.append x)) (hu : u ∈ ar.writers)
          (hdep : o.archive = a → x.depositor = u)
          (hfollow : o.archive = a → x.FollowsHeads hash w) :
          StepBy u w (setEntry w a oid (.live (o.append x)))

    /-- A step or a takedown, made by the agent `u`. -/
    inductive Act (u : Agent) : World D → World D → Prop
      | step {w w' : World D} : StepBy hash u w w' → Act u w w'
      | takedown (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
          (ha : w a = some ar) (hl : lookup w a oid = some (.live o)) (hu : u ∈ ar.writers) :
          Act u w (takedown hash w a oid o)

    /-- An act of some agent. -/
    def AnyAct (w w' : World D) : Prop := ∃ u, Act hash u w w'

    /-- Acts, by any agents. -/
    abbrev Acts : World D → World D → Prop := Star (AnyAct hash)

A step made by an agent is a valid step, and an act is an event, so
everything proved about valid steps and events holds of them.

    theorem StepBy.toValidStep {u : Agent} {w w' : World D} (h : StepBy hash u w w') :
        ValidStep hash w w' := by
      cases h with
      | newArchive a ar h hempty _ => exact .newArchive w a ar h hempty
      | create a ar oid o ha ho hwf hpins hhome _ _ hfo =>
        exact .create w a ar oid o ha ho hwf hpins hhome hfo
      | append a ar oid o x ha ho hf hst hk hm hpins hhome _ _ hfo =>
        exact .append w a ar oid o x ha ho hf hst hk hm hpins hhome hfo

    theorem Act.toEvent {u : Agent} {w w' : World D} (h : Act hash u w w') : Event hash w w' := by
      cases h with
      | step hs => exact .step hs.toValidStep
      | takedown a ar oid o _ hl _ => exact .takedown w a oid o hl

    theorem Acts.toEvents {w w' : World D} (h : Acts hash w w') : Events hash w w' :=
      h.mono fun ⟨_, ha⟩ => ha.toEvent

## Outsiders change nothing

An agent who is not a writer of an archive cannot change any of its
entries: no object created, no version added, nothing taken down. A new
archive is not a change of an existing one; it starts empty.

    /-- **An outsider changes nothing.** -/
    theorem Act.outsider {u : Agent} {w w' : World D} (h : Act hash u w w') {a : ArchiveId}
        (hout : ∀ ar, w a = some ar → u ∉ ar.writers) (x : ObjectId) :
        lookup w' a x = lookup w a x := by
      cases h with
      | step hs =>
        cases hs with
        | newArchive b ar hb hempty _ =>
          rw [lookup_newArchive hb hempty]
        | create b ar oid o hb _ _ _ _ hu _ =>
          rw [lookup_setEntry hb]
          split
          · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; exact absurd hu (hout ar hb)
          · rfl
        | append b ar oid o y hb _ _ _ _ _ _ _ hu _ =>
          rw [lookup_setEntry hb]
          split
          · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; exact absurd hu (hout ar hb)
          · rfl
      | takedown b ar oid o hb hl hu =>
        rw [lookup_takedown_eq hash hl]
        split
        · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; exact absurd hu (hout ar hb)
        · rfl

In particular, the authors of a paper cannot change the journal's selection
of it, nor the journal the authors' paper: each is an outsider to the
other's archive.

## Every version was deposited by its own archive's writers

The invariant: for every live object, kept anywhere, every version was
deposited by a writer of the object's own archive (the one named in its
`object.json`), which exists.

    /-- Every version was deposited by a writer of its object's own archive. -/
    def DepositorsOk (w : World D) : Prop :=
      ∀ b x o, lookup w b x = some (.live o) →
        ∃ ws, writersOf w o.archive = some ws ∧ ∀ v ∈ o.versions, v.depositor ∈ ws

The proof follows the act. A new archive changes no writers of the
archives that exist. A new object of the archive's own was deposited by its
writers (`hdep`). A mirror copies versions of an original, whose depositors
are the original archive's writers. A version appended to an own object
records the acting writer; one appended to a mirror is the original's next
version. A takedown removes an object.

    theorem StepBy.depositors {u : Agent} {w w' : World D} (h : StepBy hash u w w')
        (hw : DepositorsOk w) : DepositorsOk w' := by
      intro b x o' hl
      cases h with
      | newArchive a ar ha hempty _ =>
        rw [lookup_newArchive ha hempty] at hl
        obtain ⟨ws, hws, hdep⟩ := hw b x o' hl
        have hna : o'.archive ≠ a := by
          intro he; rw [he] at hws; simp [writersOf, ha] at hws
        exact ⟨ws, by simpa [writersOf, hna] using hws, hdep⟩
      | create a ar oid o ha ho _ _ hhome _ hdep =>
        rw [writersOf_setEntry]
        rw [lookup_setEntry ha] at hl
        split at hl
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases hl
          rcases hhome with hown | ⟨orig, hlo, harch, t, ht⟩
          · refine ⟨ar.writers, by simp [writersOf, hown, ha], fun v hv => hdep hown v hv⟩
          · obtain ⟨ws, hws, hd⟩ := hw _ _ _ hlo
            rw [harch] at hws
            exact ⟨ws, hws, fun v hv => hd v (by rw [ht]; exact List.mem_append_left _ hv)⟩
        · exact hw _ _ _ hl
      | append a ar oid o y ha ho _ _ _ _ _ hhome hu hdep =>
        rw [writersOf_setEntry]
        rw [lookup_setEntry ha] at hl
        split at hl
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases hl
          have hlo : lookup w b x = some (.live o) := by simp [lookup, ha, ho]
          obtain ⟨ws, hws, hd⟩ := hw _ _ _ hlo
          refine ⟨ws, hws, fun v hv => ?_⟩
          simp only [Obj.append, List.mem_append, List.mem_singleton] at hv
          rcases hv with hv | rfl
          · exact hd v hv
          · rcases hhome with hown | ⟨orig, hlor, harch, t, ht⟩
            · rw [hdep hown]
              have : ws = ar.writers := by
                rw [hown] at hws; simp [writersOf, ha] at hws; exact hws.symm
              rw [this]; exact hu
            · obtain ⟨ws', hws', hd'⟩ := hw _ _ _ hlor
              rw [harch, show (o.append _).archive = o.archive from rfl, hws] at hws'
              cases hws'
              exact hd' _ (by rw [ht]; simp [Obj.append])
        · exact hw _ _ _ hl

    theorem Act.depositors {u : Agent} {w w' : World D} (h : Act hash u w w')
        (hw : DepositorsOk w) : DepositorsOk w' := by
      cases h with
      | step hs => exact hs.depositors hash hw
      | takedown a ar oid o ha hlo _ =>
        intro b x o' hl
        have hl0 := (lookup_takedown hash hlo hl).2
        obtain ⟨ws, hws, hd⟩ := hw _ _ _ hl0
        exact ⟨ws, by unfold OpenSheaf.takedown tombstone; rw [writersOf_setEntry]; exact hws, hd⟩

    theorem Acts.depositors {w : World D}
        (h : Acts hash (fun _ => (none : Option (Archive D))) w) : DepositorsOk w :=
      h.invariant _ (fun ⟨_, ha⟩ => ha.depositors hash) fun b x o hl => by simp [lookup] at hl

## Consequences

**Custodians cannot speak for authors.** `Acts.depositors`, read for
mirrors: a mirror kept by a journal or a library holds only versions
deposited by the writers of the original archive. Whatever the custodian's
agents do, they cannot add a version in the authors' name.

**A selection changes only by its curator.** A selection kept in its own
archive holds only versions deposited by that archive's writers, its
curators: every change of its member list, which is a new version
([chapter 5](45-worlds.md)), was made by one of them. With `Act.outsider`,
nobody else can make one. Here a curator is any writer of the selection's
archive: in an institutional repository whose writers include the authors
who deposit in it, they are the curators of its selections too. A curator
of each selection, distinct from the other writers, needs writers per
object ([model issue 5](https://github.com/opensheaf/opensheaf-lean/issues/5)).

    /-- **A selection changes only by an act of its curator** (section 10.2). -/
    theorem Acts.curated {w : World D}
        (h : Acts hash (fun _ => (none : Option (Archive D))) w) {a : ArchiveId}
        {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
        (hown : o.archive = a) {ar : Archive D} (ha : w a = some ar) :
        ∀ v ∈ o.versions, v.depositor ∈ ar.writers := by
      obtain ⟨ws, hws, hd⟩ := Acts.depositors hash h a oid o hl
      rw [hown] at hws
      simp [writersOf, ha] at hws
      rw [← hws] at hd
      exact hd

The theorem holds of every object kept in its own archive: a paper's
versions were deposited by the writers of the authors' archive, a
catalogue's by those of its archive. For a selection, it is what section
10.2 asks.

    end OpenSheaf
