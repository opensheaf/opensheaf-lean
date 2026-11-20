# Names are eternal

A named document version carries no digest: "version 2 of this line" says
which version is meant, not what it holds. The earlier chapters prove that
in one world all copies agree on what it holds, when owners are honest.
This chapter proves that they agree across worlds too:

- **names are eternal**: a named document version held in a world, and in
  any other world, has the same content in both, whatever happened between
  them, and even when neither world follows from the other
  (`names_eternal`);
- in terms of sections, the glued sections of any two worlds agree wherever
  both are defined (`glue_eternal`).

So a citation by name alone, `sheaf:<name>:<owner>/v<n>` (section 12.1),
means the same thing for all time and in every place, or stops meaning
anything where nothing holds it; it never comes to mean something else.

In version 0.1 of this program the proof followed the events from one world
to a later one, and relied on the fact that an object lived in one home
archive, which a takedown closed for ever. Version 0.2 needs neither. The
head of every copy of a line, in every world built by events, is signed by
the line's owner (`Events.headsSigned`, in the model), and what a signature
says does not depend on the world: an owner that signs one history has
signed one version at each number, for all worlds at once. The argument is
therefore shorter, and its conclusion stronger: it compares any two worlds,
not only a world and a later one.

What version 0.1 also proved, that a name held nowhere is never held again
(**no resurrection**), is false in version 0.2, and the chapter drops it:
a line taken down everywhere may come back, "from a copy holding the
version its tombstone pins" (section 13.2), or deposited again by its owner
in an archive that hosts it (section 6.5). What remains true is what
matters to a reader: when it comes back, it holds the same content
(`names_eternal`).

    -- in Sheaf/Eternal.lean:
    import Sheaf.Acyclic

    namespace OpenSheaf.Sheaf

    variable {D : Type} [DecidableEq D] (E : Env D)

## Two worlds

A copy holding a named document version is a copy of the line it names, and
its head is signed by the owner, with the whole copy as its inventory. Two
copies in two worlds are thus two histories the owner signed, which are
prefixes of one another, when the owner signs one history; and in the
longer one, which is well formed, a number has one content.

    theorem holds_line {w : World D} (hw : SoundWorld E w) {x : Name} {v : Version D}
        (h : Holds w x v) : ∃ b l c, lookup w b (.line l) = some (.live c) ∧ c.kind ≠ .owner ∧
          v ∈ c.versions ∧ x = ⟨.line l, v.documentVersion⟩ := by
      obtain ⟨b, l, c, hl, hk, hv, rfl⟩ := h
      exact ⟨b, l, c, hl, hk, hv, by simp only [Obj.name, (hw.1 _ _ _ hl).id]⟩

    /-- **Names are eternal.** A named document version held in two worlds built by
    events has the same content in both, when owners are honest. -/
    theorem names_eternal {w w' : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w)
        (hs' : Events E (fun _ => (none : Option (Archive D))) w') {H : Histories D}
        (hh : Honest E H w) (hh' : Honest E H w')
        {x : Name} {v v' : Version D} (h : Holds w x v) (h' : Holds w' x v') :
        v.content = v'.content := by
      obtain ⟨b, l, c, hl, hk, hv, rfl⟩ := holds_line E (Events.sound E hs) h
      obtain ⟨b', l', c', hl', hk', hv', hx⟩ := holds_line E (Events.sound E hs') h'
      simp only [Name.mk.injEq, ObjectId.line.injEq] at hx
      obtain ⟨rfl, hd⟩ := hx
      have hc := honest_comparable E hs hs' hh hh' hl hl' hk hk'
      apply content_eq_iff.mpr
      rcases hc with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact one_number_one_content (((Events.sound E hs').1 _ _ _ hl').history hk')
          (by rw [ht]; exact List.mem_append_left _ hv) hv' hd
      · exact one_number_one_content (((Events.sound E hs).1 _ _ _ hl).history hk)
          hv (by rw [ht]; exact List.mem_append_left _ hv') hd

In terms of sections: the value of a glued section at a point is the
content of any version holding it (`glue_value`), so the glued sections of
two worlds agree wherever both are defined.

    /-- **Gluing across worlds.** The glued sections of two worlds built by events
    agree wherever both are defined, when owners are honest. -/
    theorem glue_eternal {w w' : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w)
        (hs' : Events E (fun _ => (none : Option (Archive D))) w') {H : Histories D}
        (hh : Honest E H w) (hh' : Honest E H w')
        {g : Sec (HeldIn w) (Content D)} (hg : Glues (sections w) g)
        {g' : Sec (HeldIn w') (Content D)} (hg' : Glues (sections w') g')
        {x : Name} (hx : HeldIn w x) (hx' : HeldIn w' x) : g x hx = g' x hx' := by
      have hk := Events.sound E hs
      have hk' := Events.sound E hs'
      obtain ⟨v, hv⟩ := (heldIn_iff E hk x).mp hx
      obtain ⟨v', hv'⟩ := (heldIn_iff E hk' x).mp hx'
      rw [glue_value E hk hg hv hx, glue_value E hk' hg' hv' hx']
      exact names_eternal E hs hs' hh hh' hv hv'

## Holding through steps

What follows by steps keeps every holding, since copies only grow; a
takedown holds nothing new. The chapters after this one use both.

    omit [DecidableEq D] in
    theorem Step.holds {w w' : World D} (hs : Step w w') {x : Name} {v : Version D}
        (h : Holds w x v) : Holds w' x v := by
      obtain ⟨b, l, c, hl, hk, hv, rfl⟩ := h
      obtain ⟨c', hl', hg⟩ := hs.live_grows hl
      obtain ⟨t, ht⟩ := hg.versions
      exact ⟨b, l, c', hl', by rw [hg.kind]; exact hk, by rw [ht]; exact List.mem_append_left _ hv,
        by simp only [Obj.name, hg.id]⟩

    omit [DecidableEq D] in
    theorem Steps.holds {w w' : World D} (hs : Steps w w') {x : Name} {v : Version D}
        (h : Holds w x v) : Holds w' x v :=
      hs.invariant (fun w => Holds w x v) (fun h1 h2 => Step.holds h1 h2) h

    omit [DecidableEq D] in
    theorem takedown_holds {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl0 : lookup w a oid = some (.live o)) {x : Name} {v : Version D}
        (h : Holds (takedown E.hash w a oid o) x v) : Holds w x v := by
      obtain ⟨b, l, c, hl, hk, hv, hx⟩ := h
      exact ⟨b, l, c, (lookup_takedown E.hash hl0 hl).2, hk, hv, hx⟩

    end OpenSheaf.Sheaf
