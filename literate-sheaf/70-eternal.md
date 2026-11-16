# Names are eternal

A named document version carries no digest: "version 2 of the paper in the
author's archive" says which version is meant, not what it holds. The
earlier chapters prove that in one world all copies agree on what it holds.
This chapter proves that they agree across time too:

- **names are eternal**: a named document version held in a world, and in
  any later world, has the same content in both, whatever happened between
  them: deposits, new mirrors, takedowns (`names_eternal`);
- **no resurrection**: a named document version that was held, and is held
  nowhere any more, is never held again (`no_resurrection`).

So a citation by name alone means the same thing for all time, or stops
meaning anything; it never comes to mean something else. In terms of
sections, the worlds of a sequence of events glue over time as well
as over names: the glued sections of a world and of any later world agree
wherever both are defined (`glue_eternal`).

The proof follows the events from a world `w`. It keeps two facts about
every named document version held in `w`: every later version holding it
has the same content, and it stays held unless its object is taken down in
its own archive. A tombstone then blocks every way of holding it again: a
new object needs an empty entry, a new mirror or a new version of a mirror
needs a live original, and a new version in the object's own archive needs
the object live there.

    -- in Sheaf/Eternal.lean:
    import Sheaf.Acyclic

    namespace OpenSheaf.Sheaf

    variable {D : Type} [DecidableEq D] (hash : Hash D)

The object named by a named document version is *taken down* when its own
archive has a tombstone for it. Holding, `Kept` and the lemmas about them
are in the chapter [The sections of a world glue](40-world.md).

    omit [DecidableEq D] in
    /-- The object named by `x` has been taken down in its own archive. -/
    def Tomb (w : World D) (x : Name) : Prop := ∃ n d, lookup w x.archive x.object = some (.tomb n d)

## One event

A step keeps every holding, since copies only grow; a takedown holds
nothing new.

    omit [DecidableEq D] in
    theorem Step.holds {w w' : World D} (hs : Step w w') {x : Name} {v : Version D}
        (h : Holds w x v) : Holds w' x v := by
      obtain ⟨b, i, c, hl, hv, rfl⟩ := h
      obtain ⟨c', hl', ha, hi, _, t, ht⟩ := hs.live_grows hl
      exact ⟨b, i, c', hl', by rw [ht]; exact List.mem_append_left _ hv,
        by simp only [Obj.name, ha, hi]⟩

    omit [DecidableEq D] in
    theorem takedown_holds {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl0 : lookup w a oid = some (.live o)) {x : Name} {v : Version D}
        (h : Holds (takedown hash w a oid o) x v) : Holds w x v := by
      obtain ⟨b, i, c, hl, hv, hx⟩ := h
      exact ⟨b, i, c, (lookup_takedown hash hl0 hl).2, hv, hx⟩

So through one event, a version before it and a version after it that
hold the same named document version have the same content: compare them
after a step, or before a takedown.

    /-- Through one event, two versions holding the same named document version,
    one before and one after, have the same content. -/
    theorem Event.holds_same {w w' : World D} (he : Event hash w w') (hk : Kept hash w)
        (hk' : Kept hash w') {x : Name} {v v' : Version D} (h : Holds w x v)
        (h' : Holds w' x v') : sameContent v v' = true := by
      cases he with
      | step hs => exact holds_agree hash hk'.1 hk'.2.2 (Step.holds (hs.toStep hash) h) h'
      | takedown a oid o hl => exact holds_agree hash hk.1 hk.2.2 h (takedown_holds hash hl h')

Through one event, a named document version stays held, or its object is
taken down. A step keeps every copy. A takedown removes one copy: if it is
the object in its own archive, the object is taken down; if it is a mirror,
the original is live and holds what the mirror held, or was taken down
already.

    /-- Through one event, a named document version stays held, or its object is
    taken down. -/
    theorem Event.persist {w w' : World D} (he : Event hash w w') (hk : Kept hash w)
        {x : Name} {v : Version D} (h : Holds w x v) :
        (∃ v', Holds w' x v' ∧ sameContent v v' = true) ∨ Tomb w' x := by
      cases he with
      | step hs => exact Or.inl ⟨v, Step.holds (hs.toStep hash) h, sameContent_self _⟩
      | takedown a oid o hl0 =>
        obtain ⟨b, i, c, hl, hv, rfl⟩ := h
        by_cases hc : b = a ∧ i = oid
        · obtain ⟨rfl, rfl⟩ := hc
          rw [hl0] at hl; cases hl
          have hid : o.id = i := (hk.1.1 _ _ _ hl0).id
          by_cases hb : o.archive = b
          · right
            refine ⟨o.versions.length, hash (o.inventory o.versions.length), ?_⟩
            show lookup (takedown hash w b i o) o.archive o.id = _
            rw [lookup_takedown_eq hash hl0, if_yes ⟨hb, hid⟩]; rfl
          · obtain ⟨hne, hpre⟩ := hk.2.1 b i o hl0 hb
            have hother : ¬ (o.archive = b ∧ o.id = i) := fun h => hb h.1
            cases ho2 : lookup w o.archive o.id with
            | none => exact absurd ho2 hne
            | some e =>
              cases e with
              | live o2 =>
                obtain ⟨ha2, t, ht⟩ := hpre o2 ho2
                have hid2 : o2.id = o.id := (hk.1.1 _ _ _ ho2).id
                left
                refine ⟨v, ⟨o.archive, o.id, o2, ?_, by rw [ht]; exact List.mem_append_left _ hv,
                  by simp only [Obj.name, ha2, hid2]⟩, sameContent_self _⟩
                rw [lookup_takedown_eq hash hl0, if_no hother]; exact ho2
              | tomb n d =>
                right
                refine ⟨n, d, ?_⟩
                show lookup (takedown hash w b i o) o.archive o.id = _
                rw [lookup_takedown_eq hash hl0, if_no hother]; exact ho2
        · left
          refine ⟨v, ⟨b, i, c, ?_, hv, rfl⟩, sameContent_self _⟩
          rw [lookup_takedown_eq hash hl0, if_no hc]; exact hl

Nothing is held anew under a tombstone. This is the only place where the
proof looks at the kind of step, and it uses the premise `hhome` of the
model's valid steps: an object is written in its own archive, or as a
mirror of a live original.

    /-- **Nothing new under a tombstone.** No event makes a version of an object
    taken down held anywhere, if it was not held before. -/
    theorem Event.tomb_holds {w w' : World D} (he : Event hash w w') (hk : Kept hash w)
        {x : Name} (ht : Tomb w x) {v : Version D} (h : Holds w' x v) : Holds w x v := by
      obtain ⟨n, d, ht⟩ := ht
      cases he with
      | takedown a oid o hl0 => exact takedown_holds hash hl0 h
      | step hs =>
        obtain ⟨b, i, c, hl, hv, rfl⟩ := h
        cases hs with
        | newArchive a ar ha hempty =>
          rw [lookup_newArchive ha hempty] at hl
          exact ⟨b, i, c, hl, hv, rfl⟩
        | create a ar oid o ha ho hwf _ hhome _ =>
          rw [lookup_setEntry ha] at hl
          split at hl
          · rename_i hc
            obtain ⟨rfl, rfl⟩ := hc
            cases hl
            exfalso
            rcases hhome with hh | ⟨orig, hlo, _⟩
            · have : lookup w b i = none := by simp [lookup, ha, ho]
              simp only [Obj.name, hh, hwf.id] at ht
              rw [this] at ht; cases ht
            · simp only [Obj.name] at ht
              rw [hlo] at ht; cases ht
          · exact ⟨b, i, c, hl, hv, rfl⟩
        | append a ar oid o y ha ho _ _ _ _ _ hhome _ =>
          have hlo : lookup w a oid = some (.live o) := by simp [lookup, ha, ho]
          rw [lookup_setEntry ha] at hl
          split at hl
          · rename_i hc
            obtain ⟨rfl, rfl⟩ := hc
            cases hl
            simp only [Obj.append, List.mem_append, List.mem_singleton] at hv
            rcases hv with hv | rfl
            · exact ⟨b, i, o, hlo, hv, rfl⟩
            · exfalso
              rcases hhome with hh | ⟨orig, hlo', _⟩
              · have hid : o.id = i := (hk.1.1 _ _ _ hlo).id
                simp only [Obj.name, Obj.append, hh, hid] at ht
                rw [hlo] at ht; cases ht
              · simp only [Obj.name, Obj.append] at ht hlo'
                rw [hlo'] at ht; cases ht
          · exact ⟨b, i, c, hl, hv, rfl⟩

## Every later world

The two facts, together with the invariants of the model, are kept by every
event, so they hold of every world that follows `w`.

    /-- What holds from `w` on: names keep their content, and stay held unless
    their object is taken down. -/
    def Eternal (w w' : World D) : Prop :=
      Kept hash w' ∧ ∀ x v, Holds w x v →
        (∀ v', Holds w' x v' → sameContent v v' = true) ∧ ((∃ v', Holds w' x v') ∨ Tomb w' x)

    theorem Event.eternal {w w1 w2 : World D} (he : Event hash w1 w2) (h : Eternal hash w w1) :
        Eternal hash w w2 := by
      obtain ⟨hk1, hall⟩ := h
      have hk2 : Kept hash w2 := Event.copiesAgree hash he hk1
      refine ⟨hk2, fun x v hv => ⟨fun v2 hv2 => ?_, ?_⟩⟩
      · rcases (hall x v hv).2 with ⟨v1, hv1⟩ | ht
        · exact sameContent_trans ((hall x v hv).1 v1 hv1)
            (Event.holds_same hash he hk1 hk2 hv1 hv2)
        · exact (hall x v hv).1 v2 (Event.tomb_holds hash he hk1 ht hv2)
      · rcases (hall x v hv).2 with ⟨v1, hv1⟩ | ⟨n, d, ht⟩
        · rcases Event.persist hash he hk1 hv1 with ⟨v2, hv2, _⟩ | ht
          · exact Or.inl ⟨v2, hv2⟩
          · exact Or.inr ht
        · exact Or.inr ⟨n, d, Event.tomb_stays hash he ht⟩

    theorem Events.eternal {w w' : World D}
        (hs0 : Events hash (fun _ => (none : Option (Archive D))) w) (hs : Events hash w w') :
        Eternal hash w w' :=
      hs.invariant _ (fun he h => Event.eternal hash he h)
        ⟨Events.kept hash hs0, fun _ v hv =>
          ⟨fun _ hv' => holds_agree hash (Events.kept hash hs0).1 (Events.kept hash hs0).2.2 hv hv', Or.inl ⟨v, hv⟩⟩⟩

## The theorems

    /-- **Names are eternal.** A named document version held in a world, and in
    any world that follows by events, has the same content in both. -/
    theorem names_eternal {w w' : World D}
        (hs0 : Events hash (fun _ => (none : Option (Archive D))) w) (hs : Events hash w w')
        {x : Name} {v v' : Version D} (h : Holds w x v) (h' : Holds w' x v') :
        v.content = v'.content :=
      content_eq_iff.mpr ((Events.eternal hash hs0 hs).2 x v h |>.1 v' h')

Once a name is held nowhere, its object is taken down, and nothing is held
anew under a tombstone, so it stays held nowhere.

    /-- **No resurrection.** A named document version that was held, and is held
    nowhere any more, is never held again. -/
    theorem no_resurrection {w w' w'' : World D}
        (hs0 : Events hash (fun _ => (none : Option (Archive D))) w) (hs : Events hash w w')
        (hs' : Events hash w' w'') {x : Name} {v : Version D} (h : Holds w x v)
        (hgone : ∀ v', ¬ Holds w' x v') : ∀ v'', ¬ Holds w'' x v'' := by
      have ht : Tomb w' x := by
        rcases ((Events.eternal hash hs0 hs).2 x v h).2 with ⟨v', hv'⟩ | ht
        · exact absurd hv' (hgone v')
        · exact ht
      have hk' : Kept hash w' := (Events.eternal hash hs0 hs).1
      have := hs'.invariant (fun w2 => Kept hash w2 ∧ Tomb w2 x ∧ ∀ v', ¬ Holds w2 x v')
        (fun he ⟨hk, ⟨n, d, ht⟩, hno⟩ =>
          ⟨Event.copiesAgree hash he hk, ⟨n, d, Event.tomb_stays hash he ht⟩,
            fun v' hv' => hno v' (Event.tomb_holds hash he hk ⟨n, d, ht⟩ hv')⟩)
        ⟨hk', ht, hgone⟩
      exact this.2.2

In terms of sections: the value of a glued section at a point is the
content of any version holding it (`glue_value`), so the glued sections of
two worlds, one following the other, agree wherever both are defined.

    /-- **Gluing over time.** The glued sections of a world and of any later
    world agree wherever both are defined. -/
    theorem glue_eternal {w w' : World D}
        (hs0 : Events hash (fun _ => (none : Option (Archive D))) w) (hs : Events hash w w')
        {g : Sec (HeldIn w) (Content D)} (hg : Glues (sections w) g)
        {g' : Sec (HeldIn w') (Content D)} (hg' : Glues (sections w') g')
        {x : Name} (hx : HeldIn w x) (hx' : HeldIn w' x) : g x hx = g' x hx' := by
      have hk := Events.kept hash hs0
      have hk' := (Events.eternal hash hs0 hs).1
      obtain ⟨v, hv⟩ := (heldIn_iff hash hk.1 x).mp hx
      obtain ⟨v', hv'⟩ := (heldIn_iff hash hk'.1 x).mp hx'
      rw [glue_value hash hk.1 hg hv hx, glue_value hash hk'.1 hg' hv' hx']
      exact names_eternal hash hs0 hs hv hv'

    end OpenSheaf.Sheaf
