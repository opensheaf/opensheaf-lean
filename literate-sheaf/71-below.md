# What lies below is fixed

Citing a selection version by its pin is meant to fix what the selection
vetted: the revisions it pins, what they pin in turn, and so on. In the
order with pins (chapter [Collections and what they pin](55-collections.md))
that is everything below the selection version. This chapter proves that
later events cannot change it, except by taking things down:

- **nothing new below**: once a named document version is held, no later
  event adds anything below it; whatever lies below it in a later world,
  where it is still held, lay below it already (`below_back`);
- **nothing lost without takedowns**: after valid steps alone, what lies
  below it is exactly what lay below it (`below_fixed`);
- **the same values**: below it, the glued sections of the two worlds agree
  (`below_values`).

This is the property a Merkle structure has, proved here across time within
one world, from the protocol, with no hypothesis on the digest function:
the members of a version are fixed by its content, which never changes, and
their pins resolve, when they resolve, to the versions they resolved to
when they were written. Across worlds built independently, the same
property would rest on the digests instead; the model has no step relation
across worlds (see the introduction).

    -- in Sheaf/Below.lean:
    import Sheaf.Eternal

    namespace OpenSheaf.Sheaf

    variable {D : Type} [DecidableEq D] (hash : Hash D)

## One event

Through one event, a chain down to a point held before the event was a
chain before it: each of its edges ends at a point held before the event,
and an edge into such a point was an edge before (`Step.pinStep_back`,
chapter [The order with pins](57-acyclic.md)); a takedown adds no edge.

    theorem Event.below_back {w w' : World D} (he : Event hash w w') (hk : Kept hash w)
        (hk' : Kept hash w') {x y : Name} (h : (byPins hash w').le y x) (hx : HeldIn w x) :
        (byPins hash w).le y x := by
      revert hx
      induction h with
      | refl => intro _; exact Star.refl _
      | @tail m x' _ hb ih =>
        intro hx
        have hedge : Before hash w m x' := by
          rcases hb with hd | hp
          · exact Or.inl hd
          · right
            cases he with
            | step hs => exact Step.pinStep_back hash (hs.toStep hash) hk.1 hk'.1 hk'.2.2 hx hp
            | takedown a oid o hl => exact takedown_pinStep hash hl hp
        have hm := heldIn_open_byPins hash hk.1 (Star.tail (Star.refl _) hedge) hx
        exact Star.tail (ih hm) hedge

## Any number of events

A point held in a world and in a later one was held in every world between
them (no resurrection, chapter [Names are eternal](70-eternal.md)), so the
one-event lemma applies at every event.

    theorem heldIn_between {w w1 w2 : World D}
        (hs0 : Events hash (fun _ => (none : Option (Archive D))) w) (hs1 : Events hash w w1)
        (he : Event hash w1 w2) {x : Name} (hx : HeldIn w x) (hx2 : HeldIn w2 x) :
        HeldIn w1 x := by
      apply Classical.byContradiction
      intro hx1
      have hk := Events.kept hash hs0
      obtain ⟨v, hv⟩ := (heldIn_iff hash hk.1 x).mp hx
      have hgone : ∀ v', ¬ Holds w1 x v' := fun v' hv' =>
        hx1 ((heldIn_iff hash (Events.kept hash (hs0.trans hs1)).1 x).mpr ⟨v', hv'⟩)
      obtain ⟨v2, hv2⟩ :=
        (heldIn_iff hash (Events.kept hash ((hs0.trans hs1).tail he)).1 x).mp hx2
      exact no_resurrection hash hs0 hs1 (.tail (.refl _) he) hv hgone v2 hv2

    /-- **Nothing new below.** What lies below a named document version in a
    later world where it is still held lay below it already. -/
    theorem below_back {w w' : World D}
        (hs0 : Events hash (fun _ => (none : Option (Archive D))) w) (hs : Events hash w w')
        {x y : Name} (hx : HeldIn w x) (hx' : HeldIn w' x) (h : (byPins hash w').le y x) :
        (byPins hash w).le y x := by
      revert y
      induction hs with
      | refl => exact fun h => h
      | tail hs1 he ih =>
        intro y h
        have hx1 := heldIn_between hash hs0 hs1 he hx hx'
        have hk1 := Events.kept hash (hs0.trans hs1)
        have hk2 := Events.kept hash ((hs0.trans hs1).tail he)
        exact ih hx1 (Event.below_back hash he hk1 hk2 h hx1)

Valid steps keep every edge (`Steps.le`) and every holding, so without
takedowns what lies below a point is exactly what lay below it.

    /-- **Nothing lost without takedowns.** -/
    theorem below_fixed {w w' : World D}
        (hs0 : Events hash (fun _ => (none : Option (Archive D))) w)
        (hs : ValidSteps hash w w') {x y : Name} (hx : HeldIn w x) :
        (byPins hash w').le y x ↔ (byPins hash w).le y x := by
      have hk := Events.kept hash hs0
      have hx' : HeldIn w' x := by
        obtain ⟨v, hv⟩ := (heldIn_iff hash hk.1 x).mp hx
        have hev := ValidSteps.toEvents hash hs
        have hk' := Events.kept hash (hs0.trans hev)
        refine (heldIn_iff hash hk'.1 x).mpr ⟨v, ?_⟩
        exact hs.invariant (fun w2 => Holds w2 x v) (fun h1 h2 => Step.holds (h1.toStep hash) h2) hv
      exact ⟨below_back hash hs0 (ValidSteps.toEvents hash hs) hx hx',
        Steps.le hash (ValidSteps.toSteps hash hs)⟩

## The same values

Below a point held in both worlds, every point is held in both, and the
glued sections agree there, since names are eternal.

    /-- **The same values below.** -/
    theorem below_values {w w' : World D}
        (hs0 : Events hash (fun _ => (none : Option (Archive D))) w) (hs : Events hash w w')
        {g : Sec (HeldIn w) (Content D)} (hg : Glues (sections w) g)
        {g' : Sec (HeldIn w') (Content D)} (hg' : Glues (sections w') g')
        {x y : Name} (hx : HeldIn w x) (hx' : HeldIn w' x) (h : (byPins hash w').le y x) :
        ∃ (hy : HeldIn w y) (hy' : HeldIn w' y), g y hy = g' y hy' := by
      have hk := Events.kept hash hs0
      have hk' := Events.kept hash (hs0.trans hs)
      have hy := heldIn_open_byPins hash hk.1 (below_back hash hs0 hs hx hx' h) hx
      have hy' := heldIn_open_byPins hash hk'.1 h hx'
      exact ⟨hy, hy', glue_eternal hash hs0 hs hg hg' hy hy'⟩

    end OpenSheaf.Sheaf
