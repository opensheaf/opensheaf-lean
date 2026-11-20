# What lies below is fixed

Citing a selection version by its pin is meant to fix what the selection
vetted: the revisions it pins and, for those that are collections, what
their member lists pin, and so on. The references of documents are not in
the order (see the introduction). In the order with pins (chapter
[Collections and what they pin](55-collections.md)) these lie below the
selection version, together with more that the selection version did not
vet but its pin fixes all the same: the earlier versions of each revision
(section 8.4), and the selection's own earlier versions with what they
pinned, including revisions the curator has since removed. This chapter
proves that later valid steps cannot change any of it, when owners are
honest:

- **nothing new below**: once a named document version is held, no later
  valid step adds anything below it; whatever lies below it in a later
  world lay below it already (`below_back`);
- **nothing lost**: after valid steps, what lies below it is exactly what
  lay below it (`below_fixed`);
- **the same values**: below it, the glued sections of the two worlds agree
  (`below_values`).

This is the property a Merkle structure is meant to give, proved here
across time within one world, from the protocol and the owners' keys,
with no use of the digest function beyond what honest owners assume
(`OneHistory`, in the model):
the members of a version are fixed by its content, which never changes, and
their pins resolve, when they resolve, to the versions they resolved to
when they were written. Across worlds built independently, the same
property would rest on the digests instead; the model has no step relation
across worlds (see the introduction).

Version 0.1 of this program proved the first property through takedowns
too. It rested on the fact that a name held nowhere is never held again,
which version 0.2 gives up (chapter [Names are eternal](70-eternal.md)),
and on the rank of the previous chapters, which is proved for valid steps
only (chapter [The order with pins](57-acyclic.md)). Through takedowns, an
edge into a point may also come and go with the copies that hold what it
pins. The chapter therefore states the three properties for worlds built
by valid steps, and leaves takedowns out.

    -- in Sheaf/Below.lean:
    import Sheaf.Eternal

    namespace OpenSheaf.Sheaf

    variable {D : Type} [DecidableEq D] (E : Env D)

## One step

Through one valid step, a chain down to a point held before the step was a
chain before it: each of its edges ends at a point held before the step,
and an edge into such a point was an edge before (`Step.pinStep_back`,
chapter [The order with pins](57-acyclic.md)).

    theorem ValidStep.below_back {w w' : World D} (hs : ValidStep E w w')
        (hw0 : ValidSteps E (fun _ => (none : Option (Archive D))) w) {H : Histories D}
        (hh : Honest E H w') {x y : Name} (h : (byPins E w').le y x) (hx : HeldIn w x) :
        (byPins E w).le y x := by
      have hev : Events E (fun _ => (none : Option (Archive D))) w := hw0.mono .step
      have hev' : Events E (fun _ => (none : Option (Archive D))) w' := (hw0.tail hs).mono .step
      obtain ⟨hwf, hnk, _⟩ := ValidSteps.nameRanked E hw0 (hh.back E (.tail (.refl _) (hs.toStep E)))
      have hsw := Events.sound E hev
      revert hx
      induction h with
      | refl => intro _; exact Star.refl _
      | @tail m x' _ hb ih =>
        intro hx
        have hedge : Before E w m x' := by
          rcases hb with hd | hp
          · exact Or.inl hd
          · exact Or.inr (Step.pinStep_back E (hs.toStep E) hev hwf hnk (Events.sound E hev')
              (fun l => Events.copiesAgree E hev' (hh.one E l)) hx hp)
        have hm := heldIn_open_byPins E hsw (Star.tail (Star.refl _) hedge) hx
        exact Star.tail (ih hm) hedge

## Any number of steps

Valid steps keep every holding, so a point held in a world is held in
every world that follows, and the one-step lemma applies at every step.

    theorem heldIn_steps {w w' : World D} (hs0 : Events E (fun _ => (none : Option (Archive D))) w)
        (hs : Steps w w') (hs' : Events E (fun _ => (none : Option (Archive D))) w') {x : Name}
        (hx : HeldIn w x) : HeldIn w' x := by
      obtain ⟨v, hv⟩ := (heldIn_iff E (Events.sound E hs0) x).mp hx
      exact (heldIn_iff E (Events.sound E hs') x).mpr ⟨v, Steps.holds hs hv⟩

    /-- **Nothing new below.** What lies below a named document version in a world
    that follows by valid steps lay below it already. -/
    theorem below_back {w w' : World D}
        (hs0 : ValidSteps E (fun _ => (none : Option (Archive D))) w) (hs : ValidSteps E w w')
        {H : Histories D} (hh : Honest E H w') {x y : Name} (hx : HeldIn w x)
        (h : (byPins E w').le y x) :
        (byPins E w).le y x := by
      revert y
      induction hs with
      | refl => exact fun h => h
      | tail hs1 he ih =>
        intro y h
        have h01 := hs0.trans hs1
        have hx1 := heldIn_steps E (hs0.mono .step) (ValidSteps.toSteps E hs1) (h01.mono .step) hx
        exact ih (hh.back E (.tail (.refl _) (he.toStep E))) (ValidStep.below_back E he h01 hh h hx1)

Valid steps keep every edge (`Steps.le`), so what lies below a point is
exactly what lay below it.

    /-- **Nothing lost.** -/
    theorem below_fixed {w w' : World D}
        (hs0 : ValidSteps E (fun _ => (none : Option (Archive D))) w) (hs : ValidSteps E w w')
        {H : Histories D} (hh : Honest E H w') {x y : Name} (hx : HeldIn w x) :
        (byPins E w').le y x ↔ (byPins E w).le y x :=
      ⟨below_back E hs0 hs hh hx, Steps.le E (ValidSteps.toSteps E hs)⟩

## The same values

Below a point held in both worlds, every point is held in both, and the
glued sections agree there, since names are eternal.

    /-- **The same values below.** -/
    theorem below_values {w w' : World D}
        (hs0 : ValidSteps E (fun _ => (none : Option (Archive D))) w) (hs : ValidSteps E w w')
        {H : Histories D} (hh : Honest E H w') {g : Sec (HeldIn w) (Content D)}
        (hg : Glues (sections w) g)
        {g' : Sec (HeldIn w') (Content D)} (hg' : Glues (sections w') g')
        {x y : Name} (hx : HeldIn w x) (h : (byPins E w').le y x) :
        ∃ (hy : HeldIn w y) (hy' : HeldIn w' y), g y hy = g' y hy' := by
      have he0 : Events E (fun _ => (none : Option (Archive D))) w := hs0.mono .step
      have he1 : Events E (fun _ => (none : Option (Archive D))) w' := (hs0.trans hs).mono .step
      have hx' := heldIn_steps E he0 (ValidSteps.toSteps E hs) he1 hx
      have hy := heldIn_open_byPins E (Events.sound E he0) (below_back E hs0 hs hh hx h) hx
      have hy' := heldIn_open_byPins E (Events.sound E he1) h hx'
      exact ⟨hy, hy', glue_eternal E he0 he1 (hh.back E (ValidSteps.toSteps E hs)) hh hg hg' hy hy'⟩

    end OpenSheaf.Sheaf
