-- Generated from literate-sheaf/71-below.md by opensheaf-literate: edit the document, not this file.
import Sheaf.Eternal

namespace OpenSheaf.Sheaf

variable {D : Type} [DecidableEq D] (E : Env D)

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

/-- **Nothing lost.** -/
theorem below_fixed {w w' : World D}
    (hs0 : ValidSteps E (fun _ => (none : Option (Archive D))) w) (hs : ValidSteps E w w')
    {H : Histories D} (hh : Honest E H w') {x y : Name} (hx : HeldIn w x) :
    (byPins E w').le y x ↔ (byPins E w).le y x :=
  ⟨below_back E hs0 hs hh hx, Steps.le E (ValidSteps.toSteps E hs)⟩

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
