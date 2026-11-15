-- Generated from literate-sheaf/55-collections.md by opensheaf-literate: edit the document, not this file.
import Sheaf.Pins

namespace OpenSheaf.Sheaf

variable {D : Type} [DecidableEq D] (hash : Hash D)

omit [DecidableEq D] in
/-- The pins of the member list of an object version. -/
def _root_.OpenSheaf.Version.memberPins (v : Version D) : List (Pin D) :=
  match v.members with
  | none => []
  | some ms => ms.pins

omit [DecidableEq D] in
theorem memberPins_sub {v : Version D} {p : Pin D} (h : p ∈ v.memberPins) : p ∈ v.pins := by
  unfold Version.memberPins at h
  unfold Version.pins
  cases hm : v.members with
  | none => simp [hm] at h
  | some ms => simp only [hm] at h ⊢; exact List.mem_append_left _ h

/-- `y` comes before `x` by a pin: a version holding `x`, kept anywhere,
pins in its member list an object version that resolves, and that holds
`y`. -/
def PinStep (w : World D) (y x : Name) : Prop :=
  ∃ (b : ArchiveId) (i : ObjectId) (c : Obj D) (v : Version D) (p : Pin D) (o : Obj D)
    (u : Version D),
    lookup w b i = some (.live c) ∧ v ∈ c.versions ∧ x = c.name v ∧ p ∈ v.memberPins ∧
      lookup w p.archive p.object = some (.live o) ∧ resolve hash w p = .ok u ∧
      y = o.name u

/-- One step down: an earlier version of the same object, or a pinned member. -/
def Before (w : World D) (y x : Name) : Prop := deposit.le y x ∨ PinStep hash w y x

/-- The order of deposit and pins: any number of steps down. -/
def byPins (w : World D) : Order Name where
  le := Star (Before hash w)
  refl x := Star.refl x
  trans h1 h2 := h1.trans h2

theorem open_of_before {w : World D} {U : Name → Prop}
    (h : ∀ {y x}, Before hash w y x → U x → U y) : (byPins hash w).IsOpen U := by
  intro x y hle
  induction hle with
  | refl => exact id
  | tail _ hr ih => exact fun hx => ih (h hr hx)

/-- **What a world holds is open in the order with pins.** -/
theorem heldIn_open_byPins {w : World D} (hw : SoundWorld hash w) :
    (byPins hash w).IsOpen (HeldIn w) := by
  apply open_of_before
  intro y x hb hx
  rcases hb with hh | ⟨b, i, c, v, p, o, u, hl, hv, rfl, hp, ho, hr, rfl⟩
  · exact heldIn_open w hh hx
  · have hre : resolveEntry hash (some (.live o)) p = .ok u :=
      (resolve_live hash ho).symm.trans hr
    have hu := (resolveEntry_live_ok hash hre).1
    have hwf := (hw.1 _ _ _ ho).history
    exact ⟨⟨p.archive, p.object, o, ho, p.version⟩,
      (covers_iff hwf p.version _).mpr ⟨u, versionAt_mem_take hu, rfl⟩⟩

theorem below_of_ok {w : World D} {b : ArchiveId} {i : ObjectId} {c : Obj D}
    {v : Version D} {p : Pin D} {u : Version D} (hl : lookup w b i = some (.live c))
    (hv : v ∈ c.versions) (hp : p ∈ v.memberPins) (hu : resolve hash w p = .ok u) :
    ∃ o, lookup w p.archive p.object = some (.live o) ∧
      (byPins hash w).le (o.name u) (c.name v) := by
  have hu' := hu
  unfold resolve at hu'
  obtain ⟨o, ho⟩ := resolveEntry_ok_live hash hu'
  exact ⟨o, ho, Star.tail (Star.refl _)
    (Or.inr ⟨b, i, c, v, p, o, u, hl, hv, rfl, hp, ho, hu, rfl⟩)⟩

/-- **Every member lies below its collection**, or was taken down. -/
theorem members_below {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) {b : ArchiveId}
    {i : ObjectId} {c : Obj D} {v : Version D} {p : Pin D}
    (hl : lookup w b i = some (.live c)) (hv : v ∈ c.versions) (hp : p ∈ v.memberPins) :
    (∃ o u, lookup w p.archive p.object = some (.live o) ∧ resolve hash w p = .ok u ∧
      (byPins hash w).le (o.name u) (c.name v)) ∨ resolve hash w p = .removed := by
  rcases (Events.sound hash hs).2 _ _ _ hl v hv p (memberPins_sub hp) with ⟨u, hu⟩ | hr
  · obtain ⟨o, ho, hle⟩ := below_of_ok hash hl hv hp hu
    exact Or.inl ⟨o, u, ho, hu, hle⟩
  · exact Or.inr hr

/-- Without takedowns, every member lies below its collection. -/
theorem members_below_valid {w : World D}
    (hs : ValidSteps hash (fun _ => (none : Option (Archive D))) w) {b : ArchiveId}
    {i : ObjectId} {c : Obj D} {v : Version D} {p : Pin D}
    (hl : lookup w b i = some (.live c)) (hv : v ∈ c.versions) (hp : p ∈ v.memberPins) :
    ∃ o u, lookup w p.archive p.object = some (.live o) ∧ resolve hash w p = .ok u ∧
      (byPins hash w).le (o.name u) (c.name v) := by
  obtain ⟨u, hu⟩ := ValidSteps.pins_ok hash hs _ _ _ hl v hv p (memberPins_sub hp)
  obtain ⟨o, ho, hle⟩ := below_of_ok hash hl hv hp hu
  exact ⟨o, u, ho, hu, hle⟩

/-- **The value at a member is what its pin fixes.** -/
theorem glue_at_member {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w)
    {g : Sec (HeldIn w) (Content D)} (hg : Glues (sections w) g) {p : Pin D} {o : Obj D}
    {u : Version D} (ho : lookup w p.archive p.object = some (.live o))
    (hr : resolve hash w p = .ok u) (hy : HeldIn w (o.name u)) :
    g (o.name u) hy = u.content := by
  have hre : resolveEntry hash (some (.live o)) p = .ok u :=
    (resolve_live hash ho).symm.trans hr
  exact glue_value hash (Events.sound hash hs) hg
    ⟨_, _, o, ho, versionAt_mem (resolveEntry_live_ok hash hre).1, rfl⟩ hy

/-- **The stalk of a collection version**: each member it pins, with the
content its pin fixes, or a takedown reported. -/
theorem collection_members {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w)
    {g : Sec (HeldIn w) (Content D)} (hg : Glues (sections w) g) {b : ArchiveId}
    {i : ObjectId} {c : Obj D} {v : Version D} {p : Pin D}
    (hl : lookup w b i = some (.live c)) (hv : v ∈ c.versions) (hp : p ∈ v.memberPins) :
    (∃ (o : Obj D) (u : Version D), lookup w p.archive p.object = some (.live o) ∧
      resolve hash w p = .ok u ∧ (byPins hash w).le (o.name u) (c.name v) ∧
      ∃ hy : HeldIn w (o.name u), g (o.name u) hy = u.content) ∨
      resolve hash w p = .removed := by
  rcases members_below hash hs hl hv hp with ⟨o, u, ho, hr, hle⟩ | hr
  · left
    have hx : HeldIn w (c.name v) := by
      have hwf := ((Events.sound hash hs).1 _ _ _ hl).history
      exact ⟨⟨b, i, c, hl, c.versions.length⟩, (covers_iff hwf _ _).mpr
        ⟨v, by rw [List.take_length]; exact hv, rfl⟩⟩
    have hy := heldIn_open_byPins hash (Events.sound hash hs) hle hx
    exact ⟨o, u, ho, hr, hle, hy, glue_at_member hash hs hg ho hr hy⟩
  · exact Or.inr hr

end OpenSheaf.Sheaf
