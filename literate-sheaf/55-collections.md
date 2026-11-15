# Collections and what they pin

So far each object is a separate part of the base: a collection says
nothing, in the order, about its members. But a collection version holds
pins in its member list, and the model counts the member list as part of
the content of the document version (section 7.4). A selection version is
the selection *together with* the revisions it vetted, and a catalogue
version the catalogue together with the versions it pinned.

This chapter adds those pins to the order. A named document version comes
before a collection version whose member list pins it. Below a collection
version there are then the earlier versions of the collection, the
versions it pins, their earlier versions, and so on. The value of the glued
section there is the collection together with everything it pins. The
chapter proves three things:

- the named document versions held in a world stay an open set in the
  larger order: what a held collection pins, when it resolves, is held;
- in every world built by events, every member pinned by a held collection
  version lies below it, unless its object has been taken down, and then
  the pin reports `removed`; without takedowns, every member lies below it;
- the glued section gives each pinned member the content its pin fixes.

## The order with pins

A pin names an object version, not a document version. The edge goes to
the document version that the object version holds, which the world tells:
it is where the pin resolves. So the order depends on the world, and on the
digest function, through resolution. Where a pin resolves is fixed once it
resolves (immutability, in the model), so the edges of a world are kept
by every later step, and a takedown adds none (it may remove some). The
next chapter, [The order with pins](57-acyclic.md), proves both.

The edge goes to the name of the object found, which is the name the
object records. A pin that names a mirror is resolved by the model to the
mirror, which records its original's name (issue #38 of the specification
asks whether such pins should be allowed).

Only the pins of member lists give edges. The references of a document
(issues #21 and #28) are left out: in the model a description-only version
may change them, so they belong to object versions, not to document
versions.

    -- in Sheaf/Collections.lean:
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

A set is open in this order when it is closed under one step down; the
general case follows along the steps.

    theorem open_of_before {w : World D} {U : Name → Prop}
        (h : ∀ {y x}, Before hash w y x → U x → U y) : (byPins hash w).IsOpen U := by
      intro x y hle
      induction hle with
      | refl => exact id
      | tail _ hr ih => exact fun hx => ih (h hr hx)

The sets held by single object versions are open in the order of deposit,
but not in this one: an object version of a collection holds its own
history, not what it pins. Only what a whole world holds is open here
(below), so the theorem that local conditions glue applies to the order of
deposit, not to this one.

The order is a preorder, and nothing in this chapter needs more. In every
world built by events it is also a partial order, which the next chapter,
[The order with pins](57-acyclic.md), proves.

## What a world holds is open

The named document versions held in a world are closed under both kinds of
step. An earlier version of the same object is held by the same source. A
pinned member that resolves is held by its own object, at the object
version pinned: resolution found that object live, and the version in it.

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

## Every member lies below its collection

A pin that resolves gives an edge, from the collection version that holds
it down to the member.

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

In a world built by events, every pin held by a version resolves or reports
`removed` (`Events.sound`, in the model). So every member pinned by a
collection version, kept anywhere, lies one step below it, unless the
member's object has been taken down. Nothing a collection pins is missing
from what lies below it, except what a takedown removed, which the
verifier reports as removed (section 14).

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

Without takedowns, the second case cannot occur: in a world built by valid
steps, every pin held resolves (`ValidSteps.pins_ok`, in the model).

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

## The value at a member

The glued section of a world gives each pinned member the content of the
version its pin resolves to. The glued section restricts to the section of
the member's own object, at the object version pinned, whose value there is
that version's content (chapter [Pins and accepted copies](50-pins.md)). So
below a selection version, the glued section is the selection together with
exactly the revisions it vetted, as their pins fix them; whichever copies
the values are read from, they agree.

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

Together: in a world built by events, below every held collection version
lies each member it pins, with the content its pin fixes, or the member
was taken down and its pin reports `removed`.

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
