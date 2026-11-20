# Collections and what they pin

So far each object is a separate part of the base: a collection says
nothing, in the order, about its members. But a collection version holds
pins in its member list, and the model counts the member list as part of
the content of the document version (section 4.2). A selection version is
the selection *together with* the revisions it vetted, and a catalogue
version the catalogue together with the versions it pinned. In the order
with pins, below a selection version lies more than the selection: the
order of deposit puts the earlier document versions of each revision below
it too. Section 8.4 says they are not part of the selection; they lie
below it because they are fixed by its pins, not because it vetted them.

This chapter adds those pins to the order. A named document version comes
before a collection version whose member list pins it. Below a collection
version there are then the earlier versions of the collection, the
versions it pins, their earlier versions, and so on. The value of the glued
section there is the collection together with everything it pins. The
chapter proves three things:

- the named document versions held in a world stay an open set in the
  larger order: what a held collection pins, when it resolves, is held;
- in every world built by events, every member pinned by a held collection
  version lies below it, unless its line has been taken down at its hints,
  and then the pin reports `removed`; without takedowns, every member lies
  below it;
- the glued section gives each pinned member the content its pin fixes.

## The order with pins

A pin names an object version of a line, not a document version. The edge
goes to the document version that the object version holds, which the
world tells: it is where the pin resolves, at one of its hints. So the
order depends on the world, and on the digest function, through
resolution. Where a pin resolves at an archive is fixed once it resolves
(immutability, in the model), so the edges of a world are kept by every
later step, and a takedown adds none (it may remove some). The next
chapter, [The order with pins](57-acyclic.md), proves both.

The edge goes to the name of the copy found, its line. A copy found at a
hint is a copy of the pin's line, and in version 0.2 every copy of a line
has the same name, so there is no question of which archive a pin names
(the question of issue #38 of version 0.1 is gone). Edges go only to copies
that are not key logs, which no pin names (`PinOk`, in the model).

Only the pins of member lists give edges. The references of a document
(issues #21 and #28) are left out: in the model a description-only version
may change them, so they belong to object versions, not to document
versions. So are branch points, which a version of a branch may keep while
its own files change.

    -- in Sheaf/Collections.lean:
    import Sheaf.Pins

    namespace OpenSheaf.Sheaf

    variable {D : Type} [DecidableEq D] (E : Env D)

    omit [DecidableEq D] in
    /-- The pins of a member list (the model's `Version.memberPins`) are pins
    of the version. -/
    theorem memberPins_sub {v : Version D} {p : Pin D} (h : p ∈ v.memberPins) : p ∈ v.pins :=
      List.mem_append_left _ (List.mem_append_left _ h)

    /-- `y` comes before `x` by a pin: a version holding `x`, in a copy kept
    anywhere, pins in its member list an object version that resolves at one of
    the pin's hints, in a copy that holds `y`. -/
    def PinStep (w : World D) (y x : Name) : Prop :=
      ∃ (b : ArchiveId) (l : LineId) (c : Obj D) (v : Version D) (p : Pin D) (b' : ArchiveId)
        (o : Obj D) (u : Version D),
        lookup w b (.line l) = some (.live c) ∧ c.kind ≠ .owner ∧ v ∈ c.versions ∧ x = c.name v ∧
          p ∈ v.memberPins ∧ b' ∈ p.hints ∧ lookup w b' (.line p.line) = some (.live o) ∧
          o.kind ≠ .owner ∧ resolveAt E.hash w b' p = .ok u ∧ y = o.name u

    /-- One step down: an earlier version of the same line, or a pinned member. -/
    def Before (w : World D) (y x : Name) : Prop := deposit.le y x ∨ PinStep E w y x

    /-- The order of deposit and pins: any number of steps down. -/
    def byPins (w : World D) : Order Name where
      le := Star (Before E w)
      refl x := Star.refl x
      trans h1 h2 := h1.trans h2

A set is open in this order when it is closed under one step down; the
general case follows along the steps.

    theorem open_of_before {w : World D} {U : Name → Prop}
        (h : ∀ {y x}, Before E w y x → U x → U y) : (byPins E w).IsOpen U := by
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
world built by valid steps with honest owners it is also a partial order,
which the next chapter proves.

## What a world holds is open

The named document versions held in a world are closed under both kinds of
step. An earlier version of the same line is held by the same source. A
pinned member that resolves is held by the copy where it resolves, at the
object version pinned.

    /-- **What a world holds is open in the order with pins.** -/
    theorem heldIn_open_byPins {w : World D} (hw : SoundWorld E w) :
        (byPins E w).IsOpen (HeldIn w) := by
      apply open_of_before
      intro y x hb hx
      rcases hb with hh | ⟨b, l, c, v, p, b', o, u, _, _, _, rfl, _, _, ho, hko, hr, rfl⟩
      · exact heldIn_open w hh hx
      · unfold resolveAt at hr
        rw [ho] at hr
        exact heldIn_of_live E hw ho hko (versionAt_mem (resolveEntry_live_ok E.hash hr).1)

## Every member lies below its collection

A pin that resolves at one of its hints, in a copy that is not a key log,
gives an edge, from the collection version that holds it down to the
member.

    theorem below_of_ok {w : World D} {b : ArchiveId} {l : LineId} {c : Obj D}
        {v : Version D} {p : Pin D} {b' : ArchiveId} {u : Version D}
        (hl : lookup w b (.line l) = some (.live c)) (hk : c.kind ≠ .owner) (hv : v ∈ c.versions)
        (hp : p ∈ v.memberPins) (hb' : b' ∈ p.hints) (hu : resolveAt E.hash w b' p = .ok u)
        (hko : ∀ o, lookup w b' (.line p.line) = some (.live o) → o.kind ≠ .owner) :
        ∃ o, lookup w b' (.line p.line) = some (.live o) ∧
          (byPins E w).le (o.name u) (c.name v) := by
      have hu' := hu
      unfold resolveAt at hu'
      obtain ⟨o, ho⟩ := resolveEntry_ok_live E.hash hu'
      exact ⟨o, ho, Star.tail (Star.refl _)
        (Or.inr ⟨b, l, c, v, p, b', o, u, hl, hk, hv, rfl, hp, hb', ho, hko o ho, hu, rfl⟩)⟩

In a world built by events, every pin held by a version is found at one of
its hints, or reports `removed` at one (`Events.sound`, in the model); and
a copy of kind `owner` sits at the line of a key log
(`Events.keyLog_line`), which no pin held names (`Events.pinsNoKeyLog`,
`Events.pinned_not_owner`). So every member pinned by a
collection version, kept anywhere, lies one step below it, unless its line
has been taken down at a hint. Nothing a collection pins is missing from
what lies below it, except what a takedown removed, which the verifier
reports as removed (section 8.5).

    theorem Events.not_owner {w : World D} (hs : Events E (fun _ => (none : Option (Archive D))) w)
        {p : Pin D} (hnk : p.line ≠ keyLogLine p.line.owner) {b : ArchiveId} :
        ∀ o, lookup w b (.line p.line) = some (.live o) → o.kind ≠ .owner :=
      fun _ ho hk => hnk (Events.keyLog_line E hs ho hk)

    /-- **Every member lies below its collection**, or was taken down. -/
    theorem members_below {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {b : ArchiveId}
        {l : LineId} {c : Obj D} {v : Version D} {p : Pin D}
        (hl : lookup w b (.line l) = some (.live c)) (hk : c.kind ≠ .owner) (hv : v ∈ c.versions)
        (hp : p ∈ v.memberPins) :
        (∃ b' ∈ p.hints, ∃ o u, lookup w b' (.line p.line) = some (.live o) ∧
          resolveAt E.hash w b' p = .ok u ∧ (byPins E w).le (o.name u) (c.name v)) ∨
          RemovedAt E w p := by
      rcases (Events.sound E hs).2 _ _ _ hl v hv p (memberPins_sub hp) with ⟨b', hb', u, hu⟩ | hr
      · obtain ⟨o, ho, hle⟩ := below_of_ok E hl hk hv hp hb' hu
          (fun o ho => Events.pinned_not_owner E hs hl hv (memberPins_sub hp) ho)
        exact Or.inl ⟨b', hb', o, u, ho, hu, hle⟩
      · exact Or.inr hr

Without takedowns, the second case cannot occur: in a world built by valid
steps, every pin held is found (`ValidSteps.pins_ok`, in the model).

    /-- Without takedowns, every member lies below its collection. -/
    theorem members_below_valid {w : World D}
        (hs : ValidSteps E (fun _ => (none : Option (Archive D))) w) {b : ArchiveId}
        {l : LineId} {c : Obj D} {v : Version D} {p : Pin D}
        (hl : lookup w b (.line l) = some (.live c)) (hk : c.kind ≠ .owner) (hv : v ∈ c.versions)
        (hp : p ∈ v.memberPins) :
        ∃ b' ∈ p.hints, ∃ o u, lookup w b' (.line p.line) = some (.live o) ∧
          resolveAt E.hash w b' p = .ok u ∧ (byPins E w).le (o.name u) (c.name v) := by
      obtain ⟨b', hb', u, hu⟩ := ValidSteps.pins_ok E hs _ _ _ hl v hv p (memberPins_sub hp)
      obtain ⟨o, ho, hle⟩ := below_of_ok E hl hk hv hp hb' hu
        (fun o ho => Events.pinned_not_owner E (hs.mono .step) hl hv (memberPins_sub hp) ho)
      exact ⟨b', hb', o, u, ho, hu, hle⟩

## The value at a member

The glued section of a world gives each pinned member the content of the
version its pin resolves to. The glued section restricts to the section of
the copy where the pin resolves, at the object version pinned, whose value
there is that version's content (chapter [Pins and accepted
copies](50-pins.md)). So below a selection version, the glued section
gives the revisions it vetted the content their pins fix, and everything
else below it the content it has; whichever copies the values are read
from, they agree.

    /-- **The value at a member is what its pin fixes.** -/
    theorem glue_at_member {w : World D} (hw : SoundWorld E w)
        {g : Sec (HeldIn w) (Content D)} (hg : Glues (sections w) g) {p : Pin D} {b' : ArchiveId}
        {o : Obj D} {u : Version D} (ho : lookup w b' (.line p.line) = some (.live o))
        (hko : o.kind ≠ .owner) (hr : resolveAt E.hash w b' p = .ok u) (hy : HeldIn w (o.name u)) :
        g (o.name u) hy = u.content := by
      unfold resolveAt at hr
      rw [ho] at hr
      exact glue_value E hw hg
        ⟨_, _, o, ho, hko, versionAt_mem (resolveEntry_live_ok E.hash hr).1, rfl⟩ hy

Together: in a world built by events, below every held collection version
lies each member it pins, with the content its pin fixes, or the member was
taken down at a hint and its pin reports `removed` there.

    /-- **What lies below a collection version**: each member it pins, with the
    content its pin fixes, or a takedown reported. -/
    theorem collection_members {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w)
        {g : Sec (HeldIn w) (Content D)} (hg : Glues (sections w) g) {b : ArchiveId}
        {l : LineId} {c : Obj D} {v : Version D} {p : Pin D}
        (hl : lookup w b (.line l) = some (.live c)) (hk : c.kind ≠ .owner) (hv : v ∈ c.versions)
        (hp : p ∈ v.memberPins) :
        (∃ b' ∈ p.hints, ∃ (o : Obj D) (u : Version D), lookup w b' (.line p.line) = some (.live o) ∧
          resolveAt E.hash w b' p = .ok u ∧ (byPins E w).le (o.name u) (c.name v) ∧
          ∃ hy : HeldIn w (o.name u), g (o.name u) hy = u.content) ∨
          RemovedAt E w p := by
      rcases members_below E hs hl hk hv hp with ⟨b', hb', o, u, ho, hr, hle⟩ | hr
      · left
        have hx := heldIn_of_live E (Events.sound E hs) hl hk hv
        have hy := heldIn_open_byPins E (Events.sound E hs) hle hx
        exact ⟨b', hb', o, u, ho, hr, hle, hy,
          glue_at_member E (Events.sound E hs) hg ho
            (Events.pinned_not_owner E hs hl hv (memberPins_sub hp) ho) hr hy⟩
      · exact Or.inr hr

    end OpenSheaf.Sheaf
