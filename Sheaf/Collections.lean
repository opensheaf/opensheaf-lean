-- Generated from literate-sheaf/55-collections.md by opensheaf-literate: edit the document, not this file.
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

theorem open_of_before {w : World D} {U : Name → Prop}
    (h : ∀ {y x}, Before E w y x → U x → U y) : (byPins E w).IsOpen U := by
  intro x y hle
  induction hle with
  | refl => exact id
  | tail _ hr ih => exact fun hx => ih (h hr hx)

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
