# References between documents

A document may refer to an exact version of another one: a short account
of a proof to the version of its detailed argument that a journal reviewed,
a review to the version it reviews, an analysis to the data it used. The
specification's core records such links only in the text of documents and
in DataCite relations (section 8.1), which tools do not follow. Issue
[#21](https://github.com/opensheaf/opensheaf.github.io/issues/21) proposes
a **pinned reference**, a pin with a role, as one building block, and issue
[#28](https://github.com/opensheaf/opensheaf.github.io/issues/28) a first
extension recording such references in `object.json`, for the use case "A
short account of a proof, with its detailed argument".

[Chapter 1](10-basic.md) added them to the model: an object version holds a
list of references, each a role and a pin, and their pins are among the
pins it holds. This chapter says what that gives. Everything proved about
pins held applies, and three of the open questions of #28 get an answer:

- **Direction.** #28 assumes that only the focusing document pins the
  focused one, and that the link back is a plain DataCite relation. The
  model shows that a pinned link back is possible too, in a later version
  of the focused document, and that it never closes a cycle between object
  versions. It may close one between document versions: see below.
- **What copying does.** Every copy of a version carries its references,
  since they are part of what the pin fixes; the versions they name are not
  copied with it. Mirroring the account does not keep the detailed argument
  available.
- **Vetting.** A selection that pins the account fixes the detailed
  argument too, through the account's reference: implicit vetting is
  sound. But a verifier of the selection that knows only the core does not
  look at references: when the detailed argument is taken down, the
  selection verifies as before. Only a verifier that knows the extension,
  or a second selection pinning the detailed argument explicitly, reports
  it.

The chapter ends with the use case, built by acts and checked by
computation.

    -- in OpenSheaf/References.lean:
    import OpenSheaf.Story

    namespace OpenSheaf

    open OpenSheaf.Patterns

    variable {D : Type} [DecidableEq D] (hash : Hash D)

## References are pins

The pin of a reference is a pin held by the version.

    omit [DecidableEq D] in
    theorem Version.ref_pin {v : Version D} {r : Ref D} (hr : r ∈ v.refs) : r.pin ∈ v.pins :=
      List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)

So the theorems on pins held apply to references. In a world built by valid
steps, every reference resolves: a version cannot refer to a version that
does not exist yet, so the referenced version always exists first ([chapter
5](45-worlds.md)). With takedowns, every reference resolves or reports
`removed`.

    /-- **References never dangle**, in a world built by valid steps. -/
    theorem ValidSteps.refs_resolve {w : World D}
        (hs : ValidSteps hash (fun _ => (none : Option (Archive D))) w)
        {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
        {v : Version D} (hv : v ∈ o.versions) {r : Ref D} (hr : r ∈ v.refs) :
        ∃ t, resolve hash w r.pin = .ok t :=
      hs.pins_ok hash a oid o hl v hv r.pin (Version.ref_pin hr)

    /-- With takedowns, references resolve or report `removed`. -/
    theorem Events.refs_held {w : World D}
        (hs : Events hash (fun _ => (none : Option (Archive D))) w)
        {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
        {v : Version D} (hv : v ∈ o.versions) {r : Ref D} (hr : r ∈ v.refs) :
        (∃ t, resolve hash w r.pin = .ok t) ∨ resolve hash w r.pin = .removed :=
      (Events.sound hash hs).2 a oid o hl v hv r.pin (Version.ref_pin hr)

## Direction

References form no cycle with each other, nor with the pins of collections
(`no_cycles_events`, [chapter 10](65-impossible.md)). In particular two
versions never refer to each other: each would have to exist before the
other. The link back from a focused document is possible, but from a later
version of it, to a version of the focusing document that refers to an
earlier one.

The model proves this for object versions. Document versions, the unit of
citation, are another matter. A reference is not content, so the link back
can be added by a description-only version, which keeps the document
version: in the example below, document version 2 of the detailed argument
refers to document version 1 of the account, which refers to document
version 2 of the detailed argument. Whether references belong to the
document version or to the object version is a question for #28 (and #24,
what a description-only version may change).

    /-- **No two versions refer to each other**, in a world built by events. -/
    theorem no_mutual_refs {w : World D}
        (hs : Events hash (fun _ => (none : Option (Archive D))) w) {s t : Site}
        (h1 : PinsTo hash w s t) : ¬ PinsTo hash w t s :=
      fun h2 => no_cycles_events hash hs s (.cons h1 (.single h2))

## What a pin fixes

A pin of a version fixes its references, and so, through them, the versions
they name: "the hash tree goes on through the link" (the use case). A
verifier that knows references reports them with their results.

    /-- What a verifier aware of references reports for a version. -/
    def verifyRefs (w : World D) (v : Version D) : List (Ref D × Resolution D) :=
      v.refs.map fun r => (r, resolve hash w r.pin)

If a pin resolves to a version whose references all resolve, then after any
number of steps it resolves to the same version, whose references resolve
as before. This is what a selection pinning the account vets implicitly:
the detailed argument, in the version the account names.

    /-- **A pin fixes what the version refers to.** -/
    theorem pin_fixes_refs {w w' : World D} (hs : Steps w w') {p : Pin D} {a : Version D}
        (hp : resolve hash w p = .ok a) (hok : ∀ r ∈ a.refs, ∃ d, resolve hash w r.pin = .ok d) :
        resolve hash w' p = .ok a ∧ verifyRefs hash w' a = verifyRefs hash w a := by
      refine ⟨Steps.resolve_ok hash hs hp, ?_⟩
      unfold verifyRefs
      apply List.map_congr_left
      intro r hr
      obtain ⟨d, hd⟩ := hok r hr
      rw [Steps.resolve_ok hash hs hd, hd]

Any copy of the version, mirror or not, carries the same references, unless
its inventory collides with the original's: they are part of the version
the pin fixes (`copy_authentic`, [chapter 6](48-copies.md)). The versions
they name are another matter: they are kept where they are kept, and a copy
of the account does not copy them.

    /-- **References travel with every copy.** -/
    theorem copy_keeps_refs {o c : Obj D} {p : Pin D} {a u : Version D}
        (hcol : NoCollision hash (c.inventory p.version) (o.inventory p.version))
        (ho : resolveEntry hash (some (.live o)) p = .ok a)
        (hc : resolveEntry hash (some (.live c)) p = .ok u) : u.refs = a.refs := by
      rw [copy_authentic hash hcol ho hc]

## Vetting through a reference

A takedown of the referenced object leaves every pin of a selection that
does not name it as it was: a verifier of the selection that knows only the
core reports exactly what it reported before. The reference reports
`removed`.

    /-- **A core verifier does not see a takedown behind a reference.** -/
    theorem takedown_behind_ref {w : World D} {b : ArchiveId} {x : ObjectId} {o : Obj D}
        (hl : lookup w b x = some (.live o)) {s : Members D}
        (hs : ∀ p ∈ s.pins, ¬ (p.archive = b ∧ p.object = x)) {r : Ref D}
        (hr : r.pin.archive = b ∧ r.pin.object = x) :
        verify hash (takedown hash w b x o) s = verify hash w s ∧
          resolve hash (takedown hash w b x o) r.pin = .removed := by
      refine ⟨?_, takedown_removed hash hl hr⟩
      unfold verify
      apply List.map_congr_left
      intro p hp
      rw [takedown_other hash hl (hs p hp)]

So implicit vetting fixes what the journal vetted, but does not report its
loss. The use case's second selection, pinning the detailed argument
explicitly, makes core verifiers report it.

    end OpenSheaf

## The use case, computed

An author keeps a short account of a proof and its detailed argument in
her archive (`author`); a journal (`journal`) vets the account in an issue,
and mirrors it. The digest is the toy digest of [the first
story](70-story.md), and each step is made by an agent.

    -- in OpenSheaf/References.lean:
    namespace OpenSheaf.Companions

    open OpenSheaf OpenSheaf.Patterns OpenSheaf.Story

    def y0 : World Nat := fun _ => none
    def y1 : World Nat := fun b => if b = "author" then some (emptyArchive ["author"]) else y0 b
    def y2 : World Nat := fun b => if b = "journal" then some (emptyArchive ["editor"]) else y1 b

    theorem b1 : StepBy toy "author" y0 y1 := .newArchive _ _ _ rfl (fun _ => rfl) (by decide)
    theorem b2 : StepBy toy "editor" y1 y2 := .newArchive _ _ _ rfl (fun _ => rfl) (by decide)

The detailed argument comes first, with two versions: the second closes a
gap and adds a formal proof.

    def d1 : Version Nat :=
      { documentVersion := 1, files := [("details.tm", 61)], description := "The detailed argument",
        depositor := "author", message := "first version" }

    def d2 : Version Nat :=
      Version.revise [d1] [("details.tm", 62), ("details.lean", 63)] none "The detailed argument"
        "author" "a gap closed; with a formal proof"

    def details2 : Obj Nat :=
      { archive := "author", id := "kpz-details", kind := .document, versions := [d1, d2] }

    def y3 : World Nat := setEntry y2 "author" "kpz-details" (.live details2)

    theorem b3 : StepBy toy "author" y2 y3 :=
      .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
        (by simp [details2, d1, d2, Version.revise, Version.pins]) (Or.inl rfl) (by decide)
        (by decide) (by decide) (sourceOk_all_none toy (by decide))

The account refers to version 2 of the detailed argument, with the role
`IsSupplementedBy`. Its creation is valid only because that version exists.

    def pinD2 : Pin Nat := ⟨"author", "kpz-details", 2, toy (details2.inventory 2)⟩

    def a1 : Version Nat :=
      { documentVersion := 1, files := [("account.tm", 71)], description := "A short account",
        refs := [⟨"IsSupplementedBy", pinD2⟩], depositor := "author", message := "first version" }

    def account : Obj Nat :=
      { archive := "author", id := "kpz-account", kind := .document, versions := [a1] }

    def y4 : World Nat := setEntry y3 "author" "kpz-account" (.live account)

    theorem b4 : StepBy toy "author" y3 y4 :=
      .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
        (fun v hv p hp => pinOk_of_isOk ((by decide :
          ∀ v ∈ account.versions, ∀ p ∈ v.pins, (resolve toy y3 p).isOk = true) v hv p hp))
        (Or.inl rfl) (by decide) (by decide) (by decide) (sourceOk_all_none toy (by decide))

The detailed argument links back, by a description-only version of its
version 2, whose reference pins the account's version 1. It keeps the
document version: references are not content.

    def pinA1 : Pin Nat := ⟨"author", "kpz-account", 1, toy (account.inventory 1)⟩

    def d3 : Version Nat :=
      { Version.describe [d1, d2] d2 "The detailed argument" "author" "link back to the account"
        with refs := [⟨"IsSupplementTo", pinA1⟩] }

    def details3 : Obj Nat := details2.append d3

    def y5 : World Nat := setEntry y4 "author" "kpz-details" (.live details3)

    theorem b5 : StepBy toy "author" y4 y5 :=
      .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
        (fun p hp => pinOk_of_isOk ((by decide :
          ∀ p ∈ d3.pins, (resolve toy y4 p).isOk = true) p hp)) (Or.inl rfl) (by decide)
        (by decide) (by decide) (sourceOk_none toy rfl)

    example : d3.documentVersion = d2.documentVersion := by decide

The journal vets the account, in an issue that pins its version 1, and
keeps a mirror of it.

    def issue7 : Members Nat :=
      { type := .selection,
        members := [{ archive := "author", object := "kpz-account", pins := [pinA1] }] }

    def i1 : Version Nat :=
      { documentVersion := 1, files := [], members := some issue7, description := "Issue 7",
        depositor := "editor", message := "accepted: the account, version 1" }

    def issueObj : Obj Nat :=
      { archive := "journal", id := "issue-7", kind := .collection, versions := [i1] }

    def y6 : World Nat := setEntry y5 "journal" "issue-7" (.live issueObj)
    def y7 : World Nat := setEntry y6 "journal" "kpz-account" (.live account)

    theorem b6 : StepBy toy "editor" y5 y6 :=
      .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
        (fun v hv p hp => pinOk_of_isOk ((by decide :
          ∀ v ∈ issueObj.versions, ∀ p ∈ v.pins, (resolve toy y5 p).isOk = true) v hv p hp))
        (Or.inl rfl) (by decide) (by decide) (by decide) (sourceOk_all_none toy (by decide))

    theorem b7 : StepBy toy "editor" y6 y7 :=
      .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
        (fun v hv p hp => pinOk_of_isOk ((by decide :
          ∀ v ∈ account.versions, ∀ p ∈ v.pins, (resolve toy y6 p).isOk = true) v hv p hp))
        (Or.inr ⟨account, rfl, rfl, [], (List.append_nil _).symm⟩) (by decide) (by decide) (by decide) (sourceOk_all_none toy (by decide))

    theorem steps : Star ByAgent y0 y7 :=
      .tail (.tail (.tail (.tail (.tail (.tail (.tail (.refl _)
        ⟨_, b1⟩) ⟨_, b2⟩) ⟨_, b3⟩) ⟨_, b4⟩) ⟨_, b5⟩) ⟨_, b6⟩) ⟨_, b7⟩

    theorem valid : ValidSteps toy y0 y7 := steps.mono fun ⟨_, h⟩ => h.toValidStep toy

## What the verifiers report

The issue verifies; the account's reference resolves to the version of the
detailed argument it names, and the link back to the account's version 1.

    example : verify toy y7 issue7 = [(pinA1, .ok a1)] := by decide

    example : verifyRefs toy y7 a1 = [(⟨"IsSupplementedBy", pinD2⟩, .ok d2)] := by decide

    example : verifyRefs toy y7 d3 = [(⟨"IsSupplementTo", pinA1⟩, .ok a1)] := by decide

The general theorems say the same without computing: the reference
resolves, since the world was built by valid steps, and there is no cycle
of object versions, although the two documents refer to each other (as
document versions, they do form a cycle: see "Direction" above).

    example : ∃ t, resolve toy y7 pinD2 = .ok t :=
      ValidSteps.refs_resolve toy valid (a := "author") (oid := "kpz-account") (o := account) rfl
        (v := a1) (by simp [account]) (r := ⟨"IsSupplementedBy", pinD2⟩) (by simp [a1])

    example (s : Site) : ¬ Chain (PinsTo toy y7) s s := no_cycles toy valid s

A link back to a later version of the account, one that would refer to the
newest version of the detailed argument, cannot be made: that version of
the account does not exist when the link is written.

    example : (resolve toy y4 ⟨"author", "kpz-account", 2, 0⟩).isOk = false := by decide

## Copies

The author's archive disappears. The journal's mirror gives the account,
with its reference (`copy_keeps_refs`); the version it names is not on the
mirror, and cannot be found.

    def yGone : World Nat := fun b => if b = "author" then none else y7 b

    example : resolveVia toy yGone pinA1 ["journal"] = .ok a1 := by decide

    example : resolveVia toy yGone pinD2 ["journal"] = .unavailable := by decide

## A takedown behind the reference

The detailed argument is taken down. The issue verifies as before for a
verifier that knows only the core; the reference reports `removed`.

    def yDown : World Nat := takedown toy y7 "author" "kpz-details" details3

    example : verify toy yDown issue7 = [(pinA1, .ok a1)] := by decide

    example : verifyRefs toy yDown a1 = [(⟨"IsSupplementedBy", pinD2⟩, .removed)] := by decide

The general theorem gives both, for every selection and every reference:

    example : verify toy yDown issue7 = verify toy y7 issue7 ∧ resolve toy yDown pinD2 = .removed :=
      takedown_behind_ref toy (o := details3) rfl (by decide) (r := ⟨"IsSupplementedBy", pinD2⟩)
        ⟨rfl, rfl⟩

    end OpenSheaf.Companions
