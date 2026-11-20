# References between documents

A document may refer to an exact version of another one: a short account
of a proof to the version of its detailed argument that a journal reviewed,
a review to the version it reviews, an analysis to the data it used. The
specification's core records such links only in the text of documents and
in DataCite relations (section 4.4), which tools do not follow. Issue
[#21](https://github.com/opensheaf/opensheaf.github.io/issues/21) proposes
a **pinned reference**, a pin with a role, as one building block, and issue
[#28](https://github.com/opensheaf/opensheaf.github.io/issues/28) a first
extension recording such references in `object.json`, for the use case "A
short account of a proof, with its detailed argument". Neither is part of
version 0.2 of the specification; the extension would keep them under
`extensions` in `object.json` (section 2), where the inventory and the
pins fix them.

[Chapter 1](10-basic.md) added them to the model: an object version holds a
list of references, each a role and a pin (with its hints), and their pins
are among the pins it holds. This chapter says what that gives. Everything
proved about pins held applies, and three of the open questions of #28 get
an answer:

- **Direction.** #28 assumes that only the focusing document pins the
  focused one, and that the link back is a plain DataCite relation. The
  model shows that a pinned link back is possible too, in a later version
  of the focused document. It may close a cycle between document versions:
  see below.
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

The chapter ends with the use case, built by valid steps and checked by
computation.

    -- in OpenSheaf/References.lean:
    import OpenSheaf.Story

    namespace OpenSheaf

    open OpenSheaf.Patterns

    variable {D : Type} [DecidableEq D] (E : Env D)

## References are pins

The pin of a reference is a pin held by the version.

    omit [DecidableEq D] in
    theorem Version.ref_pin {v : Version D} {r : Ref D} (hr : r ∈ v.refs) : r.pin ∈ v.pins :=
      List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩))

So the theorems on pins held apply to references. In a world built by valid
steps, every reference is found at one of its hints: a version cannot
refer to a version that does not exist yet, so the referenced version
always exists first ([chapter 7](45-worlds.md)). With takedowns, every
reference is found, or reports `removed`, at one of its hints.

    /-- **References never dangle**, in a world built by valid steps. -/
    theorem ValidSteps.refs_resolve {w : World D}
        (hs : ValidSteps E (fun _ => (none : Option (Archive D))) w)
        {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
        {v : Version D} (hv : v ∈ o.versions) {r : Ref D} (hr : r ∈ v.refs) :
        Found E.hash w r.pin :=
      hs.pins_ok E a oid o hl v hv r.pin (Version.ref_pin hr)

    /-- With takedowns, references are found or report `removed`. -/
    theorem Events.refs_held {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w)
        {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
        {v : Version D} (hv : v ∈ o.versions) {r : Ref D} (hr : r ∈ v.refs) :
        Held E w r.pin :=
      (Events.sound E hs).2 a oid o hl v hv r.pin (Version.ref_pin hr)

## Direction

References form no cycle with each other, nor with the pins of
collections, as long as owners sign one history (the freedom from cycles of
[chapter 12](65-impossible.md)): each version would have to exist before
the other. The link back from a focused document is possible, but from a
later version of it, to a version of the focusing document that refers to
an earlier one.

That holds of object versions. Document versions, the unit of citation, are
another matter. A reference is not content, so the link back can be added
by a description-only version, which keeps the document version: in the
example below, document version 2 of the detailed argument refers to
document version 1 of the account, which refers to document version 2 of
the detailed argument. Whether references belong to the document version or
to the object version is a question for #28.

## What a pin fixes

A pin of a version fixes its references, and so, through them, the versions
they name: "the hash tree goes on through the link" (the use case). A
verifier that knows references reports them with their results.

    /-- What a verifier aware of references reports for a version. -/
    def verifyRefs (w : World D) (v : Version D) : List (Ref D × Resolution D) :=
      v.refs.map fun r => (r, resolve E.hash w r.pin)

If a pin resolves to a version whose references all resolve, then after any
number of steps it resolves to the same version, whose references resolve
as before, when the owners of the lines pinned sign one history (`HonestPins`,
[chapter 11](60-patterns.md)). This is what a selection pinning the account
vets implicitly: the detailed argument, in the version the account names.

    /-- **A pin fixes what the version refers to.** -/
    theorem pin_fixes_refs {w w' : World D}
        (hw' : Events E (fun _ => (none : Option (Archive D))) w') (hs : Steps w w') {p : Pin D}
        {a : Version D} (hp : resolve E.hash w p = .ok a) (hhp : HonestPins E w' [p])
        (hhr : HonestPins E w' (a.refs.map (·.pin)))
        (hok : ∀ r ∈ a.refs, ∃ d, resolve E.hash w r.pin = .ok d) :
        resolve E.hash w' p = .ok a ∧ verifyRefs E w' a = verifyRefs E w a := by
      have h1 := hhp p (List.mem_singleton_self _)
      refine ⟨Steps.resolve_ok E hw' hs h1.1 h1.2 hp, ?_⟩
      unfold verifyRefs
      apply List.map_congr_left
      intro r hr
      obtain ⟨d, hd⟩ := hok r hr
      have h2 := hhr r.pin (List.mem_map.mpr ⟨r, hr, rfl⟩)
      rw [Steps.resolve_ok E hw' hs h2.1 h2.2 hd, hd]

Any copy of the version, mirror or not, carries the same references, unless
its inventory collides with the original's: they are part of the version
the pin fixes (`copy_authentic`, [chapter 9](48-copies.md)). The versions
they name are another matter: they are kept where they are kept, and a copy
of the account does not copy them.

    /-- **References travel with every copy.** -/
    theorem copy_keeps_refs {o c : Obj D} {p : Pin D} {a u : Version D}
        (hcol : NoCollision E (c.inventory p.version) (o.inventory p.version))
        (ho : resolveEntry E.hash (some (.live o)) p = .ok a)
        (hc : resolveEntry E.hash (some (.live c)) p = .ok u) : u.refs = a.refs := by
      rw [copy_authentic E hcol ho hc]

## Vetting through a reference

A takedown of the referenced line at an archive leaves every pin of a
selection that does not look for that line there as it was: a verifier of
the selection that knows only the core reports exactly what it reported
before. The reference reports `removed` at that archive.

    /-- **A core verifier does not see a takedown behind a reference.** -/
    theorem takedown_behind_ref {w : World D} {b : ArchiveId} {x : ObjectId} {o : Obj D}
        (hl : lookup w b x = some (.live o)) {s : Members D}
        (hs : ∀ p ∈ s.pins, ∀ c ∈ p.hints, ¬ (c = b ∧ ObjectId.line p.line = x)) {r : Ref D}
        (hr : ObjectId.line r.pin.line = x) :
        verify E (takedown E.hash w b x o) s = verify E w s ∧
          resolveAt E.hash (takedown E.hash w b x o) b r.pin = .removed := by
      refine ⟨?_, takedown_removed E.hash hl hr⟩
      unfold verify
      apply List.map_congr_left
      intro p hp
      unfold resolve
      congr 2
      apply List.map_congr_left
      intro c hc
      rw [takedown_other E.hash hl (hs p hp c hc)]

So implicit vetting fixes what the journal vetted, but does not report its
loss. The use case's second selection, pinning the detailed argument
explicitly, makes core verifiers report it.

    end OpenSheaf

## The use case, computed

An author keeps a short account of a proof and its detailed argument in its
archive; a journal vets the account in an issue, and mirrors it. The owners
are those of [the first story](70-story.md), with their keys; the digest is
its toy digest, and each step is a valid step.

    -- in OpenSheaf/References.lean:
    namespace OpenSheaf.Companions

    open OpenSheaf OpenSheaf.Patterns OpenSheaf.Story

The detailed argument comes first, with two versions: the second closes a
gap and adds a formal proof. The author seals it with both, and signs the
second, which vouches for the first (section 7.3).

    def genDt : Genesis Nat := { kind := .document, nonce := "details", originator := "author" }
    def detailsLine : LineId := ⟨"details", "author"⟩

    def d1 : Version Nat :=
      { documentVersion := 1, files := [("details.tm", 61)], description := "The detailed argument",
        depositor := "author", message := "first version" }

    def d2 : Version Nat :=
      Version.revise [d1] [("details.tm", 62), ("details.lean", 63)] none "The detailed argument"
        "author" "a gap closed; with a formal proof"

    def details0 : Obj Nat :=
      { id := .line detailsLine, kind := .document, genesis := some genDt, versions := [d1, d2] }

    def sigD2 : Sig Nat := ⟨detailsLine, 2, toy (details0.inventory 2), "a1", logPin "author" logA1 1⟩

    def details2 : Obj Nat := { details0 with sigs := [sigD2] }

The account refers to version 2 of the detailed argument, with the role
`IsSupplementedBy`. Its creation is valid only because that version exists.

    def pinD2 : Pin Nat := ⟨detailsLine, 2, toy (details2.inventory 2), ["author"]⟩

    def genAc : Genesis Nat := { kind := .document, nonce := "account", originator := "author" }
    def accountLine : LineId := ⟨"account", "author"⟩

    def a1 : Version Nat :=
      { documentVersion := 1, files := [("account.tm", 71)], description := "A short account",
        refs := [⟨"IsSupplementedBy", pinD2⟩], depositor := "author", message := "first version" }

    def account0 : Obj Nat :=
      { id := .line accountLine, kind := .document, genesis := some genAc, versions := [a1] }

    def sigA1 : Sig Nat := ⟨accountLine, 1, toy (account0.inventory 1), "a1", logPin "author" logA1 1⟩

    def account : Obj Nat := { account0 with sigs := [sigA1] }

The detailed argument links back, by a description-only version of its
version 2, whose reference pins the account's version 1. It keeps the
document version: references are not content.

    def pinA1 : Pin Nat := ⟨accountLine, 1, toy (account.inventory 1), ["author", "journal"]⟩

    def d3 : Version Nat :=
      { Version.describe [d1, d2] d2 "The detailed argument" "author" "link back to the account"
        with refs := [⟨"IsSupplementTo", pinA1⟩] }

    def sigD3 : Sig Nat :=
      ⟨detailsLine, 3, toy ((details2.append d3).inventory 3), "a1", logPin "author" logA1 1⟩

    def details3 : Obj Nat := details2.append d3 [sigD3]

    example : d3.documentVersion = d2.documentVersion := by decide

The journal vets the account, in an issue that pins its version 1, and
keeps a mirror of it, which a member's hints may name.

    def issue7 : Members Nat :=
      { type := .selection,
        members := [{ line := accountLine, hints := ["author", "journal"], pins := [pinA1] }] }

    def genI7 : Genesis Nat := { kind := .collection, nonce := "issue7", originator := "journal" }
    def issueLine : LineId := ⟨"issue7", "journal"⟩

    def i1 : Version Nat :=
      { documentVersion := 1, files := [], members := some issue7, description := "Issue 7",
        depositor := "journal", message := "accepted: the account, version 1" }

    def issue0 : Obj Nat :=
      { id := .line issueLine, kind := .collection, genesis := some genI7, versions := [i1] }

    def sigI1 : Sig Nat := ⟨issueLine, 1, toy (issue0.inventory 1), "j1", logPin "journal" logJ 1⟩

    def issueObj : Obj Nat := { issue0 with sigs := [sigI1] }

The signatures made, and the environment:

    def madeC : List (Sig Nat) := [sigD2, sigA1, sigD3, sigI1]

    def EC : Env Nat :=
      { hash := toy, keyDigest := keyDigest, nameOf := nameOf, verifies := fun s => decide (s ∈ madeC) }

The worlds and the steps: the archives, the key logs (the author's also
beside the journal's mirror), the detailed argument, the account, the link
back, the issue and the mirror.

    def y0 : World Nat := fun _ => none
    def y1 : World Nat := fun b => if b = "author" then some (arch ["author"]) else y0 b
    def y2 : World Nat := fun b => if b = "journal" then some (arch ["journal"]) else y1 b
    def y3 : World Nat := setEntry y2 "author" (logLine "author") (.live logA1)
    def y4 : World Nat := setEntry y3 "journal" (logLine "journal") (.live logJ)
    def y5 : World Nat := setEntry y4 "journal" (logLine "author") (.live logA1)
    def y6 : World Nat := setEntry y5 "author" (.line detailsLine) (.live details2)
    def y7 : World Nat := setEntry y6 "author" (.line accountLine) (.live account)
    def y8 : World Nat := setEntry y7 "author" (.line detailsLine) (.live details3)
    def y9 : World Nat := setEntry y8 "journal" (.line issueLine) (.live issueObj)
    def y10 : World Nat := setEntry y9 "journal" (.line accountLine) (.live account)

    theorem b1 : ValidStep EC y0 y1 := .newArchive _ _ _ rfl (fun _ => rfl)
    theorem b2 : ValidStep EC y1 y2 := .newArchive _ _ _ rfl (fun _ => rfl)

    theorem b3 : ValidStep EC y2 y3 := create_keyLog rfl rfl (by decide)
    theorem b4 : ValidStep EC y3 y4 := create_keyLog rfl rfl (by decide)
    theorem b5 : ValidStep EC y4 y5 := create_keyLog rfl rfl (by decide)

    theorem b6 : ValidStep EC y5 y6 := create_hosted rfl rfl rfl (no_pins (by decide)) (by decide)
    theorem b7 : ValidStep EC y6 y7 := create_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)
    theorem b8 : ValidStep EC y7 y8 := append_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)
    theorem b9 : ValidStep EC y8 y9 := create_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)

    theorem copy_y9 : CopyOf y9 "journal" account := ⟨"author", account, by decide, rfl, rfl, [], by simp⟩

    theorem b10 : ValidStep EC y9 y10 :=
      create_copy rfl rfl rfl copy_y9 (pins_resolve (by decide)) (by decide)

    theorem valid : ValidSteps EC y0 y10 :=
      .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.refl _) b1) b2) b3) b4)
        b5) b6) b7) b8) b9) b10

## What the verifiers report

The issue verifies; the account's reference resolves to the version of the
detailed argument it names, and the link back to the account's version 1.

    example : verify EC y10 issue7 = [(pinA1, .ok a1)] := by decide

    example : verifyRefs EC y10 a1 = [(⟨"IsSupplementedBy", pinD2⟩, .ok d2)] := by decide

    example : verifyRefs EC y10 d3 = [(⟨"IsSupplementTo", pinA1⟩, .ok a1)] := by decide

The general theorem says the same without computing: the reference is
found, since the world was built by valid steps.

    example : Found toy y10 pinD2 :=
      ValidSteps.refs_resolve EC valid (a := "author") (oid := .line accountLine) (o := account) rfl
        (v := a1) (by simp [account, account0]) (r := ⟨"IsSupplementedBy", pinD2⟩) (by simp [a1])

A link back to a later version of the account, one that would refer to the
newest version of the detailed argument, cannot be made: that version of
the account does not exist when the link is written.

    example : (resolve toy y7 ⟨accountLine, 2, 0, ["author"]⟩).isOk = false := by decide

## Copies

The author's archive disappears. The journal's mirror gives the account,
with its reference (`copy_keeps_refs`); the version it names is not on the
mirror, and cannot be found.

    def yGone : World Nat := fun b => if b = "author" then none else y10 b

    example : resolve toy yGone pinA1 = .ok a1 := by decide

    example : resolve toy yGone { pinD2 with hints := ["author", "journal"] } = .unavailable := by
      decide

## A takedown behind the reference

The detailed argument is taken down. The issue verifies as before for a
verifier that knows only the core; the reference reports `removed`.

    def yDown : World Nat := takedown toy y10 "author" (.line detailsLine) details3

    example : verify EC yDown issue7 = [(pinA1, .ok a1)] := by decide

    example : verifyRefs EC yDown a1 = [(⟨"IsSupplementedBy", pinD2⟩, .removed)] := by decide

The general theorem gives both, for every selection and every reference:

    example : verify EC yDown issue7 = verify EC y10 issue7 ∧
        resolveAt toy yDown "author" pinD2 = .removed :=
      takedown_behind_ref EC (o := details3) rfl (by decide) (r := ⟨"IsSupplementedBy", pinD2⟩) rfl

    end OpenSheaf.Companions
