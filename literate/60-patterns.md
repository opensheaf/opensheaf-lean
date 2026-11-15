# Use cases as theorems

The [use cases](https://opensheaf.org/use-cases.html) of the specification
describe what authors, archives and selections do, and what they can rely
on. This chapter states some of those promises as theorems about the model,
for every world and every sequence of changes. They play the role of tests:
if a change of the model, or of the specification it follows, broke one of
these promises, the proof would no longer go through. The
[story](70-story.md) of chapter 11 does the same for one concrete world,
checked by computation.

    -- in OpenSheaf/Patterns.lean:
    import OpenSheaf.Copies
    import OpenSheaf.Acts

    namespace OpenSheaf.Patterns

    open OpenSheaf

    variable {D : Type} [DecidableEq D] (hash : Hash D)

## Verifying a collection

A verifier checks a collection version by resolving every pin of its member
list (section 14), `Members.pins` of [chapter 1](10-basic.md). The report
pairs each pin with its result. This is less than the verifier of section
14: it resolves each pin in the member's archive only, not through the
mirrors listed in the member (section 6.4), and it does not check the
document versions of a selection's revisions, which the model does not
record ([model issue 2](https://github.com/opensheaf/opensheaf-lean/issues/2)).

    /-- What a verifier reports for a member list: each pin with its result. -/
    def verify (w : World D) (c : Members D) : List (Pin D × Resolution D) :=
      c.pins.map fun p => (p, resolve hash w p)

    /-- Every pin of the member list resolves. -/
    def AllOk (w : World D) (c : Members D) : Prop :=
      ∀ p ∈ c.pins, ∃ v, resolve hash w p = .ok v

A member list whose pins all resolve verifies the same way after any number
of steps: this is immutability, pin by pin. The two use cases below rest on
it.

    /-- A member list that verified verifies the same after any steps. -/
    theorem verify_stable {w w' : World D} (hs : Steps w w') {c : Members D}
        (hok : AllOk hash w c) : verify hash w' c = verify hash w c := by
      unfold verify
      apply List.map_congr_left
      intro p hp
      obtain ⟨v, hv⟩ := hok p hp
      rw [Steps.resolve_ok hash hs hv, hv]

## A journal issue does not change (overlay journal, review journal)

An overlay journal lists an issue as a selection whose members pin the
revisions the editors vetted ("An overlay journal"). The authors go on
depositing new versions, new objects and archives appear. The promise: an issue
that verified once verifies in exactly the same way after any number of
such changes, and updating it never adds the new versions.

    /-- **A vetted selection is stable.** If every pin of a selection resolves,
    then after any number of steps the verifier reports exactly the same, and
    updating the selection leaves it as it is. -/
    theorem selection_stable {w w' : World D} (hs : Steps w w') {c : Members D}
        (hsel : c.type = .selection) (hok : AllOk hash w c) :
        verify hash w' c = verify hash w c ∧ collect hash w' c = c :=
      ⟨verify_stable hash hs hok, collect_selection hash w' hsel⟩

The same holds of a review journal's selection of reviewed papers, of the
record of a peer review, and of a learning record: the property is about
selections, not about who keeps them.

## A digest of digests, a volume of issues

A selection may contain collections ("A digest, a reading list"): a volume
pins its issues, each pinned in the version published. A reader who follows
the volume's pin to an issue, then the issue's pins to the papers, should
find the same papers forever. Pins to collection versions carry their
member lists with them, so this is immutability twice: the volume's pin
keeps naming the same issue version, hence the same member list, and that
list verifies as before.

    /-- **Nested pins are stable.** If a pin resolves to a collection version
    whose pins all resolve, then after any number of steps it resolves to the
    same version, and the member list read through it verifies as before. -/
    theorem nested_stable {w w' : World D} (hs : Steps w w') {q : Pin D} {cv : Version D}
        (hq : resolve hash w q = .ok cv)
        (hok : ∀ c, cv.members = some c → AllOk hash w c) :
        resolve hash w' q = .ok cv ∧
          ∀ c, cv.members = some c → verify hash w' c = verify hash w c :=
      ⟨Steps.resolve_ok hash hs hq, fun c hc => verify_stable hash hs (hok c hc)⟩

## A co-author follows a paper (catalogues)

A co-author lists a joint paper in a catalogue with `follow` ("Co-authors in
different archives"). The promise: after the authors deposit a new version,
updating the catalogue pins it. First, the head of an object after a
deposit is the version deposited.

    /-- After a deposit, the head of the object resolves to the version
    deposited. -/
    theorem head_after_deposit {w : World D} {a : ArchiveId} {ar : Archive D}
        {oid : ObjectId} {o : Obj D} (x : Version D) (ha : w a = some ar) :
        ∃ p, headPin hash (setEntry w a oid (.live (o.append x))) a oid = some p ∧
          resolve hash (setEntry w a oid (.live (o.append x))) p = .ok x := by
      have hl : lookup (setEntry w a oid (.live (o.append x))) a oid =
          some (.live (o.append x)) := by
        rw [lookup_setEntry ha]; simp
      have hp : headPin hash (setEntry w a oid (.live (o.append x))) a oid =
          some ⟨a, oid, (o.append x).versions.length,
            hash ((o.append x).inventory (o.append x).versions.length)⟩ := by
        unfold headPin; rw [hl]; simp [Obj.append]
      refine ⟨_, hp, ?_⟩
      obtain ⟨o', hl', hne, hr⟩ := headPin_resolves hash hp
      rw [hl] at hl'
      cases hl'
      simpa [Obj.append] using hr

The statement needs no hypothesis on what the archive kept under `oid`
before: Lean pointed out that the first version of this theorem assumed the
object existed and never used it. The head after a deposit is the version
deposited, whatever was there.

Then the update of the catalogue: the member following the paper gets that
pin.

    /-- **A followed paper is pinned at its new version.** After the authors
    deposit `x`, updating a catalogue that follows the paper gives the member
    a pin that resolves to `x`. -/
    theorem follow_after_deposit {w : World D} {a : ArchiveId} {ar : Archive D}
        {oid : ObjectId} {o : Obj D} (x : Version D) (ha : w a = some ar)
        {c : Members D} (hcat : c.type = .catalogue)
        {m : Member D} (hm : m ∈ c.members) (hf : m.follow = true)
        (hma : m.archive = a) (hmo : m.object = oid) :
        ∃ p, { m with pins := [p] } ∈
            (collect hash (setEntry w a oid (.live (o.append x))) c).members ∧
          resolve hash (setEntry w a oid (.live (o.append x))) p = .ok x := by
      obtain ⟨p, hp, hr⟩ := head_after_deposit hash (o := o) x ha
      refine ⟨p, collect_follow hash _ hcat hm hf ?_, hr⟩
      rw [hma, hmo]; exact hp

Together with `selection_stable`, this is the difference between the two
kinds of collection, in the case where it matters: the same deposit moves
the catalogue and leaves the selection where it was.

## A correction of the description (description-only versions)

The authors correct a typo in the title of a document version, the current
one or an earlier one ("A researcher's own archive"). The promise: the
correction is a new object version, so it is recorded and pinnable, but not
a new document version, so citations of the document version stay right;
and the history stays well formed.

    /-- **A description-only version is not a new document version.** -/
    theorem correction_same_document_version {o : Obj D} (hwf : WellFormed o.versions)
        {v : Version D} (hv : v ∈ o.versions) (d a m : String) :
        WellFormed (o.append (Version.describe o.versions v d a m)).versions ∧
          (Version.describe o.versions v d a m).documentVersion = v.documentVersion :=
      ⟨WellFormed.snoc hwf (describe_extends hv d a m), rfl⟩

## A withdrawal does not erase what was vetted (section 11.1)

The authors withdraw a paper that a journal has vetted. The promise: the
withdrawal is a new version with status `withdrawn`; the pin of the vetted
revision still resolves to it, exactly as it was vetted. Presentations show
the two together (section 11.1); the model shows that both remain
reachable.

    /-- **Withdrawal keeps the vetted revision.** -/
    theorem withdrawal_keeps_vetted {w : World D} {a : ArchiveId} {ar : Archive D}
        {oid : ObjectId} {o : Obj D} (ha : w a = some ar) (ho : ar.entries oid = some (.live o))
        (hne : o.versions ≠ []) (dep msg : String) {p : Pin D} {v : Version D}
        (hp : resolve hash w p = .ok v) :
        let x := (o.versions.getLast hne).withdraw dep msg
        resolve hash (setEntry w a oid (.live (o.append x))) p = .ok v ∧
          x.status = .withdrawn :=
      ⟨Step.resolve_ok hash (Step.append w a ar oid o _ ha ho) hp, rfl⟩

The first half holds of any version appended, not only of a withdrawal
(it is immutability); only the status is specific. That the withdrawal is
a version the archive may add is [chapter 2](20-object.md)'s
`withdraw_extends` and `withdraw_noReinstatement`.

The table "What happens when ..." of the use cases describes a withdrawal
in both columns at once: a catalogue follows it, and pins the withdrawn
head; a selection does not move, and its vetted revisions verify as
before. One deposit, both columns:

    /-- **A withdrawal, in both columns.** A catalogue following the paper pins
    the withdrawal; a selection of it verifies as before and does not move. -/
    theorem withdrawal_both_columns {w : World D} {a : ArchiveId} {ar : Archive D}
        {oid : ObjectId} {o : Obj D} (ha : w a = some ar) (ho : ar.entries oid = some (.live o))
        (hne : o.versions ≠ []) (dep msg : String)
        {c : Members D} (hcat : c.type = .catalogue) {m : Member D} (hm : m ∈ c.members)
        (hf : m.follow = true) (hma : m.archive = a) (hmo : m.object = oid)
        {s : Members D} (hsel : s.type = .selection) (hok : AllOk hash w s) :
        let x := (o.versions.getLast hne).withdraw dep msg
        let w' := setEntry w a oid (.live (o.append x))
        (∃ p, { m with pins := [p] } ∈ (collect hash w' c).members ∧
            resolve hash w' p = .ok x ∧ x.status = .withdrawn) ∧
          verify hash w' s = verify hash w s ∧ collect hash w' s = s := by
      intro x w'
      obtain ⟨p, hp, hr⟩ := follow_after_deposit hash (o := o) x ha hcat hm hf hma hmo
      exact ⟨⟨p, hp, hr, rfl⟩,
        selection_stable hash (.tail (.refl _) (Step.append w a ar oid o x ha ho)) hsel hok⟩

## A takedown is reported, not hidden (sections 11.2, 14)

A paper vetted by a journal is taken down, by law. The promise: verifying
the journal's selection, or any collection, reports the pins of that paper
as removed, and every other pin as before.

    /-- **A takedown is reported.** -/
    theorem takedown_reported {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl : lookup w a oid = some (.live o)) (p : Pin D) :
        resolve hash (takedown hash w a oid o) p =
          if p.archive = a ∧ p.object = oid then .removed else resolve hash w p := by
      split
      · rename_i h
        exact takedown_removed hash hl h
      · rename_i h
        exact takedown_other hash hl h

The table adds that "an accepted copy is a document of the selection's
archive, to which the takedown is applied separately": a takedown of the
original does not touch it (`acceptedCopy_survives`,
[chapter 6](48-copies.md)).

## The owner decides (overlay journal, learning record)

"Later versions of the accepted copy (corrections, notices, a withdrawal)
are the editors' acts; the authors' archive cannot change them" ("An overlay
journal"). The same holds of an issue, of a student's thesis, of the record
of a piece of work: every object kept in its own archive. In a world built
by acts ([chapter 7](49-acts.md)), its versions were all deposited by the
archive's writers, and an act of anyone else leaves it as it is.

    /-- **The owner decides.** Every version of an object kept in its own archive
    was deposited by a writer of the archive, and nobody else can change it. -/
    theorem owner_controls {w : World D} (h : Acts hash (fun _ => (none : Option (Archive D))) w)
        {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
        (hown : o.archive = a) {ar : Archive D} (ha : w a = some ar) :
        (∀ v ∈ o.versions, v.depositor ∈ ar.writers) ∧
          ∀ u w', u ∉ ar.writers → Act hash u w w' → lookup w' a oid = lookup w a oid :=
      ⟨Acts.own_depositors hash h hl hown ha, fun _ _ hu hact =>
        hact.outsider hash (fun ar' h' => by rw [ha] at h'; cases h'; exact hu) oid⟩

## A mirror is a receipt (learning record)

"When the institution keeps a mirror of the work at each submission, the
mirror is also its receipt" ("A learning record"). The promise: whatever
the student's archive holds later, the versions in the institution's
mirror are the versions of the original, at the same numbers. It holds in
every world built by events, so in every later world too: the student can
add versions, not change those received.

    /-- **A mirror is a receipt.** In a world built by events, every version of a
    mirror is the original's version at the same number. -/
    theorem mirror_receipt {w : World D}
        (hs : Events hash (fun _ => (none : Option (Archive D))) w)
        {b : ArchiveId} {x : ObjectId} {m o : Obj D} (hm : lookup w b x = some (.live m))
        (hb : m.archive ≠ b) (ho : lookup w m.archive m.id = some (.live o))
        {n : Nat} {v : Version D} (hv : m.versionAt n = some v) : o.versionAt n = some v := by
      obtain ⟨_, t, ht⟩ := (Events.mirrorsOk hash hs b x m hm hb).2 o ho
      exact versionAt_prefix (t := []) (by simp) ht (Obj.versionAt_bounds hv).2 hv

Outside the protocol the student's archive can be rewritten (`tamper_detected`,
[chapter 10](65-impossible.md)); the receipt then still shows what was
received, and the pin tells which of the two is the version handed in.

## Retention (learning record)

"When the institution's retention period ends, the record is deleted by a
takedown; its tombstones show that it existed, and the student's own copy
is not affected" ("A learning record"). Two promises: the pins of the
record report `removed` from then on, whatever happens later; and every
other pin that resolved, the student's work among them, resolves as
before, through any later valid steps.

    /-- **Retention.** After a takedown of the record, its pins report `removed`
    forever, and every other pin resolves as before. -/
    theorem record_retention {w : World D} {a : ArchiveId} {oid : ObjectId} {r : Obj D}
        (hl : lookup w a oid = some (.live r)) :
        (∀ p : Pin D, p.archive = a ∧ p.object = oid → ∀ w',
            Events hash (takedown hash w a oid r) w' → resolve hash w' p = .removed) ∧
          (∀ q : Pin D, ¬ (q.archive = a ∧ q.object = oid) → ∀ v, resolve hash w q = .ok v →
            ∀ w', ValidSteps hash (takedown hash w a oid r) w' → resolve hash w' q = .ok v) := by
      refine ⟨fun p hp w' hs => ?_, fun q hq v hv w' hs => ?_⟩
      · obtain ⟨n, d, h⟩ := (resolve_removed_iff hash).mp (takedown_removed hash hl hp)
        exact (resolve_removed_iff hash).mpr ⟨n, d, Events.tomb_stays hash hs h⟩
      · exact Steps.resolve_ok hash (ValidSteps.toSteps hash hs)
          (by rw [takedown_other hash hl hq]; exact hv)

    end OpenSheaf.Patterns
