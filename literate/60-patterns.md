# Use cases as theorems

The [use cases](https://opensheaf.org/use-cases.html) of the specification
describe what authors, archives and selections do, and what they can rely
on. This chapter states some of those promises as theorems about the model,
for every world and every sequence of changes. They play the role of tests:
if a change of the model, or of the specification it follows, broke one of
these promises, the proof would no longer go through. The
[story](70-story.md) of chapter 14 does the same for one concrete world,
checked by computation.

Several promises are about what a reader finds through the hints of a pin,
whichever hint answers. They hold as long as the owners of the lines
pinned sign one history each, and the copies the world holds do not collide
with it (`OneHistory`, [chapter 9](48-copies.md)): the model calls such
owners **honest** in that world, and says it of the owners of a list of
pins with `HonestPins` (the sheaf's `Honest`, over histories of every line,
is another statement). An owner whose keys signed a fork of a line breaks
the promise for that line, and only for it; the fork is then attributable
to whoever held the keys, which then sign no one history of the line
(`Events.fork_signed`).

    -- in OpenSheaf/Patterns.lean:
    import OpenSheaf.Copies

    namespace OpenSheaf.Patterns

    open OpenSheaf

    variable {D : Type} [DecidableEq D] (E : Env D)

## Verifying a collection

A verifier resolves every member of a collection version "as a resolver
does (section 12.3)" (section 14.5), and reports the status of each (section
8.5). The model's verifier resolves every pin of the member list,
`Members.pins` of [chapter 1](10-basic.md), through its hints, and pairs
each pin with its result. It does not check signatures, which valid steps
have checked ([chapter 8](47-acts.md)), nor the document versions of a
selection's revisions, which the model does not record
([model issue 2](https://github.com/opensheaf/opensheaf-lean/issues/2)).

    /-- What a verifier reports for a member list: each pin with its result. -/
    def verify (w : World D) (c : Members D) : List (Pin D × Resolution D) :=
      c.pins.map fun p => (p, resolve E.hash w p)

    /-- Every pin of the member list resolves. -/
    def AllOk (w : World D) (c : Members D) : Prop :=
      ∀ p ∈ c.pins, ∃ v, resolve E.hash w p = .ok v

    /-- The owners of the lines pinned are honest, and no pin names a key log. -/
    def HonestPins (w : World D) (ps : List (Pin D)) : Prop :=
      ∀ p ∈ ps, OneHistory E w p.line ∧ p.line ≠ keyLogLine p.line.owner

A member list whose pins all resolve verifies the same way after any number
of steps, when the owners pinned are honest: this is immutability, pin by
pin, and agreement of copies (`Steps.resolve_ok`, [chapter
9](48-copies.md)). The use cases below rest on it.

    /-- A member list that verified verifies the same after any steps. -/
    theorem verify_stable {w w' : World D}
        (hw' : Events E (fun _ => (none : Option (Archive D))) w') (hs : Steps w w')
        {c : Members D} (hh : HonestPins E w' c.pins) (hok : AllOk E w c) :
        verify E w' c = verify E w c := by
      unfold verify
      apply List.map_congr_left
      intro p hp
      obtain ⟨v, hv⟩ := hok p hp
      rw [Steps.resolve_ok E hw' hs (hh p hp).1 (hh p hp).2 hv, hv]

## A journal issue does not change (overlay journal, review journal)

An overlay journal lists an issue as a selection whose members pin the
revisions the editors vetted ("An overlay journal"). The authors go on
depositing new versions, new lines and archives appear. The promise: an
issue that verified once verifies in exactly the same way after any number
of such changes, and updating it never adds the new versions.

    /-- **A vetted selection is stable.** If every pin of a selection resolves,
    then after any number of steps the verifier reports exactly the same, and
    updating the selection leaves it as it is. -/
    theorem selection_stable {w w' : World D}
        (hw' : Events E (fun _ => (none : Option (Archive D))) w') (hs : Steps w w')
        {c : Members D} (hsel : c.type = .selection) (hh : HonestPins E w' c.pins) (hok : AllOk E w c) :
        verify E w' c = verify E w c ∧ collect E.hash w' c = c :=
      ⟨verify_stable E hw' hs hh hok, collect_selection E.hash w' hsel⟩

Without honesty, the promise holds at each hint: a pin that resolved to a
version at an archive resolves to it there after any steps, whoever
signed what (`Steps.resolveAt_ok`, [chapter 3](30-archive.md)). The same
holds of a review journal's selection of reviewed papers, of the record of
a peer review, and of a learning record: the property is about selections,
not about who keeps them.

## A digest of digests, a volume of issues

A selection may contain collections ("A digest, a reading list"): a volume
pins its issues, each pinned in the version published. A reader who follows
the volume's pin to an issue, then the issue's pins to the papers, should
find the same papers forever. Pins to collection versions carry their
member lists with them, so this is immutability twice.

    /-- **Nested pins are stable.** If a pin resolves to a collection version whose
    pins all resolve, then after any number of steps it resolves to the same
    version, and the member list read through it verifies as before. -/
    theorem nested_stable {w w' : World D}
        (hw' : Events E (fun _ => (none : Option (Archive D))) w') (hs : Steps w w')
        {q : Pin D} {cv : Version D} (hq : resolve E.hash w q = .ok cv) (hhq : HonestPins E w' [q])
        (hok : ∀ c, cv.members = some c → HonestPins E w' c.pins ∧ AllOk E w c) :
        resolve E.hash w' q = .ok cv ∧
          ∀ c, cv.members = some c → verify E w' c = verify E w c := by
      have := hhq q (List.mem_singleton_self _)
      exact ⟨Steps.resolve_ok E hw' hs this.1 this.2 hq,
        fun c hc => verify_stable E hw' hs (hok c hc).1 (hok c hc).2⟩

## A co-author follows a paper (catalogues)

A co-author lists a joint paper in a catalogue with `follow` ("Co-authors in
different archives"). The promise: after the authors deposit a new version,
updating the catalogue pins it. First, the head of a line, at the first of
its hints, after a deposit there is the version deposited.

    /-- After a deposit at the first hint, the head of the line resolves there to
    the version deposited. -/
    theorem head_after_deposit {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
        {o : Obj D} (x : Version D) (ss : List (Sig D)) (ha : w a = some ar)
        (rest : List ArchiveId) :
        ∃ p, headPin E.hash (setEntry w a (.line l) (.live (o.append x ss))) (a :: rest) l = some p ∧
          resolveAt E.hash (setEntry w a (.line l) (.live (o.append x ss))) a p = .ok x := by
      have hl : lookup (setEntry w a (.line l) (.live (o.append x ss))) a (.line l) =
          some (.live (o.append x ss)) := by
        rw [lookup_setEntry ha]; simp
      have hp : headPin E.hash (setEntry w a (.line l) (.live (o.append x ss))) (a :: rest) l =
          some ⟨l, (o.append x ss).versions.length,
            E.hash ((o.append x ss).inventory (o.append x ss).versions.length), a :: rest⟩ := by
        unfold headPin headIn; rw [hl]; simp [Obj.append]
      refine ⟨_, hp, ?_⟩
      unfold resolveAt
      rw [hl]
      apply resolveEntry_live_of
      · simp [Obj.versionAt, Obj.append]
      · rfl

The statement needs no hypothesis on what the archive kept under the line
before: the head after a deposit is the version deposited, whatever was
there.

Then the update of the catalogue: the member following the paper gets that
pin.

    /-- **A followed paper is pinned at its new version.** After the owner deposits
    `x` at the first hint of a member that follows the paper, updating the
    catalogue gives the member a pin that resolves there to `x`. -/
    theorem follow_after_deposit {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
        {o : Obj D} (x : Version D) (ss : List (Sig D)) (ha : w a = some ar)
        {c : Members D} (hcat : c.type = .catalogue)
        {m : Member D} (hm : m ∈ c.members) (hf : m.follow = true)
        {rest : List ArchiveId} (hma : m.hints = a :: rest) (hml : m.line = l) :
        ∃ p, { m with pins := [p] } ∈
            (collect E.hash (setEntry w a (.line l) (.live (o.append x ss))) c).members ∧
          resolveAt E.hash (setEntry w a (.line l) (.live (o.append x ss))) a p = .ok x := by
      obtain ⟨p, hp, hr⟩ := head_after_deposit E (o := o) (l := l) x ss ha rest
      refine ⟨p, collect_follow E.hash _ hcat hm hf ?_, hr⟩
      rw [hma, hml]; exact hp

Together with `selection_stable`, this is the difference between the two
types of collection, in the case where it matters: the same deposit moves
the catalogue and leaves the selection where it was.

## A correction of the description (description-only versions)

The authors correct a typo in the title of a document version, the current
one or an earlier one ("A researcher's own archive"). The promise: the
correction is a new object version, so it is recorded and pinnable, but not
a new document version, so citations of the document version stay right;
and the history stays well formed.

    /-- **A description-only version is not a new document version.** -/
    theorem correction_same_document_version {o : Obj D} (hwf : WellFormed o.versions)
        {v : Version D} (hv : v ∈ o.versions) (d a m : String) (ss : List (Sig D)) :
        WellFormed (o.append (Version.describe o.versions v d a m) ss).versions ∧
          (Version.describe o.versions v d a m).documentVersion = v.documentVersion :=
      ⟨WellFormed.snoc hwf (describe_extends hv d a m), rfl⟩

## A withdrawal does not erase what was vetted (section 13.1)

The authors withdraw a paper that a journal has vetted. The promise: the
withdrawal is a new version with status `withdrawn`; the pin of the vetted
revision still resolves to it, exactly as it was vetted. "A withdrawn line
keeps every version, signed, pinned and copied as before" (section 13.1);
presentations show the two together.

    /-- **Withdrawal keeps the vetted revision.** -/
    theorem withdrawal_keeps_vetted {w : World D} {a : ArchiveId} {ar : Archive D}
        {oid : ObjectId} {o : Obj D} (ha : w a = some ar) (ho : ar.entries oid = some (.live o))
        (hne : o.versions ≠ []) (dep msg : String) (ss : List (Sig D)) {b : ArchiveId}
        {p : Pin D} {v : Version D} (hp : resolveAt E.hash w b p = .ok v) :
        let x := (o.versions.getLast hne).withdraw dep msg
        resolveAt E.hash (setEntry w a oid (.live (o.append x ss))) b p = .ok v ∧
          x.status = .withdrawn :=
      ⟨Step.resolveAt_ok E.hash (Step.append w a ar oid o _ ss ha ho) hp, rfl⟩

The first half holds of any version appended, not only of a withdrawal (it
is immutability); only the status is specific. That the withdrawal is a
version the owner may add is [chapter 2](20-object.md)'s `withdraw_extends`
and `withdraw_noReinstatement`.

The table "What happens when ..." of the use cases describes a withdrawal
in both columns at once: a catalogue follows it, and pins the withdrawn
head; a selection does not move, and its vetted revisions resolve as
before, at the hints where they resolved. One deposit, both columns:

    /-- **A withdrawal, in both columns.** A catalogue following the paper pins
    the withdrawal; every pin of a selection that resolved at a hint resolves there
    as before, and the selection does not move. -/
    theorem withdrawal_both_columns {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
        {o : Obj D} (ha : w a = some ar) (ho : ar.entries (.line l) = some (.live o))
        (hne : o.versions ≠ []) (dep msg : String) (ss : List (Sig D))
        {c : Members D} (hcat : c.type = .catalogue) {m : Member D} (hm : m ∈ c.members)
        (hf : m.follow = true) {rest : List ArchiveId} (hma : m.hints = a :: rest)
        (hml : m.line = l) {s : Members D} (hsel : s.type = .selection) :
        let x := (o.versions.getLast hne).withdraw dep msg
        let w' := setEntry w a (.line l) (.live (o.append x ss))
        (∃ p, { m with pins := [p] } ∈ (collect E.hash w' c).members ∧
            resolveAt E.hash w' a p = .ok x ∧ x.status = .withdrawn) ∧
          (∀ p ∈ s.pins, ∀ b v, resolveAt E.hash w b p = .ok v → resolveAt E.hash w' b p = .ok v) ∧
          collect E.hash w' s = s := by
      intro x w'
      obtain ⟨p, hp, hr⟩ := follow_after_deposit E (o := o) x ss ha hcat hm hf hma hml
      exact ⟨⟨p, hp, hr, rfl⟩,
        fun _ _ _ _ h => Step.resolveAt_ok E.hash (Step.append w a ar _ o x ss ha ho) h,
        collect_selection E.hash w' hsel⟩

## Nobody else adds to a member (sections 7.5 and 15.1)

When "another archive adds a version to a member's line", the table
answers: "it is not the owner's: it is not signed, so verifiers report it
as not a version, and the collection does not follow it". In the model, a version that
is not signed by the owner never enters a world built by events: whatever
copy of the member a reader finds, its head is signed with a current key of
the member's owner's key log as the world holds it, and vouches for every
version before it (`Events.headsSigned`, [chapter
8](47-acts.md)).

    /-- **Only the owner adds to a member.** Every copy of a member, wherever it is
    kept, ends in a version signed with a current key of the owner's key log as
    the world holds it. -/
    theorem member_signed {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {m : Member D}
        (hnk : m.line ≠ keyLogLine m.line.owner) {b : ArchiveId} {o : Obj D}
        (hl : lookup w b (.line m.line) = some (.live o)) : HeadSigned E w m.line o :=
      Events.headsSigned E hs hl fun hk => hnk (Events.keyLog_line E hs hl hk)

## The member's archive disappears

"Members are fetched from mirrors, or any copy matching the pin" (the
table): when the archives listed first in a member's `at` give no version,
a copy at a later location gives it, and it is the version pinned, unless
inventories collide (`resolve_stand_in`, `resolve_sound`, [chapter
9](48-copies.md)). An accepted copy is another line, which a takedown of
the parent does not reach (`acceptedCopy_survives`).

## A takedown is reported, not hidden (sections 13.2, 14.5)

A paper vetted by a journal is taken down, by law. The promise: at the
archive that took it down, every pin of the paper reports `removed`, and
everything else resolves as before; copies kept elsewhere are not reached
("open, #33", the table).

    /-- **A takedown is reported.** -/
    theorem takedown_reported {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl : lookup w a oid = some (.live o)) (b : ArchiveId) (p : Pin D) :
        resolveAt E.hash (takedown E.hash w a oid o) b p =
          if b = a ∧ ObjectId.line p.line = oid then .removed else resolveAt E.hash w b p := by
      split
      · rename_i h
        obtain ⟨rfl, h⟩ := h
        exact takedown_removed E.hash hl h
      · rename_i h
        exact takedown_other E.hash hl h

## The owner decides (overlay journal, learning record)

Later versions of the accepted copy (corrections, notices, a withdrawal)
"are the editors' acts, signed by the journal; the authors cannot change
them" ("An overlay journal"). The same holds of an issue, of a student's thesis, of
the record of a piece of work: every line. In a world built by events,
every copy of a line ends in a version its owner signed; and a valid step
that adds to a line, anywhere, adds a version its owner signed.

    /-- **The owner decides.** A valid step that writes a copy of a line, which is
    not a key log, writes one whose head the line's owner signed. -/
    theorem owner_decides {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
        {o' : Obj D} (hauth : Authorised E w a ar (.line l) o') (hk : o'.kind ≠ .owner) :
        HeadSigned E w l o' :=
      (authorised_ownersSign E hauth).1 hk

## A mirror is a receipt (learning record)

"When the institution keeps a mirror of the work at each submission ...,
the mirror is also its receipt" ("A learning record"). The promise: whatever the
student's archive holds later, the versions in the institution's mirror
are the versions of the student's line, at the same numbers, as long as the
student signs one history. If the student's keys sign another history, the
two copies fork, and the receipt shows what was received, with the
student's signature (`Events.fork_signed`).

    /-- **A mirror is a receipt.** In a world built by events, a version of any
    copy of a line is the version of every other copy at the same number, when
    the owner signs one history. -/
    theorem mirror_receipt {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {l : LineId}
        (h1 : OneHistory E w l) (hnk : l ≠ keyLogLine l.owner)
        {b b' : ArchiveId} {m o : Obj D} (hm : lookup w b (.line l) = some (.live m))
        (ho : lookup w b' (.line l) = some (.live o))
        {n : Nat} {v u : Version D} (hv : m.versionAt n = some v) (hu : o.versionAt n = some u) :
        u = v :=
      ((Events.copiesAgree E hs h1 b b' m o hm ho (fun hk => hnk (Events.keyLog_line E hs hm hk))
        (fun hk => hnk (Events.keyLog_line E hs ho hk))).versionAt hv hu).symm

## Retention (learning record)

"When the institution's retention period ends, the record is deleted by a
takedown ...; its tombstones show that it existed, and the student's own copy
is not affected" ("A learning record"). Two promises: at the institution's
archive, the pins of the record report `removed` from then on, whatever
happens later; and every other pin that resolved at an archive, the
student's work among them, resolves there as before, through any later
valid steps.

    /-- **Retention.** After a takedown of the record, its pins report `removed`
    there forever, and every other pin resolves as before. -/
    theorem record_retention {w : World D} {a : ArchiveId} {oid : ObjectId} {r : Obj D}
        (hl : lookup w a oid = some (.live r)) :
        (∀ p : Pin D, ObjectId.line p.line = oid → ∀ w',
            Events E (takedown E.hash w a oid r) w' → resolveAt E.hash w' a p = .removed) ∧
          (∀ b (q : Pin D), ¬ (b = a ∧ ObjectId.line q.line = oid) → ∀ v,
            resolveAt E.hash w b q = .ok v →
            ∀ w', ValidSteps E (takedown E.hash w a oid r) w' → resolveAt E.hash w' b q = .ok v) := by
      refine ⟨fun p hp w' hs => ?_, fun b q hq v hv w' hs => ?_⟩
      · obtain ⟨n, d, h⟩ := (resolveAt_removed_iff E.hash).mp (takedown_removed E.hash hl hp)
        exact (resolveAt_removed_iff E.hash).mpr ⟨n, d, Events.tomb_stays E hs h⟩
      · exact Steps.resolveAt_ok E.hash (ValidSteps.toSteps E hs)
          (by rw [takedown_other E.hash hl hq]; exact hv)

    end OpenSheaf.Patterns
