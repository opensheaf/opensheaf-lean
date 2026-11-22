# Well-formed worlds

The steps of [chapter 3](30-archive.md) accept anything: an object with no
version, a version whose document version jumps from 2 to 5, a collection
version without a member list, a pin of a version that does not exist, a
version that nobody signed. Immutability holds all the same, and it is
worth knowing that it does not depend on good behaviour. But the
specification asks for more, and this chapter says what: it defines
**valid steps**, which check what the specification requires of each new
object and object version, and proves that they keep the archives **well
formed**:

- every object is stored under its own identifier, has at least one
  version, and, unless it is a key log, a well-formed history of document
  versions ([chapter 2](20-object.md)); a draft has no genesis record, a
  line has one;
- the versions of a collection, and only those, have member lists
  (section 8.2), and these lists obey the rules of section 8
  ([chapter 6](40-collection.md));
- every pin held by any version is found at one of its hints, so that,
  without takedowns, nothing ever dangles.

The checks on signatures, on key logs, on copies and on branches are part
of the valid steps too; what they guarantee is proved in the next two
chapters.

Valid steps check the last condition on every pin they write: it is found,
or reports `removed`. This is a **modelling choice**, stronger than the
specification. Section 8.5 asks that every member be pinned, not that
every pin resolve when it is made: section 14 reports members as
"unavailable", and issue #29 discusses pins of objects that readers cannot
reach. The model asks that a tool resolve every pin it writes, as the
reference tools do. A pin that reports `removed` is accepted only when it
is carried over, held already by a version of the world: after a takedown,
a collection keeps the pins of the line taken down in its later versions (a
withdrawal, a description, an update), and a mirror copies them. A pin made
afresh into a line taken down is refused. The freedom from cycles of
[chapter 12](65-impossible.md) rests on the first half of this choice.

The chapter also proves two facts about all steps, valid or not: an
identifier taken down is never reused, and an object only grows, so that
every earlier version of a collection, with its member list, is kept.
Finally it adds takedowns to the valid steps, as **events**, and proves
what remains true: every pin held is found, or reports `removed`, and
tombstones stay.

    -- in OpenSheaf/Worlds.lean:
    import OpenSheaf.Collection
    import OpenSheaf.Lines

    namespace OpenSheaf

    variable {D : Type} [DecidableEq D] (E : Env D)

## Well-formed objects and worlds

    /-- The member list of a version, if any, is well formed. -/
    def Version.membersOk (v : Version D) : Prop :=
      match v.members with
      | none => True
      | some c => c.WF

    instance (v : Version D) : Decidable v.membersOk := by
      unfold Version.membersOk; split <;> infer_instance

    /-- The identifier names a line, not a draft. -/
    def ObjectId.isLine : ObjectId → Bool
      | .line _ => true
      | .draft _ => false

The history of a key log has no document versions (section 4.1): its
versions are checked by [chapter 4](35-owners.md) instead. A branch numbers
its document versions from 1, like any line, and keeps the branch point's
own number in `parent.documentVersion`, as section 9.4 says since
[issue #57](https://github.com/opensheaf/opensheaf.github.io/issues/57)
was decided ("a branch numbers its own document versions, from 1 without
gaps, as every line does"); the model had made this choice before. It
keeps the counting of chapter 2, and its theorems, the same for every
line.

    /-- A well-formed object stored under `oid` (sections 4, 4.2, 8.2 and 10.1). -/
    structure Obj.WF (o : Obj D) (oid : ObjectId) : Prop where
      id : o.id = oid
      nonempty : o.versions ≠ []
      history : o.kind ≠ .owner → WellFormed o.versions
      kinds : ∀ v ∈ o.versions, v.members.isSome = true ↔ o.kind = .collection
      members : ∀ v ∈ o.versions, v.membersOk
      statuses : StatusOk o.versions
      genesis : o.genesis.isSome = oid.isLine

A pin held by a version is found, or reports `removed`, at one of its
hints:

    /-- At one of its hints, the pin's line has been taken down. -/
    def RemovedAt (w : World D) (p : Pin D) : Prop :=
      ∃ b ∈ p.hints, resolveAt E.hash w b p = .removed

    /-- The pin is found, or reports `removed`, at one of its hints. -/
    abbrev Held (w : World D) (p : Pin D) : Prop :=
      Found E.hash w p ∨ RemovedAt E w p

    /-- Every pin held by a version of a live object is found. -/
    def PinsOk (w : World D) : Prop :=
      ∀ a oid o, lookup w a oid = some (.live o) →
        ∀ v ∈ o.versions, ∀ p ∈ v.pins, Found E.hash w p

    /-- No object has been taken down. -/
    def NoTombs (w : World D) : Prop := ∀ a oid n d, lookup w a oid ≠ some (.tomb n d)

A world is well formed when its objects are, its pins are found, and,
since it is built without takedowns, it holds no tombstone.

    /-- A well-formed world. -/
    def WFWorld (w : World D) : Prop :=
      (∀ a oid o, lookup w a oid = some (.live o) → o.WF oid) ∧ PinsOk E w ∧ NoTombs w

The empty world, with no archive, is well formed.

    theorem WFWorld.empty : WFWorld E (fun _ => (none : Option (Archive D))) :=
      ⟨fun _ _ _ h => by simp [lookup] at h, fun _ _ _ h => by simp [lookup] at h,
        fun _ _ _ _ h => by simp [lookup] at h⟩

## Copies

A copy of a line is "its object as held in one storage root" (section 11).
An archive may make a copy of a line written elsewhere, "the object's
versions up to the latest signed version of the copy it copies", and a
mirror "MUST NOT be changed except by adding the owner's signed versions
as section 7.5 allows, from a copy that agrees with it" (section 11.1). One
predicate says it for both: the new state of the object is a prefix of
another live copy of the same line, kept by another archive, with the same
genesis record. Signature files need not all be copied.

The model accepts a copy of any prefix, where section 11.1 asks for the
whole of the copy copied up to its latest signed version; whether a copy
may stop at a pinned version is
[issue #39](https://github.com/opensheaf/opensheaf.github.io/issues/39)
([model issue 6](https://github.com/opensheaf/opensheaf-lean/issues/6)).

    /-- `o` is a copy of a prefix of a live copy of the same line, kept by another
    archive (section 11.1). -/
    def CopyOf (w : World D) (a : ArchiveId) (o : Obj D) : Prop :=
      ∃ b c, b ≠ a ∧ lookup w b o.id = some (.live c) ∧ c.genesis = o.genesis ∧
        ∃ t, c.versions = o.versions ++ t

## Signatures and identity

A new version of a line is added "only if, once added, it is signed and not
contested (section 7.3) against the key log the archive holds: signed
directly by its owner, or vouched for by a version signed directly that is
added with it from the same copy" (section 7.5). The model checks the head
of the new state of the object: it is signed directly, without tainted
signatures, against the copy of the owner's key log that the archive
keeps, which is valid and not frozen by a fork (section 7.5); and it vouches
for the versions before it. A step adds one version at a time, so the
version it adds must itself be signed directly: a version that only a later
version vouches for can be added only by creating the copy with both, which
a mirror that exists already cannot do. This is a **modelling
restriction**: section 7.5 lets the two be added together. Besides:

- the archive hosts the owner, and the owner has not ended, or the
  versions come from a copy: a mirror grows only by copying (section 11.1),
  and "for an owner whose key log has an ending version ..., an archive
  takes versions of its other lines only from copies found elsewhere,
  never as new deposits" (section 7.5);
- a key log is valid ([chapter 4](35-owners.md)); it may be kept and grown
  in any archive, since it "checks itself from its owner name" (section
  6.5);
- drafts are never signed (section 10.1), and need no signature.

Every signature file an archive adds must be valid (`SigOk`, below),
whether it comes with a new object or version or later, as section 7.1
allows ("an owner MAY add signatures to a version later"). Whether the
owner knows it made the version, and is not ended, is the owner tool's
affair, not the archive's.

    /-- The new state `o` of the copy of the line `l` (not a key log) kept by
    archive `a` is signed and allowed there (sections 7.5 and 11.1). -/
    def LineOk (w : World D) (a : ArchiveId) (ar : Archive D) (l : LineId) (o : Obj D) : Prop :=
      ∃ kl, lookup w a (.line (keyLogLine l.owner)) = some (.live kl) ∧ KeyLogOk E l.owner kl ∧
        ¬ Frozen kl ∧ SignedClean E kl l o o.versions.length ∧
        ((l.owner ∈ ar.owners ∧ ¬ HasEnding kl) ∨ CopyOf w a o)

The identity of a line (sections 5 and 9.1): its genesis record is of the
object's kind; a key log has the owner name as name and is valid; the
originator's line is named by algorithm 0 and has no parent; every other
line of the genesis record is a branch, named by one of the 16 names of the
record, of another owner, and every version declares its parent, of a line
of the same record and another owner. The model does not check which
algorithm a branch takes after a clash (section 5.3), nor the rule on
reused genesis records (section 5.4).

    /-- The identity of the line `l`, whose object is `o` (sections 5, 6 and 9.1). -/
    def IdentityOk (l : LineId) (o : Obj D) : Prop :=
      match o.genesis with
      | none => False
      | some g =>
        g.kind = o.kind ∧
        if o.kind = .owner then l = keyLogLine l.owner ∧ KeyLogOk E l.owner o
        else
          (l.owner = g.originator ∧ l.name = E.nameOf g 0 ∧ ∀ v ∈ o.versions, v.parent = none) ∨
          (l.owner ≠ g.originator ∧ (∃ k, k < 16 ∧ l.name = E.nameOf g k) ∧
            ∀ v ∈ o.versions, ∃ pa, v.parent = some pa ∧ pa.pin.line.owner ≠ l.owner ∧
              ∃ k, k < 16 ∧ pa.pin.line.name = E.nameOf g k)

A draft "is a `document` or a `collection`", has no `parent`, and "is never
signed" (section 10.1).

    /-- A draft has no signature files, is not an owner, and has no parent
    (section 10.1). -/
    def DraftOk (o : Obj D) : Prop :=
      o.sigs = [] ∧ o.kind ≠ .owner ∧ ∀ v ∈ o.versions, v.parent = none

What a step that writes `o` under `oid` in archive `a` must show: for a
draft, that it is one; for a line, its identity, and its signatures as
above.

    /-- The object `o`, written under `oid` by archive `a`, is authorised. -/
    def Authorised (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D) :
        Prop :=
      match oid with
      | .draft _ => DraftOk o
      | .line l => IdentityOk E l o ∧ (o.kind ≠ .owner → LineOk E w a ar l o)

## Branch points

A branch holds its branch point, and "the first object version of a branch
holds exactly the files of the parent version" (section 9.2), as does every
version that takes a new branch point (section 9.4), which in the
specification also keeps the files of the branch's own notices; the model
has no notices, and every file counts. A new branch point is only "a
later version of the same parent line ...: with the same `owner`
and `name`, a higher object version, and a document version later than the
previous branch point's" ("a parent version holding the same document
version (a DOI added) is not a new branch point"), and the new parent
version must continue the previous one: the model compares document
versions by number (it has no `history`), and checks continuity by asking
the copy that resolves the new pin to resolve the previous one too, which
says that the new parent inventory extends the previous one. The model
checks this against the parent version, found at a hint of the pin
(the evidence of section 9.2, which would let a verifier check without it,
is left out): the files are compared as lists, path, digest and order, and
the document version held is the one `parent` records. A branch is made
from a parent version at hand; a copy of a branch is not checked again
(the check was made when the branch was), so that a branch whose parent
has since been taken down can still be mirrored. A
version that keeps the branch point of the version before keeps the same
parent version and document version (`Parent.Keeps`, [chapter
1](10-basic.md)); it may change the hints of the pin (`parent.url`) and the
evidence, which are not part of the branch point, and its files may differ
(the branch's own notes, a version of record).

    /-- The branch point of `x`, after a version whose branch point is `prev`
    (sections 9.1 to 9.4). -/
    def BranchPointOk (w : World D) (prev : Option (Parent D)) (x : Version D) : Prop :=
      match x.parent with
      | none => prev = none
      | some pa =>
        Parent.Keeps prev pa ∨
        ((∀ pp, prev = some pp → pp.pin.line = pa.pin.line ∧ pp.pin.version < pa.pin.version ∧
            pp.documentVersion < pa.documentVersion) ∧
          ∃ b ∈ pa.pin.hints, ∃ u, resolveAt E.hash w b pa.pin = .ok u ∧
            x.files = u.files ∧ u.documentVersion = pa.documentVersion ∧
            ∀ pp, prev = some pp → ∃ u0, resolveAt E.hash w b pp.pin = .ok u0)

    /-- The branch point of the version before version `i` of a history. -/
    def prevParent (l : List (Version D)) (i : Nat) : Option (Parent D) :=
      match i with
      | 0 => none
      | j + 1 => (l[j]?).bind (·.parent)

A version made by `Version.revise` or `Version.describe`
([chapter 2](20-object.md)) records the branch point of the head of the
history it extends, so it keeps it: the owner of a branch revises it, or
describes an earlier document version of it, without checking its branch
point again.

    theorem revise_branchPoint (w : World D) (l : List (Version D)) (fs : List (LogicalPath × D))
        (ms : Option (Members D)) (d a m : String) :
        BranchPointOk E w (headParent l) (Version.revise l fs ms d a m) := by
      unfold BranchPointOk
      cases h : headParent l with
      | none => simp [Version.revise, h]
      | some pa => simp only [Version.revise, h]; exact Or.inl (Parent.same_refl pa)

    theorem describe_branchPoint (w : World D) (l : List (Version D)) (v : Version D)
        (d a m : String) : BranchPointOk E w (headParent l) (Version.describe l v d a m) := by
      unfold BranchPointOk
      cases h : headParent l with
      | none => simp [Version.describe, h]
      | some pa => simp only [Version.describe, h]; exact Or.inl (Parent.same_refl pa)

## Pins and followed members

A new version may hold a pin that reports `removed`, but only one that the
world already holds: a description-only version of a collection after one
of its members was taken down keeps that member's pin. A pin made afresh
must be found. Without this rule a step could write a pin, with any number
and any digest, into a line taken down, which no verifier could ever
check.

A pin is carried over when some version of the world holds a pin that
names the same object version (`Pin.names`, [chapter 1](10-basic.md)): its
hints may differ, since a collection may change where it looks for a member
without changing what it pins.

    /-- Some version of a live object of the world holds a pin naming the same
    object version. -/
    def HeldBy (w : World D) (p : Pin D) : Prop :=
      ∃ b i c v q, lookup w b i = some (.live c) ∧ v ∈ c.versions ∧ q ∈ v.pins ∧ q.names p

A pin never names a key log: the versions of a key log are named only by
the `keyLog` of signature files (section 7.2), which are not pins held by
versions; members are documents and collections (section 8.2), and an
owner object "is never withdrawn or branched" (section 4.1). The model
checks it on every pin written, as the line of a key log, `(X, X)`
([chapter 4](35-owners.md)).

    /-- A pin a new version may hold: it names no key log, and it is found, or it
    reports `removed` and is carried over from a version the world already holds. -/
    def PinOk (w : World D) (p : Pin D) : Prop :=
      p.line ≠ keyLogLine p.line.owner ∧ (Found E.hash w p ∨ (RemovedAt E w p ∧ HeldBy w p))

    theorem PinOk.held {w : World D} {p : Pin D} (h : PinOk E w p) : Held E w p :=
      h.2.elim Or.inl fun h => Or.inr h.1

A pin held after an entry is set was held before, unless the new entry
holds it; a new, empty archive holds none. With it, one shows that a world
does not hold a pin by walking back through the steps that built it
(chapter [A story](70-story.md)).

    omit [DecidableEq D] in
    theorem heldBy_setEntry {w : World D} {a : ArchiveId} {oid : ObjectId} {e : Entry D}
        {p : Pin D} (h : HeldBy (setEntry w a oid e) p)
        (he : ∀ c, e = .live c → ∀ v ∈ c.versions, ∀ q ∈ v.pins, ¬ q.names p) : HeldBy w p := by
      obtain ⟨b, i, c, v, q, hl, hv, hq, hn⟩ := h
      cases ha : w a with
      | none =>
        have : setEntry w a oid e = w := by
          funext b'; unfold setEntry; by_cases hb : b' = a <;> simp [hb, ha]
        rw [this] at hl; exact ⟨b, i, c, v, q, hl, hv, hq, hn⟩
      | some ar =>
        rw [lookup_setEntry ha] at hl
        by_cases hbi : b = a ∧ i = oid
        · simp only [hbi, and_self, ite_true, Option.some.injEq] at hl
          exact absurd hn (he c hl v hv q hq)
        · simp only [hbi, ite_false] at hl
          exact ⟨b, i, c, v, q, hl, hv, hq, hn⟩

    omit [DecidableEq D] in
    theorem heldBy_newArchive {w : World D} {a : ArchiveId} {ar : Archive D} (h : w a = none)
        (hempty : ∀ x, ar.entries x = none) {p : Pin D}
        (hb : HeldBy (fun b => if b = a then some ar else w b) p) : HeldBy w p := by
      unfold HeldBy at hb ⊢
      simp only [lookup_newArchive h hempty] at hb
      exact hb

The check on followed members: "a followed member pins the latest signed
version of its line ... when the document version of the collection that
holds it was made; a description-only version of the collection keeps the
member list of the document version it holds" (section 8.3).
A tool "follows only a signed version that extends the version pinned; a
copy that does not is a fork of the line (section 7.4), which it reports,
keeping the pin". The model's tool takes the head of the first copy found
at the member's hints ([chapter 6](40-collection.md)), and pins it, or
keeps the member's single pin when that head is no later than it, or when
no copy at the hints holds both (the head does not extend the pin: a fork,
or a stale copy). A member whose line has no head at its hints keeps its
pin, as `collect` does. The model does not ask the head to be uncontested:
a head that has become contested since it was added (section 7.3) is
followed, where section 8.3 says not to; telling it needs the key log of
the archive holding the head, which the check does not consult. The check
applies to the new document versions an owner makes of its catalogue, not
to its description-only versions, nor to copies, which copy versions made
earlier. An earlier version of the model checked every version, and so a
catalogue whose followed member had moved could get no description-only
version, nor a withdrawal: the new version would have had to pin the new
head, which changes its member list, its content. The model raised this as
[issue #45](https://github.com/opensheaf/opensheaf.github.io/issues/45),
which the specification settled this way. For a line created whole, the
check applies to its last version, as before.

    /-- The result is a version. -/
    def Resolution.isOk : Resolution D → Bool
      | .ok _ => true
      | _ => false

    /-- The member's single pin may be kept although `p` is the head: `p` is no
    later, or no copy at the hints holds both. -/
    def Member.MayKeep (w : World D) (m : Member D) (p : Pin D) : Prop :=
      match m.pins with
      | [q] => p.version ≤ q.version ∨
          ¬ ∃ b ∈ m.hints, (resolveAt E.hash w b q).isOk = true ∧ (resolveAt E.hash w b p).isOk = true
      | _ => False

    /-- A followed member pins the head of its line at its hints, if any, or keeps
    its pin when the head does not extend it. -/
    def Member.FollowsHead (w : World D) (m : Member D) : Prop :=
      match headPin E.hash w m.hints m.line with
      | some p => m.pins = [p] ∨ m.MayKeep E w p
      | none => True

    instance (w : World D) (m : Member D) (p : Pin D) : Decidable (m.MayKeep E w p) := by
      unfold Member.MayKeep; split <;> infer_instance

    instance (w : World D) (m : Member D) : Decidable (m.FollowsHead E w) := by
      unfold Member.FollowsHead; split <;> infer_instance

    /-- In a catalogue version, the followed members pin the heads of their lines
    (section 8.3). -/
    def Version.FollowsHeads (w : World D) (v : Version D) : Prop :=
      match v.members with
      | some c => c.type = .catalogue → ∀ m ∈ c.members, m.follow = true → m.FollowsHead E w
      | none => True

    instance (w : World D) (v : Version D) : Decidable (v.FollowsHeads E w) := by
      unfold Version.FollowsHeads; split <;> infer_instance

    /-- The last version of a history, if any, follows heads. -/
    def HeadFollows (w : World D) (l : List (Version D)) : Prop :=
      match l.getLast? with
      | some x => x.FollowsHeads E w
      | none => True

    instance (w : World D) (l : List (Version D)) : Decidable (HeadFollows E w l) := by
      unfold HeadFollows; split <;> infer_instance

## Valid steps

A valid step is a step with the checks of the specification:

- a new archive is empty;
- a new object is well formed, its pins are found, or report `removed` and
  are carried over, at the time it is created, so that it pins only
  versions that already exist; its branch points hold their parents'
  files; it is authorised, as above;
- a new object version extends the history (section 4.2), unless it is a
  version of a key log; changes the status only as section 13.1 says (a
  new document version is active, any other version of a withdrawn line
  withdrawn, [chapter 2](20-object.md)); has a member list
  exactly if the object is a collection, and then a well-formed one; pins
  only versions that are found, or report `removed` and are carried over;
  keeps its branch point or takes a new one as section 9.4 says; and leaves the
  object authorised;
- in a new document version that an owner makes of its catalogue (not a
  copy, nor a description-only version), every member with `follow` pins
  the head of its line;
- new witnesses verify, and sign versions of the object.

Every signature file an archive adds, with a new object, with a new
version, or later as a witness, must be valid: "an archive adds no invalid
signature file" (section 7.5). The model checks what section 7.3 checks of
a signature file that a reader can judge: it verifies; it signs a version
of the object, with the digest of its inventory; it names a version of the
signer's key log, its owner's for a line, the version before for a key
log; and its key is one that version allows, a current key, or for a key
log a rotation key (section 6.1), as the archive's copy of the key log
reaches it. The computed first version of a key log is never signed.

    /-- The key of `s` is a rotation key of the version of the key log `o` before the
    one it signs (section 6.1). -/
    def RotationKeyOk (o : Obj D) (s : Sig D) : Prop :=
      match keysAt o (s.version - 1) with
      | some pk => E.keyDigest s.key ∈ pk.next
      | none => False

    instance (o : Obj D) (s : Sig D) : Decidable (RotationKeyOk E o s) := by
      unfold RotationKeyOk; split <;> infer_instance

    /-- The key of `s` is a current key of the key-log version it names, in the copy
    of its owner's key log that archive `a` keeps (sections 7.2 and 7.3). -/
    def CurrentKeyOk (w : World D) (a : ArchiveId) (s : Sig D) : Prop :=
      match lookup w a (.line (keyLogLine s.line.owner)) with
      | some (.live kl) => ∃ kv ∈ (keyVersion E kl s.keyLog).toList, s.key ∈ kv.keys
      | _ => False

    instance (w : World D) (a : ArchiveId) (s : Sig D) : Decidable (CurrentKeyOk E w a s) := by
      unfold CurrentKeyOk; split <;> infer_instance

    /-- The key-log version named by `s`, a signature file of the object `o` kept by
    archive `a`, allows its key (sections 6.1, 7.2 and 7.3). -/
    def WitnessKeyOk (w : World D) (a : ArchiveId) (o : Obj D) (s : Sig D) : Prop :=
      if o.kind = .owner then
        2 ≤ s.version ∧ s.keyLog.line = s.line ∧ s.keyLog.version = s.version - 1 ∧
          s.keyLog.digest = E.hash (o.inventory (s.version - 1)) ∧ RotationKeyOk E o s
      else
        s.keyLog.line = keyLogLine s.line.owner ∧ CurrentKeyOk E w a s

    instance (w : World D) (a : ArchiveId) (o : Obj D) (s : Sig D) :
        Decidable (WitnessKeyOk E w a o s) := by
      unfold WitnessKeyOk; infer_instance

    /-- The signature file `s` of the object `o`, added by archive `a`, is valid. -/
    def SigOk (w : World D) (a : ArchiveId) (o : Obj D) (s : Sig D) : Prop :=
      E.verifies s = true ∧ o.id = .line s.line ∧ 1 ≤ s.version ∧ s.version ≤ o.versions.length ∧
        s.digest = E.hash (o.inventory s.version) ∧ WitnessKeyOk E w a o s

    instance (w : World D) (a : ArchiveId) (o : Obj D) (s : Sig D) : Decidable (SigOk E w a o s) := by
      unfold SigOk; infer_instance

    /-- The valid steps: the model's reading of what the specification allows. -/
    inductive ValidStep : World D → World D → Prop
      | newArchive (w : World D) (a : ArchiveId) (ar : Archive D) (h : w a = none)
          (hempty : ∀ x, ar.entries x = none) :
          ValidStep w (fun b => if b = a then some ar else w b)
      | create (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
          (ha : w a = some ar) (ho : ar.entries oid = none) (hwf : o.WF oid)
          (hpins : ∀ v ∈ o.versions, ∀ p ∈ v.pins, PinOk E w p)
          (hbranch : ¬ CopyOf w a o → ∀ i (h : i < o.versions.length),
            BranchPointOk E w (prevParent o.versions i) o.versions[i])
          (hfollow : ¬ CopyOf w a o → HeadFollows E w o.versions)
          (hauth : Authorised E w a ar oid o) (hsigs : ∀ s ∈ o.sigs, SigOk E w a o s) :
          ValidStep w (setEntry w a oid (.live o))
      | append (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
          (x : Version D) (ss : List (Sig D)) (ha : w a = some ar)
          (ho : ar.entries oid = some (.live o))
          (hf : o.kind ≠ .owner → Extends o.versions x) (hst : StatusStep o.versions x)
          (hk : x.members.isSome = true ↔ o.kind = .collection) (hm : x.membersOk)
          (hpins : ∀ p ∈ x.pins, PinOk E w p)
          (hbranch : ¬ CopyOf w a (o.append x ss) →
            BranchPointOk E w (o.versions.getLast?.bind (·.parent)) x)
          (hfollow : ¬ CopyOf w a (o.append x ss) →
            x.documentVersion = docCount o.versions + 1 → x.FollowsHeads E w)
          (hauth : Authorised E w a ar oid (o.append x ss))
          (hsigs : ∀ s ∈ ss, SigOk E w a (o.append x ss) s) :
          ValidStep w (setEntry w a oid (.live (o.append x ss)))
      | witness (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
          (ss : List (Sig D)) (ha : w a = some ar) (ho : ar.entries oid = some (.live o))
          (hss : ∀ s ∈ ss, SigOk E w a o s) :
          ValidStep w (setEntry w a oid (.live { o with sigs := o.sigs ++ ss }))

    /-- Any number of valid steps. -/
    abbrev ValidSteps : World D → World D → Prop := Star (ValidStep E)

A valid step is a step, so everything proved about steps holds of valid
steps, immutability first.

    theorem ValidStep.toStep {w w' : World D} (h : ValidStep E w w') : Step w w' := by
      cases h with
      | newArchive a ar h _ => exact .newArchive w a ar h
      | create a ar oid o ha ho => exact .create w a ar oid o ha ho
      | append a ar oid o x ss ha ho => exact .append w a ar oid o x ss ha ho
      | witness a ar oid o ss ha ho => exact .witness w a ar oid o ss ha ho

    theorem ValidSteps.toSteps {w w' : World D} (h : ValidSteps E w w') : Steps w w' :=
      h.mono (·.toStep E)

## What a step does to an entry

Every proof below asks what a step did to the entry of one object. There
are three answers: nothing; the entry was empty before (a new object, or
an object of a new archive); the object **grew**: it kept its identifier,
kind and genesis record, its history and its signature files, and may have
more of either.

    /-- `o'` is `o`, possibly with more versions and more signature files. -/
    structure Grows (o o' : Obj D) : Prop where
      id : o'.id = o.id
      kind : o'.kind = o.kind
      genesis : o'.genesis = o.genesis
      versions : ∃ t, o'.versions = o.versions ++ t
      sigs : ∀ s ∈ o.sigs, s ∈ o'.sigs

    omit [DecidableEq D] in
    theorem Grows.refl (o : Obj D) : Grows o o := ⟨rfl, rfl, rfl, ⟨[], by simp⟩, fun _ h => h⟩

    omit [DecidableEq D] in
    theorem Grows.trans {o o' o'' : Obj D} (h1 : Grows o o') (h2 : Grows o' o'') : Grows o o'' := by
      obtain ⟨t1, ht1⟩ := h1.versions
      obtain ⟨t2, ht2⟩ := h2.versions
      exact ⟨h2.id.trans h1.id, h2.kind.trans h1.kind, h2.genesis.trans h1.genesis,
        ⟨t1 ++ t2, by rw [ht2, ht1, List.append_assoc]⟩, fun s hs => h2.sigs s (h1.sigs s hs)⟩

    omit [DecidableEq D] in
    theorem Grows.append (o : Obj D) (x : Version D) (ss : List (Sig D)) :
        Grows o (o.append x ss) :=
      ⟨rfl, rfl, rfl, ⟨[x], rfl⟩, fun _ h => List.mem_append_left _ h⟩

    omit [DecidableEq D] in
    theorem Grows.witness (o : Obj D) (ss : List (Sig D)) :
        Grows o { o with sigs := o.sigs ++ ss } :=
      ⟨rfl, rfl, rfl, ⟨[], by simp⟩, fun _ h => List.mem_append_left _ h⟩

    omit [DecidableEq D] in
    theorem Step.lookup_cases {w w' : World D} (hs : Step w w') (b : ArchiveId) (x : ObjectId) :
        lookup w' b x = lookup w b x ∨ lookup w b x = none ∨
        (∃ o o', lookup w b x = some (.live o) ∧ lookup w' b x = some (.live o') ∧ Grows o o') := by
      cases hs with
      | newArchive a ar ha =>
        by_cases hb : b = a
        · subst hb; exact Or.inr (Or.inl (by simp [lookup, ha]))
        · exact Or.inl (by simp [lookup, hb])
      | create a ar oid o ha ho =>
        rw [lookup_setEntry ha]
        split
        · rename_i h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr (Or.inl (by simp [lookup, ha, ho]))
        · exact Or.inl rfl
      | append a ar oid o v ss ha ho =>
        rw [lookup_setEntry ha]
        split
        · rename_i h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr (Or.inr ⟨o, _, by simp [lookup, ha, ho], rfl, Grows.append o v ss⟩)
        · exact Or.inl rfl
      | witness a ar oid o ss ha ho =>
        rw [lookup_setEntry ha]
        split
        · rename_i h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr (Or.inr ⟨o, _, by simp [lookup, ha, ho], rfl, Grows.witness o ss⟩)
        · exact Or.inl rfl

For a valid step, the same question has a finer answer, which the proofs
of the next chapters use: a live entry after the step is the entry before;
or the step wrote it, authorised, either as a new object whose pins it
checked or as an object grown by a version whose pins it checked; or the
step added valid witnesses to it.

    /-- What a valid step did to a live entry after it. -/
    theorem ValidStep.live_cases {w w' : World D} (hs : ValidStep E w w') {b : ArchiveId}
        {x : ObjectId} {o' : Obj D} (h : lookup w' b x = some (.live o')) :
        lookup w b x = some (.live o') ∨
        (∃ ar, w b = some ar ∧ Authorised E w b ar x o' ∧
          ((lookup w b x = none ∧ ∀ v ∈ o'.versions, ∀ p ∈ v.pins, PinOk E w p) ∨
            ∃ o y ss, lookup w b x = some (.live o) ∧ o' = o.append y ss ∧
              ∀ p ∈ y.pins, PinOk E w p)) ∨
        ∃ o ss, lookup w b x = some (.live o) ∧ o' = { o with sigs := o.sigs ++ ss } ∧
          ∀ s ∈ ss, SigOk E w b o s := by
      cases hs with
      | newArchive a ar ha hempty =>
        rw [lookup_newArchive ha hempty] at h; exact Or.inl h
      | create a ar oid o ha ho _ hpins _ _ hauth =>
        rw [lookup_setEntry ha] at h
        split at h
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases h
          exact Or.inr (Or.inl ⟨ar, ha, hauth, Or.inl ⟨by simp [lookup, ha, ho], hpins⟩⟩)
        · exact Or.inl h
      | append a ar oid o y ss ha ho _ _ _ _ hpins _ _ hauth =>
        rw [lookup_setEntry ha] at h
        split at h
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases h
          exact Or.inr (Or.inl ⟨ar, ha, hauth,
            Or.inr ⟨o, y, ss, by simp [lookup, ha, ho], rfl, hpins⟩⟩)
        · exact Or.inl h
      | witness a ar oid o ss ha ho hss =>
        rw [lookup_setEntry ha] at h
        split at h
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases h
          exact Or.inr (Or.inr ⟨o, ss, by simp [lookup, ha, ho], rfl, hss⟩)
        · exact Or.inl h

## Identifiers are not reused

A tombstone stays: no step replaces it, since a new object needs an empty
entry and a new version a live one. An identifier taken down (section 13.3)
can therefore never name another object, and a pin of the line taken down
can never resolve there to something else. Section 13.2 lets a line taken
down return, from a copy holding the version its tombstone pins; the model
leaves returns out, and says so where it matters.

    omit [DecidableEq D] in
    /-- **A tombstone stays.** -/
    theorem Step.tomb_stays {w w' : World D} (hs : Step w w') {b : ArchiveId} {x : ObjectId}
        {n : Nat} {d : D} (h : lookup w b x = some (.tomb n d)) :
        lookup w' b x = some (.tomb n d) := by
      rcases hs.lookup_cases b x with h1 | h1 | ⟨o, _, h1, _⟩
      · rw [h1, h]
      · rw [h] at h1; cases h1
      · rw [h] at h1; cases h1

    omit [DecidableEq D] in
    theorem Steps.tomb_stays {w w' : World D} (hs : Steps w w') {b : ArchiveId} {x : ObjectId}
        {n : Nat} {d : D} (h : lookup w b x = some (.tomb n d)) :
        lookup w' b x = some (.tomb n d) :=
      hs.invariant (fun w => lookup w b x = some (.tomb n d)) (·.tomb_stays) h

## Objects only grow

A live object stays live and grows. For a collection: every change of its
member list is a new version, which records who deposited it and why (the
depositor and the message), and every earlier member list is kept, as a
prefix of the history. This is half of section 8.4's "adding a revision
..., removing one, or adding or removing a member is a new version of the
selection, made by its curator". The other half, that only the curator may
make that version, needs signatures: it is proved in
[chapter 8](47-acts.md).

    omit [DecidableEq D] in
    /-- **Objects only grow.** -/
    theorem Step.live_grows {w w' : World D} (hs : Step w w') {b : ArchiveId} {x : ObjectId}
        {o : Obj D} (h : lookup w b x = some (.live o)) :
        ∃ o', lookup w' b x = some (.live o') ∧ Grows o o' := by
      rcases hs.lookup_cases b x with h1 | h1 | ⟨o1, o', h1, h2, hg⟩
      · exact ⟨o, by rw [h1, h], Grows.refl o⟩
      · rw [h] at h1; cases h1
      · rw [h] at h1; cases h1; exact ⟨o', h2, hg⟩

    omit [DecidableEq D] in
    theorem Steps.live_grows {w w' : World D} (hs : Steps w w') {b : ArchiveId} {x : ObjectId}
        {o : Obj D} (h : lookup w b x = some (.live o)) :
        ∃ o', lookup w' b x = some (.live o') ∧ Grows o o' := by
      refine hs.invariant (fun w => ∃ o', lookup w b x = some (.live o') ∧ Grows o o') ?_
        ⟨o, h, Grows.refl o⟩
      rintro _ _ hstep ⟨o1, h1, hg1⟩
      obtain ⟨o2, h2, hg2⟩ := hstep.live_grows h1
      exact ⟨o2, h2, hg1.trans hg2⟩

## Valid steps keep worlds well formed

The main theorem of the chapter. An entry after a valid step is either an
entry of before, or the object just created, or an object grown by the
step; in each case it is well formed. The pins of its versions are either
pins held before the step, or pins checked by it. The lemma is stated for
any property `Q` of the pins held before, so that it serves twice: here,
and for takedowns below.

    theorem WF_witness {o : Obj D} {oid : ObjectId} (h : o.WF oid) (ss : List (Sig D)) :
        ({ o with sigs := o.sigs ++ ss } : Obj D).WF oid :=
      ⟨h.id, h.nonempty, h.history, h.kinds, h.members, h.statuses, h.genesis⟩

    theorem ValidStep.entry {w w' : World D} (hs : ValidStep E w w')
        (hobj : ∀ a oid o, lookup w a oid = some (.live o) → o.WF oid)
        {Q : Pin D → Prop} (hq : ∀ a oid o, lookup w a oid = some (.live o) →
          ∀ v ∈ o.versions, ∀ p ∈ v.pins, Q p)
        {b : ArchiveId} {x : ObjectId} {o' : Obj D} (h : lookup w' b x = some (.live o')) :
        o'.WF x ∧ ∀ v ∈ o'.versions, ∀ p ∈ v.pins, Q p ∨ Held E w p := by
      cases hs with
      | newArchive a ar ha hempty =>
        rw [lookup_newArchive ha hempty] at h
        exact ⟨hobj _ _ _ h, fun v hv p hp => Or.inl (hq _ _ _ h v hv p hp)⟩
      | create a ar oid o ha ho hwf hpins =>
        rw [lookup_setEntry ha] at h
        split at h
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases h
          exact ⟨hwf, fun v hv p hp => Or.inr ((hpins v hv p hp).held E)⟩
        · exact ⟨hobj _ _ _ h, fun v hv p hp => Or.inl (hq _ _ _ h v hv p hp)⟩
      | append a ar oid o y ss ha ho hf hst hk hm hpins =>
        rw [lookup_setEntry ha] at h
        split at h
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases h
          have hl : lookup w b x = some (.live o) := by simp [lookup, ha, ho]
          have hwf := hobj _ _ _ hl
          refine ⟨⟨hwf.id, by simp [Obj.append], fun hko => (hwf.history hko).snoc (hf hko), ?_, ?_,
            hwf.statuses.snoc hst, hwf.genesis⟩, ?_⟩
          · simpa [Obj.append, or_imp, forall_and] using ⟨hwf.kinds, hk⟩
          · simpa [Obj.append, or_imp, forall_and] using ⟨hwf.members, hm⟩
          · simpa [Obj.append, or_imp, forall_and] using
              ⟨fun v hv p hp => Or.inl (hq _ _ _ hl v hv p hp),
                fun p hp => Or.inr ((hpins p hp).held E)⟩
        · exact ⟨hobj _ _ _ h, fun v hv p hp => Or.inl (hq _ _ _ h v hv p hp)⟩
      | witness a ar oid o ss ha ho =>
        rw [lookup_setEntry ha] at h
        split at h
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases h
          have hl : lookup w b x = some (.live o) := by simp [lookup, ha, ho]
          exact ⟨WF_witness (hobj _ _ _ hl) ss, fun v hv p hp => Or.inl (hq _ _ _ hl v hv p hp)⟩
        · exact ⟨hobj _ _ _ h, fun v hv p hp => Or.inl (hq _ _ _ h v hv p hp)⟩

Valid steps create no tombstone: a new archive is empty, and the other
steps write live objects.

    theorem ValidStep.noTombs {w w' : World D} (hs : ValidStep E w w') (h : NoTombs w) :
        NoTombs w' := by
      intro b x n d hl
      have := (hs.toStep E).lookup_cases b x
      rcases this with h1 | h1 | ⟨o, o', _, h2, _⟩
      · rw [h1] at hl; exact h _ _ _ _ hl
      · cases hs with
        | newArchive a ar ha hempty =>
          rw [lookup_newArchive ha hempty] at hl; exact h _ _ _ _ hl
        | create a ar oid o ha =>
          rw [lookup_setEntry ha] at hl
          split at hl
          · cases hl
          · exact h _ _ _ _ hl
        | append a ar oid o y ss ha =>
          rw [lookup_setEntry ha] at hl
          split at hl
          · cases hl
          · exact h _ _ _ _ hl
        | witness a ar oid o ss ha =>
          rw [lookup_setEntry ha] at hl
          split at hl
          · cases hl
          · exact h _ _ _ _ hl
      · rw [h2] at hl; cases hl

A pin reports `removed` at an archive exactly when the archive has a
tombstone of its line (`resolveAt_removed_iff`, [chapter 3](30-archive.md)),
and tombstones stay, so `removed` stays too; a pin found stays found.

    theorem Step.removedAt {w w' : World D} (hs : Step w w') {p : Pin D}
        (h : RemovedAt E w p) : RemovedAt E w' p := by
      obtain ⟨b, hb, hr⟩ := h
      obtain ⟨n, d, hl⟩ := (resolveAt_removed_iff E.hash).mp hr
      exact ⟨b, hb, (resolveAt_removed_iff E.hash).mpr ⟨n, d, hs.tomb_stays hl⟩⟩

    theorem Step.held {w w' : World D} (hs : Step w w') {p : Pin D} (h : Held E w p) :
        Held E w' p :=
      h.elim (fun hf => Or.inl (hs.found E.hash hf)) (fun hr => Or.inr (hs.removedAt E hr))

So, without takedowns, a pin written by a valid step is found: none reports
`removed`.

    /-- **Valid steps keep worlds well formed.** -/
    theorem ValidStep.wf {w w' : World D} (hs : ValidStep E w w') (hw : WFWorld E w) :
        WFWorld E w' :=
      ⟨fun _ _ _ h => (hs.entry E hw.1 hw.2.1 h).1,
       fun _ _ _ h v hv p hp => by
         rcases (hs.entry E hw.1 hw.2.1 h).2 v hv p hp with hf | hf | ⟨b, _, hr⟩
         · exact (hs.toStep E).found E.hash hf
         · exact (hs.toStep E).found E.hash hf
         · obtain ⟨n, d, hl⟩ := (resolveAt_removed_iff E.hash).mp hr
           exact absurd hl (hw.2.2 _ _ _ _),
       hs.noTombs E hw.2.2⟩

    theorem ValidSteps.wf {w w' : World D} (hs : ValidSteps E w w') (hw : WFWorld E w) :
        WFWorld E w' :=
      hs.invariant _ (·.wf E) hw

The consequence: in archives built by valid steps from nothing, every pin
held by any version is found. Takedowns are not steps; what they do to this
property is the subject of the next section.

    /-- **Nothing dangles.** -/
    theorem ValidSteps.pins_ok {w : World D}
        (hs : ValidSteps E (fun _ => (none : Option (Archive D))) w) : PinsOk E w :=
      (hs.wf E (WFWorld.empty E)).2.1

In such worlds every member of every collection is pinned, as section 8.5
asks, and its pins are found.

    /-- **Every member is pinned.** -/
    theorem ValidSteps.members_pinned {w : World D}
        (hs : ValidSteps E (fun _ => (none : Option (Archive D))) w)
        {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
        {v : Version D} (hv : v ∈ o.versions) {c : Members D} (hc : v.members = some c)
        {m : Member D} (hm : m ∈ c.members) :
        m.pins ≠ [] ∧ ∀ p ∈ m.pins, Found E.hash w p := by
      have hw := hs.wf E (WFWorld.empty E)
      have hmo := (hw.1 _ _ _ hl).members v hv
      unfold Version.membersOk at hmo
      rw [hc] at hmo
      refine ⟨(hmo m hm).2.1, fun p hp => hw.2.1 _ _ _ hl v hv p ?_⟩
      simp only [Version.pins, Version.memberPins, hc, Members.pins]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨m, hm, hp⟩))

## Takedowns among the steps

Takedowns are not steps: they remove versions, against which pins were
made. They happen all the same, by law or because an archive stops keeping
a line, and the model must say what they do to the rest. An **event** is a
valid step or a takedown of a live copy of a line. A draft is never taken
down: "it is deleted, and leaves no tombstone" (section 13), which
[chapter 10](50-drafts.md) models. Nor is a key log, in the model. This is
a **modelling restriction**: section 13.2 lets an archive take down an
owner object, one that its objects need "only for itself, and only by law
or at its keeper's request", the signatures that need it being then
unchecked there, and one that nothing needs for any reason. The model,
which has neither keepers nor the status unchecked, leaves all these
takedowns out, so that an owner's key log, once held, stays: the authority
of an owner's signatures in a world rests on the key logs the world holds
([chapter 8](47-acts.md)).

    /-- A valid step, or a takedown (section 13.2). -/
    inductive Event : World D → World D → Prop
      | step {w w' : World D} : ValidStep E w w' → Event w w'
      | takedown (w : World D) (a : ArchiveId) (l : LineId) (o : Obj D)
          (hk : l ≠ keyLogLine l.owner) (hl : lookup w a (.line l) = some (.live o)) :
          Event w (takedown E.hash w a (.line l) o)

    /-- Any number of events. -/
    abbrev Events : World D → World D → Prop := Star (Event E)

The property that events keep: objects are well formed, and every pin held
is found, or reports `removed`.

    /-- Every pin held is found, or reports `removed`. -/
    def PinsHeld (w : World D) : Prop :=
      ∀ a oid o, lookup w a oid = some (.live o) →
        ∀ v ∈ o.versions, ∀ p ∈ v.pins, Held E w p

    /-- A sound world: well-formed objects, and pins held are found or report
    removed. -/
    def SoundWorld (w : World D) : Prop :=
      (∀ a oid o, lookup w a oid = some (.live o) → o.WF oid) ∧ PinsHeld E w

    theorem SoundWorld.empty : SoundWorld E (fun _ => (none : Option (Archive D))) :=
      ⟨(WFWorld.empty E).1, fun _ _ _ h => by simp [lookup] at h⟩

    theorem ValidStep.sound {w w' : World D} (hs : ValidStep E w w') (hw : SoundWorld E w) :
        SoundWorld E w' :=
      ⟨fun _ _ _ h => (hs.entry E hw.1 hw.2 h).1,
       fun _ _ _ h v hv p hp => by
         rcases (hs.entry E hw.1 hw.2 h).2 v hv p hp with hh | hh
         · exact (hs.toStep E).held E hh
         · exact (hs.toStep E).held E hh⟩

A takedown leaves every other object as it was (`lookup_takedown`,
[chapter 3](30-archive.md)). At the archive that took the line down, its
pins report `removed`; elsewhere they resolve as before.

    theorem takedown_held {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl : lookup w a oid = some (.live o)) {p : Pin D} (h : Held E w p) :
        Held E (takedown E.hash w a oid o) p := by
      have key : ∀ b ∈ p.hints, (∃ t, resolveAt E.hash w b p = .ok t) ∨
          resolveAt E.hash w b p = .removed →
          Held E (takedown E.hash w a oid o) p := by
        intro b hb hr
        by_cases hc : b = a ∧ ObjectId.line p.line = oid
        · obtain ⟨rfl, hc⟩ := hc
          exact Or.inr ⟨b, hb, takedown_removed E.hash hl hc⟩
        · rw [← takedown_other E.hash hl hc] at hr
          rcases hr with ⟨t, ht⟩ | hr
          · exact Or.inl ⟨b, hb, t, ht⟩
          · exact Or.inr ⟨b, hb, hr⟩
      rcases h with ⟨b, hb, t, ht⟩ | ⟨b, hb, hr⟩
      · exact key b hb (Or.inl ⟨t, ht⟩)
      · exact key b hb (Or.inr hr)

    theorem takedown_sound {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl : lookup w a oid = some (.live o)) (hw : SoundWorld E w) :
        SoundWorld E (takedown E.hash w a oid o) :=
      ⟨fun _ _ _ h => hw.1 _ _ _ (lookup_takedown E.hash hl h).2,
       fun _ _ _ h v hv p hp =>
         takedown_held E hl (hw.2 _ _ _ (lookup_takedown E.hash hl h).2 v hv p hp)⟩

    theorem Event.sound {w w' : World D} (he : Event E w w') (hw : SoundWorld E w) :
        SoundWorld E w' := by
      cases he with
      | step hs => exact hs.sound E hw
      | takedown a oid o _ hl => exact takedown_sound E hl hw

    /-- **Only a takedown stops a pin from being found, and then it reports
    removed.** In a world built by events from nothing, every pin held by any
    version is found, or reports `removed`, at one of its hints. -/
    theorem Events.sound {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) : SoundWorld E w :=
      hs.invariant _ (·.sound E) (SoundWorld.empty E)

Tombstones stay through events too: a takedown leaves other entries as they
were, and the entry it changes was live.

    theorem Event.tomb_stays {w w' : World D} (he : Event E w w') {b : ArchiveId}
        {x : ObjectId} {n : Nat} {d : D} (h : lookup w b x = some (.tomb n d)) :
        lookup w' b x = some (.tomb n d) := by
      cases he with
      | step hs => exact (hs.toStep E).tomb_stays h
      | takedown a oid o _ hl =>
        rw [lookup_takedown_eq E.hash hl, if_no (by rintro ⟨rfl, rfl⟩; simp [hl] at h)]
        exact h

    theorem Events.tomb_stays {w w' : World D} (hs : Events E w w') {b : ArchiveId}
        {x : ObjectId} {n : Nat} {d : D} (h : lookup w b x = some (.tomb n d)) :
        lookup w' b x = some (.tomb n d) :=
      hs.invariant (fun w => lookup w b x = some (.tomb n d)) (·.tomb_stays E) h

    end OpenSheaf
