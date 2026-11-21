# Basic notions

This chapter defines the vocabulary of the model: names and owner names,
lines and drafts, pins, member lists, keys and signatures, and object
versions (specification, sections 4 to 9). There is nothing to prove yet;
the choices made here decide what the later chapters can state.

Everything lives in the namespace `OpenSheaf`.

    -- in OpenSheaf/Basic.lean:
    namespace OpenSheaf

## Names, owners, lines

A work and an owner have a **name**, the digest of a genesis record
(section 5), and an owner's name is its **owner name** (section 6). A
**line** is the history of a work as decided by one owner, named by the
pair (name, owner) (section 7), and a draft has an identifier of its own,
chosen by its archive (section 10.1). The identifier of an object is
`sheaf:<name>:<owner>` or `sheaf:draft:<id>` (section 4); the model keeps
the parts and never looks inside them.

Archives are named by no file (section 3): an archive is found at a base
URL, a location that may change and need not be unique. The model indexes
archives by such a location, `ArchiveId`, and uses it only to say where a
copy is kept and where a pin is looked up; nothing in an object names it.

    /-- A name: the digest of a genesis record, written in base32 (section 5). -/
    abbrev Name := String

    /-- An owner name: the name of an owner's genesis record (section 6). -/
    abbrev OwnerName := String

    /-- The base URL of an archive: a location, not a name (section 3). -/
    abbrev ArchiveId := String

    /-- The identifier a draft's archive chooses for it (section 10.1). -/
    abbrev DraftId := String

    /-- A logical path of the content of an object version (OCFL). -/
    abbrev LogicalPath := String

    /-- A key, written as a `did:key` URI (section 6.1). -/
    abbrev Key := String

    /-- A line: a name and the owner name of the line's owner (section 7). -/
    structure LineId where
      name : Name
      owner : OwnerName
      deriving DecidableEq, Repr

    /-- The identifier of an object: a line, or a draft (sections 4 and 10.1). -/
    inductive ObjectId
      | line (l : LineId)
      | draft (d : DraftId)
      deriving DecidableEq, Repr

An owner object is the owner's own line, (owner name, owner name): its key
log (section 6).

    /-- The line of an owner's key log: `(owner name, owner name)` (section 6). -/
    def keyLogLine (x : OwnerName) : LineId := ⟨x, x⟩

## Enumerations

Three fields of the specification take one of a few values: the `kind` of an
object, its `status`, and the `type` of a collection.

    /-- `kind` in `object.json` and `genesis.json` (sections 4 and 5.1). -/
    inductive Kind
      | document
      | collection
      | owner
      deriving DecidableEq, Repr

    /-- `status` in `object.json` (sections 4.3 and 13.1). -/
    inductive Status
      | active
      | withdrawn
      deriving DecidableEq, Repr

    /-- `type` in `members.json` (section 8.1). -/
    inductive CollectionType
      | catalogue
      | selection
      deriving DecidableEq, Repr

## Pins

A pin is "the pair (object version, SHA-512 digest of that version's
inventory file, as its checksum file states it)" (section 4), of a line. Digests are values of a type `D`
left open, so that the model does not depend on the digest algorithm (see
the [introduction](index.md)). Version numbers count from 1, as OCFL's
`v1`, `v2`, ...

Where a pin is written, the specification also gives where copies may be
found: the `at` of a collection member (section 8.2), a branch's
`parent.url` (section 9.1), the `at` of a `sheaf:` URI (section 12.1). These
are **hints**, "equal hints, which need no signature" (section 8.2). The
model's pin carries its hints, as `hints` (`at` is a keyword of Lean): the
archives in which a reader looks for the version, in order. They are not
part of what the pin names: two pins with the same line, version and
digest name the same object version, wherever they say to look
(`Pin.names`). Where the model compares pins for what they name (a branch
point kept, a pin carried over, [chapter 7](45-worlds.md)), it compares
them by `Pin.names`, never by equality, so that changing a hint changes
nothing else.

    /-- A pin: an object version of a line, and the digest of its inventory
    (section 4); with the hints of where copies may be found, which are not part
    of what it names (sections 3, 8.2 and 12.1). -/
    structure Pin (D : Type) where
      line : LineId
      version : Nat
      digest : D
      hints : List ArchiveId := []
      deriving DecidableEq, Repr

    /-- Two pins name the same object version: same line, version and digest. -/
    def Pin.names {D : Type} (p q : Pin D) : Prop :=
      p.line = q.line ∧ p.version = q.version ∧ p.digest = q.digest

    instance {D : Type} [DecidableEq D] (p q : Pin D) : Decidable (p.names q) := by
      unfold Pin.names; infer_instance

    theorem Pin.names_refl {D : Type} (p : Pin D) : p.names p := ⟨rfl, rfl, rfl⟩

## Member lists

A collection's `members.json` lists members, each naming a line by its name
and owner, with `at`, where copies of it may be found (section 8.2), which
the model calls `hints`. The two
types of collection pin their members differently. In a catalogue a member
has one pin, of an object version, and `follow` says whether the
catalogue's tools move it to the latest version (section 8.3). In a
selection the pins are the revision set vetted by the curator (section
8.4). The model gives both a list of pins, each carrying the member's
hints, and lets the operations of [chapter 6](40-collection.md) treat them
differently.

    /-- An entry of `members.json` (section 8.2): the member's line, where copies of
    it may be found, and its pins. In a catalogue it has one pin, and `follow` says
    whether updates move it to the latest version (section 8.3); in a selection its
    pins are the revision set (section 8.4). -/
    structure Member (D : Type) where
      line : LineId
      hints : List ArchiveId
      follow : Bool := false
      pins : List (Pin D)
      deriving DecidableEq, Repr

    /-- `members.json` (section 8.2). -/
    structure Members (D : Type) where
      type : CollectionType
      members : List (Member D)
      deriving DecidableEq, Repr

## References

A document may refer to an exact version of another document: a short
account of a proof to the version of its detailed argument that was
reviewed, a review to the version it reviews, an analysis to the data it
used. The core of the specification records such links only inside the
documents and in DataCite relations (section 4.4), which tools do not
follow as pins. Issue
[#21](https://github.com/opensheaf/opensheaf.github.io/issues/21) proposes
one structure for them, a **pinned reference**: a pin, with a role saying
what it means; issue
[#28](https://github.com/opensheaf/opensheaf.github.io/issues/28) proposes a
first extension that records such references in `object.json`. The model
follows these proposals, which are not part of the specification: a
reference is a role and a pin, with its hints. Roles are left as strings
(DataCite relation types such as `IsSupplementedBy` or `Reviews`), and the
model never looks inside them.

    /-- A pinned reference from an object version to an exact version of a line:
    a pin, and its role (issues #21 and #28). -/
    structure Ref (D : Type) where
      role : String
      pin : Pin D
      deriving DecidableEq, Repr

## Keys and signatures

An owner signs the versions of its lines with **current keys**, and the
versions of its key log with **rotation keys**, committed in advance by
their digests (section 6.1). Each version of a key log holds `keys.json`:

- `keys` and `threshold`: the current keys, and how many must sign a version
  of a line;
- `next` and `nextThreshold`: the digests of the rotation keys that sign the
  next version of the key log, and how many must;
- `ended` and `successor`, in an ending version (section 6.3), which has
  neither keys nor rotation keys;
- `exposed`: keys of earlier versions that this version declares exposed.

Keys are digested by a function of the environment (`Env.keyDigest`,
[chapter 2](20-object.md)) into the same type `D` as inventories: the
specification uses SHA-256 for keys and SHA-512 for inventories, and the
model needs neither.

    /-- `keys.json` (section 6.1). -/
    structure Keys (D : Type) where
      keys : List Key := []
      threshold : Nat := 0
      next : List D := []
      nextThreshold : Nat := 0
      ended : Bool := false
      successor : Option OwnerName := none
      exposed : List Key := []
      deriving DecidableEq, Repr

A **signature file** holds one signature of an object version by the owner
of its line (section 7.2): the object, the version, the digest of its
inventory, the key that signs, and the version of the signer's key log
against which it is judged, as a pin of the owner object. The signer is the
owner of the line, and the key log pinned is the signer's, a rule that
[chapter 5](38-lines.md) checks. What is signed is the message made of
these fields; whether a signature verifies is a fact of the environment
(`Env.verifies`, [chapter 2](20-object.md)).

    /-- A signature file (section 7.2): a signature of version `version` of `line`,
    whose inventory has the digest `digest`, by `key`, judged against the key-log
    version `keyLog`. -/
    structure Sig (D : Type) where
      line : LineId
      version : Nat
      digest : D
      key : Key
      keyLog : Pin D
      deriving DecidableEq, Repr

A **fork record** of a key log (section 6.3) carries the versions of the
other side of a fork: for each, its inventory file, its checksum file, its
`keys.json`, and its signature files. The model keeps the number and the
digest of the inventory, the signature files, and the version itself, as
the fields a version of a key log has: its `keys.json`, files, description,
status and record of deposit ([chapter 4](35-owners.md) rebuilds the
inventory from them and checks the digest, as section 14.3 checks
"`keys.json` and checksum file against its inventory").

    /-- A version of a key log carried by a fork record, under `forked/<d>/`
    (section 6.3): its number, the digest of its inventory, its signature files,
    and the version itself. -/
    structure Carried (D : Type) where
      version : Nat
      digest : D
      keys : Keys D
      sigs : List (Sig D)
      files : List (LogicalPath × D) := []
      description : String := ""
      status : Status := .active
      depositor : String := ""
      message : String := ""
      deriving DecidableEq, Repr

## Branch points

A branch records its **branch point** in `parent` (section 9.1): the pin of
the parent version (with `url` as a hint), the document version it holds,
and, as evidence, the parent owner's signature files of that version
(`parent/signatures/`, section 9.2). The other evidence of the
specification (`parent/inventory.json`, `parent/object.json` and
`parent/parent/`) is left out. The model carries the signature files but
does not check them, nor that they are present: it checks a branch point
by resolving it ([chapter 7](45-worlds.md)), so the check of section 9.3
without access to the parent's line is not modelled.

    /-- `parent` in `object.json` (section 9.1), with the signature files of the
    parent version that the branch carries as evidence (section 9.2). -/
    structure Parent (D : Type) where
      pin : Pin D
      documentVersion : Nat
      sigs : List (Sig D) := []
      deriving DecidableEq, Repr

Two records of a branch point name the same one when they pin the same
parent version and record the same document version of it. The hints of
the pin (`parent.url`) and the evidence are not part of it: a version
that updates `parent.url`, or carries more of the parent owner's signature
files, keeps the branch point (section 9.4 speaks of the parent version,
not of where it is found).

    /-- Two branch points are the same: the same parent version, by line, number
    and digest, and the same document version; hints and evidence aside
    (sections 9.1 and 9.4). -/
    def Parent.Same {D : Type} (pa pb : Parent D) : Prop :=
      pa.pin.names pb.pin ∧ pa.documentVersion = pb.documentVersion

    instance {D : Type} [DecidableEq D] (pa pb : Parent D) : Decidable (pa.Same pb) := by
      unfold Parent.Same; infer_instance

    theorem Parent.same_refl {D : Type} (pa : Parent D) : pa.Same pa := ⟨Pin.names_refl _, rfl⟩

    /-- The branch point `pa` keeps the branch point `prev` of the version before,
    if there is one. -/
    def Parent.Keeps {D : Type} : Option (Parent D) → Parent D → Prop
      | none, _ => False
      | some pp, pa => pp.Same pa

    instance {D : Type} [DecidableEq D] (prev : Option (Parent D)) (pa : Parent D) :
        Decidable (Parent.Keeps prev pa) := by
      cases prev <;> unfold Parent.Keeps <;> infer_instance

## Object versions

An object version holds the content of the object as of that version, its
description, and OpenSheaf's record of it (sections 4.2 to 4.4). The model
keeps:

- the **content**: the files, as logical paths with the digests of their
  bytes, and, for a collection, the member list;
- the **document version**, which counts the changes of the content
  ([chapter 2](20-object.md)); an owner object has none, and the model
  writes 0;
- the **description**, `datacite.json`, as an uninterpreted string;
- the **references** of the version, recorded in `object.json` by an
  extension (the proposal above);
- for a branch, its **branch point**, `parent`;
- for an owner object, its **keys**, `keys.json`, and, for a fork record,
  the versions it **carries**;
- the **status**, active or withdrawn;
- the **depositor** and the **message**, which OCFL keeps in the inventory
  and which the specification uses to record who made each version and why
  (section 4.1).

The genesis record is part of every version too (section 4.1); the model
keeps it once, with the object ([chapter 2](20-object.md)). The
description, the references, the branch point, the status and the record
of the deposit are not content: a new version that changes only them is a
description-only version or a withdrawal, and keeps the document version.

    /-- An object version (sections 4.1 to 4.4). Its content is its files and, for a
    collection, its member list; the description, the branch point, the keys and
    the record of the deposit (depositor and message, kept in the inventory) are
    not content. -/
    structure Version (D : Type) where
      documentVersion : Nat
      files : List (LogicalPath × D)
      members : Option (Members D) := none
      description : String
      refs : List (Ref D) := []
      parent : Option (Parent D) := none
      keys : Option (Keys D) := none
      carried : List (Carried D) := []
      status : Status := .active
      depositor : String
      message : String
      deriving DecidableEq, Repr

The pins *held* by an object version are those of its member list, of its
references, and of its branch point. Every theorem of the model about pins
held (that they resolve when they are made, that they never dangle without
a takedown, that they form no cycles) is therefore about references and
branch points too.

    /-- Every pin of a member list. -/
    def Members.pins {D : Type} (c : Members D) : List (Pin D) :=
      c.members.flatMap (·.pins)

    /-- The pins of the member list of an object version, if any. -/
    def Version.memberPins {D : Type} (v : Version D) : List (Pin D) :=
      match v.members with
      | none => []
      | some ms => ms.pins

    /-- The pin of the branch point of an object version, if any. -/
    def Version.parentPins {D : Type} (v : Version D) : List (Pin D) :=
      match v.parent with
      | none => []
      | some pa => [pa.pin]

    /-- The pins held by an object version: those of its member list, of its
    references and of its branch point. -/
    def Version.pins {D : Type} (v : Version D) : List (Pin D) :=
      v.memberPins ++ v.refs.map (·.pin) ++ v.parentPins

    end OpenSheaf
