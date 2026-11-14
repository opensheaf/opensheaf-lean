# Basic notions

This chapter defines the vocabulary of the model: identifiers, pins, member
lists and object versions (specification, sections 3, 7, 9 and 10). There is
nothing to prove yet; the choices made here decide what the later chapters
can state.

Everything lives in the namespace `OpenSheaf`.

    -- in OpenSheaf/Basic.lean:
    namespace OpenSheaf

## Identifiers

Archives and objects are named by strings (sections 6.2 and 6.3), and so are
the logical paths of the content of an object version (OCFL). The model
never looks inside them: it only compares them.

    /-- The identifier of an archive (section 6.2). -/
    abbrev ArchiveId := String

    /-- The identifier of an object within its archive (section 6.3). -/
    abbrev ObjectId := String

    /-- A logical path of the content of an object version (OCFL). -/
    abbrev LogicalPath := String

## Enumerations

Three fields of the specification take one of a few values: the `kind` of an
object, its `status`, and the `type` of a collection, which is either a
catalogue or a selection.

    /-- `kind` in `object.json` (section 9). -/
    inductive Kind
      | document
      | collection
      deriving DecidableEq, Repr

    /-- `status` in `object.json` (sections 9 and 11). -/
    inductive Status
      | active
      | withdrawn
      deriving DecidableEq, Repr

    /-- `type` in `members.json` (section 10.1). -/
    inductive CollectionType
      | catalogue
      | selection
      deriving DecidableEq, Repr

## Pins

A pin fixes one object version (section 10.2): the archive, the object, the
OCFL version number, and the digest of the inventory of that version. Digests
are values of a type `D` left open, so that the model does not depend on the
digest algorithm (see the [introduction](index.md)). Version numbers count
from 1, as OCFL's `v1`, `v2`, ...

    /-- A pin fixes one object version: the archive, the object, the OCFL version
    number (`v1` is `1`) and the digest of the inventory of that version
    (section 10.2). -/
    structure Pin (D : Type) where
      archive : ArchiveId
      object : ObjectId
      version : Nat
      digest : D
      deriving DecidableEq, Repr

## Member lists

A collection's `members.json` lists members, each naming an object of some
archive (section 10.2). The two kinds of collection use the pins of a member
differently. In a catalogue a member has one pin, of an object version, and
`follow` says whether updating the catalogue moves the pin to the newest
version. In a selection the pins are the revision set vetted by the curator.
The model gives both a list of pins and lets the operations of
[chapter 4](40-collection.md) treat them differently.

    /-- An entry of `members.json` (section 10.2). In a catalogue it has one pin,
    of an object version, and `follow` says whether updates move it to the head;
    in a selection its pins are the revision set vetted by the curator. -/
    structure Member (D : Type) where
      archive : ArchiveId
      object : ObjectId
      follow : Bool := false
      pins : List (Pin D)
      deriving DecidableEq, Repr

    /-- `members.json` (section 10). -/
    structure Members (D : Type) where
      type : CollectionType
      members : List (Member D)
      deriving DecidableEq, Repr

## Object versions

An object version holds the content of the object as of that version, its
description, and OpenSheaf's record of it (sections 7 and 9). The model keeps:

- the **content**: the files, as logical paths with the digests of their
  bytes, and, for a collection, the member list;
- the **document version**, which counts the changes of the content
  ([chapter 2](20-object.md));
- the **description**, `datacite.json`, as an uninterpreted string;
- the **status**, active or withdrawn;
- the **depositor** and the **message**, which OCFL keeps in the inventory
  and which the specification uses to record who made each version and why.

The description, the status and the record of the deposit are not content:
a new version that changes only them is a description-only version or a
withdrawal, and keeps the document version.

    /-- An object version (sections 7 and 9). Its content is its files and, for a
    collection, its member list; the description and the record of the deposit
    (depositor and message, kept in the inventory) are not content. -/
    structure Version (D : Type) where
      documentVersion : Nat
      files : List (LogicalPath × D)
      members : Option (Members D) := none
      description : String
      status : Status := .active
      depositor : String
      message : String
      deriving DecidableEq, Repr

The pins *held* by an object version are those of its member list. A
document has none in this model; relations in `datacite.json` that point to
exact object versions would be pins too, and can be added here when the
model needs them.

    /-- The pins held by an object version: those of its member list. -/
    def Version.pins {D : Type} (v : Version D) : List (Pin D) :=
      match v.members with
      | none => []
      | some ms => ms.members.flatMap (·.pins)

    end OpenSheaf
