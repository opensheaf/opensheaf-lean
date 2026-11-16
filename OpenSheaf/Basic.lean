-- Generated from literate/10-basic.md by opensheaf-literate: edit the document, not this file.
namespace OpenSheaf

/-- The identifier of an archive (section 6.2). -/
abbrev ArchiveId := String

/-- The identifier of an object within its archive (section 6.3). -/
abbrev ObjectId := String

/-- A logical path of the content of an object version (OCFL). -/
abbrev LogicalPath := String

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

/-- A pin fixes one object version: the archive, the object, the OCFL version
number (`v1` is `1`) and the digest of the inventory of that version
(section 10.2). -/
structure Pin (D : Type) where
  archive : ArchiveId
  object : ObjectId
  version : Nat
  digest : D
  deriving DecidableEq, Repr

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

/-- A pinned reference from an object version to an exact version of an
object: a pin, and its role (issues #21 and #28). -/
structure Ref (D : Type) where
  role : String
  pin : Pin D
  deriving DecidableEq, Repr

/-- An object version (sections 7 and 9). Its content is its files and, for a
collection, its member list; the description and the record of the deposit
(depositor and message, kept in the inventory) are not content. -/
structure Version (D : Type) where
  documentVersion : Nat
  files : List (LogicalPath × D)
  members : Option (Members D) := none
  description : String
  refs : List (Ref D) := []
  source : Option (Pin D) := none
  status : Status := .active
  depositor : String
  message : String
  deriving DecidableEq, Repr

/-- Every pin of a member list. -/
def Members.pins {D : Type} (c : Members D) : List (Pin D) :=
  c.members.flatMap (·.pins)

/-- The pins of the member list of an object version, if any. -/
def Version.memberPins {D : Type} (v : Version D) : List (Pin D) :=
  match v.members with
  | none => []
  | some ms => ms.pins

/-- The pins held by an object version: those of its member list and of its
references. -/
def Version.pins {D : Type} (v : Version D) : List (Pin D) :=
  v.memberPins ++ v.refs.map (·.pin)

end OpenSheaf
