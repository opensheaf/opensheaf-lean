-- Generated from literate/10-basic.md by opensheaf-literate: edit the document, not this file.
namespace OpenSheaf

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

/-- The line of an owner's key log: `(owner name, owner name)` (section 6). -/
def keyLogLine (x : OwnerName) : LineId := ⟨x, x⟩

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

/-- A pinned reference from an object version to an exact version of a line:
a pin, and its role (issues #21 and #28). -/
structure Ref (D : Type) where
  role : String
  pin : Pin D
  deriving DecidableEq, Repr

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

/-- `parent` in `object.json` (section 9.1), with the signature files of the
parent version that the branch carries as evidence (section 9.2). -/
structure Parent (D : Type) where
  pin : Pin D
  documentVersion : Nat
  sigs : List (Sig D) := []
  deriving DecidableEq, Repr

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
