# Named document versions

The points of the space are *named document versions*: an object, named by
its identifier, and a document version number (section 4.2 of the
specification). In version 0.2 the identifier of a sealed object is its
line, `sheaf:<name>:<owner>` (section 4), the same in every archive that
keeps a copy: no file of an object names the archive that holds it (section
4.3). So a named document version names a version of a line wherever it is
kept, which is what a `sheaf:` URI without a digest names
(`sheaf:<name>:<owner>/v<n>`, section 12.1). A name has no digest. It says
which version of which work is meant, not what that version holds.

Version 0.1 of this program named an object by its archive and identifier;
version 0.2 of the specification names it by its line alone, and the base
follows. The sections of the base come only from lines that are not key
logs (chapter [The sections of a world glue](40-world.md)): a draft's
identifier is local to its archive (section 10.1), and a key log has no
document versions (section 4.1).

    -- in Sheaf/Base.lean:
    import OpenSheaf.Impossible
    import Sheaf.Order

    namespace OpenSheaf.Sheaf

    /-- A named document version: an object, named by its identifier, and a
    document version number. -/
    structure Name where
      object : ObjectId
      doc : Nat
      deriving DecidableEq, Repr

## The order of deposit

A named document version comes after the earlier document versions of the
same object. The owner of the line numbers document versions from 1,
without gaps (section 4.2), so the order is that of the numbers. An object version holds every document version
deposited before it, since its inventory lists every earlier object
version, so the set of document versions it holds is closed downwards: an
open set.

Number 0 names no document version. The order keeps it apart, below no
other point and above none, so that the points need no subtype and the open
sets held by objects never contain it.

The reading order of the document versions (`history` in `object.json`) is
not this order. It may put a version found later before versions deposited
earlier, and a later object version may correct it, so it changes; the
order of deposit does not. The reading order is a structure on top of the
sheaf, not part of its base.

The order is called `deposit` in the code, not `history`, which is the
name of the reading order in `object.json` and of a field of the model's
well-formed objects.

    /-- The order of deposit: earlier document versions of the same object. -/
    def deposit : Order Name where
      le x y := x.object = y.object ∧ x.doc ≤ y.doc ∧ (x.doc = 0 → y.doc = 0)
      refl _ := ⟨rfl, Nat.le_refl _, id⟩
      trans := fun ⟨h2, h3, h4⟩ ⟨h2', h3', h4'⟩ =>
        ⟨h2.trans h2', Nat.le_trans h3 h3', fun h => h4' (h4 h)⟩

## The value at a point

The value at a named document version is its *content*: its files
(sources, renditions, change note, and any file that holds a note), and
for a collection its member list. The model compares content in this way
(`sameContent` in the chapter "Objects and their history" of the model):
files as a set, by path and digest, and the member list. A notice kept as a
file is content, by the model's choice there; adding one makes a new
document version.

The description and the status are not content. Section 4.2
lets a description-only version change them while the document version
stays the same. So they belong to object versions, not to named document
versions, and they are not values of this sheaf (see the introduction).

    variable {D : Type}

    /-- The content of a document version: its files, as a set, and its member
    list. -/
    structure Content (D : Type) where
      files : LogicalPath × D → Prop
      members : Option (Members D)

    /-- The content of an object version. -/
    def _root_.OpenSheaf.Version.content (v : Version D) : Content D :=
      ⟨fun f => f ∈ v.files, v.members⟩

    /-- The named document version held by an object version of `o`. -/
    def _root_.OpenSheaf.Obj.name (o : Obj D) (v : Version D) : Name :=
      ⟨o.id, v.documentVersion⟩

Two object versions have the same content, as a value, exactly when the
model says they have the same content.

    variable [DecidableEq D]

    theorem content_eq_iff {v u : Version D} :
        v.content = u.content ↔ sameContent v u = true := by
      rw [sameContent_iff]
      constructor
      · intro h
        have hf := congrArg Content.files h
        have hm := congrArg Content.members h
        exact ⟨fun f => by
          have := congrFun hf f
          simp only [Version.content] at this
          rw [this], hm⟩
      · rintro ⟨hf, hm⟩
        simp only [Version.content]
        rw [hm]
        congr 1
        funext f
        exact propext (hf f)

## Numbers and content

The rule of section 4.2 has two directions, and the model proves both, in
its chapter "What cannot happen": in a well-formed history, object versions
with the same document version have the same content
(`one_number_one_content`), and object versions with the same content have
the same document version (`one_content_one_number`). Within one history,
numbers and contents correspond one to one. The model also proves that the
numbers start at 1 and have no gaps (`doc_pos`, `no_gaps`), and that a
prefix of a well-formed history is well formed (`WellFormed.prefix`). The
next chapters use these facts.

    end OpenSheaf.Sheaf
