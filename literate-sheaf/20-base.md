# Named document versions

The points of the space are *named document versions*: an object, named by
its archive and identifier, and a document version number (section 7.3 of
the specification). A name has no digest. It says which version of which
work is meant, not what that version holds.

    -- in Sheaf/Base.lean:
    import OpenSheaf.Impossible
    import Sheaf.Order

    namespace OpenSheaf.Sheaf

    /-- A named document version: an object, named by its archive and identifier,
    and a document version number. -/
    structure Name where
      archive : ArchiveId
      object : ObjectId
      doc : Nat
      deriving DecidableEq, Repr

## The order of history

A named document version comes after the earlier document versions of the
same object. The archive numbers document versions in the order in which
they are deposited, from 1 and without gaps (section 7.3), so the order is
that of the numbers. An object version holds every document version
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

    /-- The order of history: earlier document versions of the same object. -/
    def history : Order Name where
      le x y := x.archive = y.archive ∧ x.object = y.object ∧ x.doc ≤ y.doc ∧ (x.doc = 0 → y.doc = 0)
      refl _ := ⟨rfl, rfl, Nat.le_refl _, id⟩
      trans := fun ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩ =>
        ⟨h1.trans h1', h2.trans h2', Nat.le_trans h3 h3', fun h => h4' (h4 h)⟩

## The value at a point

The value at a named document version is its *content*: the files of the
document's own (sources, renditions, change note), and for a collection its
member list. The model compares content in this way (`sameContent` in the
chapter "Objects and their history" of the model): files as a set, by path
and digest, and the member list.

The description, the status and the notices are not content. Section 7.3
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
      ⟨o.archive, o.id, v.documentVersion⟩

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

The rule of section 7.3 has two directions, and the model proves both, in
its chapter "What cannot happen": in a well-formed history, object versions
with the same document version have the same content
(`one_number_one_content`), and object versions with the same content have
the same document version (`one_content_one_number`). Within one history,
numbers and contents correspond one to one. The model also proves that the
numbers start at 1 and have no gaps (`doc_pos`, `no_gaps`), and that a
prefix of a well-formed history is well formed (`WellFormed.prefix`). The
next chapters use these facts.

    end OpenSheaf.Sheaf
