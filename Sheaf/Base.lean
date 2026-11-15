-- Generated from literate-sheaf/20-base.md by opensheaf-literate: edit the document, not this file.
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

/-- The order of history: earlier document versions of the same object. -/
def history : Order Name where
  le x y := x.archive = y.archive ∧ x.object = y.object ∧ x.doc ≤ y.doc ∧ (x.doc = 0 → y.doc = 0)
  refl _ := ⟨rfl, rfl, Nat.le_refl _, id⟩
  trans := fun ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩ =>
    ⟨h1.trans h1', h2.trans h2', Nat.le_trans h3 h3', fun h => h4' (h4 h)⟩

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

end OpenSheaf.Sheaf
