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

theorem sameContent_symm {v u : Version D} (h : sameContent v u = true) :
    sameContent u v = true := by
  rw [sameContent_iff] at *
  exact ⟨fun f => (h.1 f).symm, h.2.symm⟩

theorem sameContent_trans {v u t : Version D} (h1 : sameContent v u = true)
    (h2 : sameContent u t = true) : sameContent v t = true := by
  rw [sameContent_iff] at *
  exact ⟨fun f => (h1.1 f).trans (h2.1 f), h1.2.trans h2.2⟩

/-- **One content, one number.** In a well-formed history, versions with the
same content hold the same document version. -/
theorem one_content_one_number {l : List (Version D)} (h : WellFormed l)
    {v u : Version D} (hv : v ∈ l) (hu : u ∈ l) (heq : sameContent v u = true) :
    v.documentVersion = u.documentVersion := by
  induction l using snoc_induction generalizing v u with
  | nil => cases hv
  | snoc l x ih =>
    obtain ⟨hwf, hx⟩ := h.init
    have key : ∀ y ∈ l, sameContent y x = true → y.documentVersion = x.documentVersion := by
      intro y hy hyx
      rcases hx with ⟨z, hz, hzx, hxz⟩ | ⟨hnew, _⟩
      · exact (ih hwf hy hz (sameContent_trans hyx (sameContent_symm hzx))).trans hxz.symm
      · rw [hnew y hy] at hyx; cases hyx
    simp only [List.mem_append, List.mem_singleton] at hv hu
    rcases hv with hv | rfl <;> rcases hu with hu | rfl
    · exact ih hwf hv hu heq
    · exact key v hv heq
    · exact (key u hu (sameContent_symm heq)).symm
    · rfl

/-- In a well-formed history, every document version is numbered from 1. -/
theorem doc_pos {l : List (Version D)} (h : WellFormed l) {v : Version D} (hv : v ∈ l) :
    1 ≤ v.documentVersion := by
  induction l using snoc_induction generalizing v with
  | nil => cases hv
  | snoc l x ih =>
    obtain ⟨hwf, hx⟩ := h.init
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact ih hwf hv
    · rcases hx with ⟨z, hz, _, hxz⟩ | ⟨_, hxn⟩
      · rw [hxz]; exact ih hwf hz
      · omega

/-- A prefix of a well-formed history is well formed. -/
theorem _root_.OpenSheaf.WellFormed.prefix {l t : List (Version D)} (h : WellFormed (l ++ t)) :
    WellFormed l := by
  intro i hi
  have := h i (by simp; omega)
  rwa [List.take_append_of_le_length (Nat.le_of_lt hi), List.getElem_append_left hi] at this

end OpenSheaf.Sheaf
