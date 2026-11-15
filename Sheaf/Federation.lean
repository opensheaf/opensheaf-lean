-- Generated from literate-sheaf/76-federation.md by opensheaf-literate: edit the document, not this file.
import Sheaf.Local

namespace OpenSheaf.Sheaf

variable {D : Type}

/-- **Every section extends.** A section over a set extends to any larger set:
the sheaf of sections is flasque. -/
theorem flasque {P V : Type} [Inhabited V] {U U' : P → Prop} (h : Sub U U') (s : Sec U V) :
    ∃ s' : Sec U' V, s'.restrict h = s := by
  classical
  refine ⟨fun x _ => if hx : U x then s x hx else default, ?_⟩
  funext x hx
  simp [Sec.restrict, hx]

/-- Two worlds side by side: the archives of the first, then those of the
second. -/
def union (w1 w2 : World D) : World D :=
  fun a => match w1 a with
    | some ar => some ar
    | none => w2 a

/-- No archive is in both. -/
def Disjoint (w1 w2 : World D) : Prop := ∀ a, w1 a = none ∨ w2 a = none

theorem lookup_union_left {w1 w2 : World D} {a : ArchiveId} {i : ObjectId} {e : Entry D}
    (h : lookup w1 a i = some e) : lookup (union w1 w2) a i = some e := by
  unfold lookup union at *
  cases h1 : w1 a with
  | none => rw [h1] at h; cases h
  | some ar => rw [h1] at h; exact h

theorem lookup_union_right {w1 w2 : World D} (hd : Disjoint w1 w2) {a : ArchiveId}
    {i : ObjectId} {e : Entry D} (h : lookup w2 a i = some e) :
    lookup (union w1 w2) a i = some e := by
  have h2 : w2 a ≠ none := by
    intro h2; unfold lookup at h; rw [h2] at h; cases h
  have h1 : w1 a = none := (hd a).resolve_right h2
  unfold lookup union at *
  rw [h1]; exact h

theorem lookup_union_cases {w1 w2 : World D} {a : ArchiveId} {i : ObjectId} {e : Entry D}
    (h : lookup (union w1 w2) a i = some e) :
    lookup w1 a i = some e ∨ lookup w2 a i = some e := by
  unfold lookup union at *
  cases h1 : w1 a with
  | none => rw [h1] at h; exact Or.inr h
  | some ar => rw [h1] at h; exact Or.inl h

/-- The copies of the two worlds that share a name have comparable histories. -/
def CrossAgree (w1 w2 : World D) : Prop :=
  ∀ b x m b' x' m', lookup w1 b x = some (.live m) → lookup w2 b' x' = some (.live m') →
    m.archive = m'.archive → m.id = m'.id → Comparable m.versions m'.versions

theorem union_copiesAgree {w1 w2 : World D} (h1 : CopiesAgree w1) (h2 : CopiesAgree w2)
    (hx : CrossAgree w1 w2) : CopiesAgree (union w1 w2) := by
  intro b x m b' x' m' hl hl' ha hi
  rcases lookup_union_cases hl with hl | hl <;> rcases lookup_union_cases hl' with hl' | hl'
  · exact h1 _ _ _ _ _ _ hl hl' ha hi
  · exact hx _ _ _ _ _ _ hl hl' ha hi
  · exact (hx _ _ _ _ _ _ hl' hl ha.symm hi.symm).symm
  · exact h2 _ _ _ _ _ _ hl hl' ha hi

variable [DecidableEq D] (hash : Hash D)

/-- Copies that agree, and well-formed histories, give compatible sections:
the argument of the main theorem, for any world. -/
theorem compatible_of_agree {w : World D}
    (hwf : ∀ b i c, lookup w b i = some (.live c) → WellFormed c.versions)
    (hca : CopiesAgree w) : Compatible (sections w) := by
  intro i j x ⟨a1, o1, k1, d1⟩ ⟨a2, o2, _, d2⟩
  have hc := hca _ _ _ _ _ _ i.live j.live (a1.symm.trans a2) (o1.symm.trans o2)
  simp only [sections, objSec]
  rcases hc with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hi : j.obj.versions = i.obj.versions.take i.version ++
        (i.obj.versions.drop i.version ++ t) := by rw [ht]; exact take_drop_append _ _ _
    exact docContent_agree (hwf _ _ _ j.live) hi (List.take_append_drop _ _).symm k1 d1 d2
  · have hj : i.obj.versions = j.obj.versions.take j.version ++
        (j.obj.versions.drop j.version ++ t) := by rw [ht]; exact take_drop_append _ _ _
    exact docContent_agree (hwf _ _ _ i.live) (List.take_append_drop _ _).symm hj k1 d1 d2

/-- **Federation.** Two worlds built separately by events, on different
archives, glue into one sheaf when the copies they share agree. -/
theorem federation {w1 w2 : World D}
    (hs1 : Events hash (fun _ => (none : Option (Archive D))) w1)
    (hs2 : Events hash (fun _ => (none : Option (Archive D))) w2)
    (hx : CrossAgree w1 w2) :
    ∃ g, Glues (sections (union w1 w2)) g ∧ ∀ g', Glues (sections (union w1 w2)) g' → g' = g := by
  apply sheaf
  apply compatible_of_agree
  · intro b i c hl
    rcases lookup_union_cases hl with hl | hl
    · exact ((Events.sound hash hs1).1 _ _ _ hl).history
    · exact ((Events.sound hash hs2).1 _ _ _ hl).history
  · exact union_copiesAgree (Events.copiesAgree hash hs1) (Events.copiesAgree hash hs2) hx

omit [DecidableEq D] in
/-- A source of the first world is a source of the union. -/
def Source.left {w1 w2 : World D} (i : Source w1) : Source (union w1 w2) :=
  ⟨i.archive, i.id, i.obj, lookup_union_left i.live, i.version⟩

omit [DecidableEq D] in
def Source.right {w1 w2 : World D} (hd : Disjoint w1 w2) (i : Source w2) :
    Source (union w1 w2) :=
  ⟨i.archive, i.id, i.obj, lookup_union_right hd i.live, i.version⟩

/-- The sections of the two worlds agree wherever both are defined. -/
def CrossCompatible (w1 w2 : World D) : Prop :=
  ∀ (i : Source w1) (j : Source w2) x (hi : cover w1 i x) (hj : cover w2 j x),
    sections w1 i x hi = sections w2 j x hj

/-- **Only pairs across need checking.** The union of two worlds built by
events is compatible exactly when the sections of the two worlds agree
where both are defined: pairs within a world need no check. -/
theorem federation_iff {w1 w2 : World D} (hd : Disjoint w1 w2)
    (hs1 : Events hash (fun _ => (none : Option (Archive D))) w1)
    (hs2 : Events hash (fun _ => (none : Option (Archive D))) w2) :
    Compatible (sections (union w1 w2)) ↔ CrossCompatible w1 w2 := by
  constructor
  · intro h i j x hi hj
    exact h (Source.left i) (Source.right hd j) x hi hj
  · intro h i j x hi hj
    have c1 := world_compatible hash hs1
    have c2 := world_compatible hash hs2
    rcases lookup_union_cases i.live with li | li <;> rcases lookup_union_cases j.live with lj | lj
    · exact c1 ⟨i.archive, i.id, i.obj, li, i.version⟩ ⟨j.archive, j.id, j.obj, lj, j.version⟩
        x hi hj
    · exact h ⟨i.archive, i.id, i.obj, li, i.version⟩ ⟨j.archive, j.id, j.obj, lj, j.version⟩
        x hi hj
    · exact (h ⟨j.archive, j.id, j.obj, lj, j.version⟩ ⟨i.archive, i.id, i.obj, li, i.version⟩
        x hj hi).symm
    · exact c2 ⟨i.archive, i.id, i.obj, li, i.version⟩ ⟨j.archive, j.id, j.obj, lj, j.version⟩
        x hi hj

omit [DecidableEq D] in
theorem heldIn_left {w1 w2 : World D} : Sub (HeldIn w1) (HeldIn (union w1 w2)) :=
  fun _ ⟨i, hx⟩ => ⟨Source.left i, hx⟩

omit [DecidableEq D] in
/-- **Each world keeps its section.** The glued section of the union restricts
to the glued section of the first world. -/
theorem union_restricts {w1 w2 : World D} {g : Sec (HeldIn (union w1 w2)) (Content D)}
    (hg : Glues (sections (union w1 w2)) g) : Glues (sections w1) (g.restrict heldIn_left) := by
  intro i
  funext x hx
  exact congrFun (congrFun (hg (Source.left i)) x) hx

end OpenSheaf.Sheaf
