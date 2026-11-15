-- Generated from literate-sheaf/40-world.md by opensheaf-literate: edit the document, not this file.
import Sheaf.Object

namespace OpenSheaf.Sheaf

variable {D : Type}

/-- A source of sections: a live object kept somewhere, and one of its object
versions. -/
structure Source (w : World D) where
  archive : ArchiveId
  id : ObjectId
  obj : Obj D
  live : lookup w archive id = some (.live obj)
  version : Nat

/-- The named document versions a source holds. -/
abbrev cover (w : World D) (i : Source w) : Name → Prop := Held i.obj i.version

/-- The section of a source. -/
abbrev sections (w : World D) (i : Source w) : Sec (cover w i) (Content D) :=
  objSec i.obj i.version

/-- The named document versions held anywhere in a world. -/
def HeldIn (w : World D) : Name → Prop := Union (cover w)

theorem heldIn_open (w : World D) : history.IsOpen (HeldIn w) :=
  history.union_open fun i => held_open i.obj i.version

variable [DecidableEq D] (hash : Hash D)

omit [DecidableEq D] in
theorem take_drop_append (l t : List (Version D)) (n : Nat) :
    l ++ t = l.take n ++ (l.drop n ++ t) := by
  rw [← List.append_assoc, List.take_append_drop]

theorem docContent_agree {L l1 l2 t1 t2 : List (Version D)} (hL : WellFormed L)
    (h1 : L = l1 ++ t1) (h2 : L = l2 ++ t2) {k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ docCount l1)
    (hk' : k ≤ docCount l2) : docContent l1 k = docContent l2 k := by
  have hw1 : WellFormed l1 := by subst h1; exact hL.prefix
  obtain ⟨u, hu, huk⟩ := no_gaps hw1 hk1 hk
  have huL : u ∈ L := by rw [h1]; exact List.mem_append_left _ hu
  rw [docContent_eq hL h1 hk1 hk huL huk, docContent_eq hL h2 hk1 hk' huL huk]

/-- **The sections of a world are compatible.** -/
theorem world_compatible {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) :
    Compatible (sections w) := by
  intro i j x ⟨a1, o1, k1, d1⟩ ⟨a2, o2, _, d2⟩
  have hsound := Events.sound hash hs
  have hc := Events.copiesAgree hash hs _ _ _ _ _ _ i.live j.live
    (a1.symm.trans a2) (o1.symm.trans o2)
  simp only [sections, objSec]
  rcases hc with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hL := (hsound.1 _ _ _ j.live).history
    have hi : j.obj.versions = i.obj.versions.take i.version ++
        (i.obj.versions.drop i.version ++ t) := by rw [ht]; exact take_drop_append _ _ _
    exact docContent_agree hL hi (List.take_append_drop _ _).symm k1 d1 d2
  · have hL := (hsound.1 _ _ _ i.live).history
    have hj : i.obj.versions = j.obj.versions.take j.version ++
        (j.obj.versions.drop j.version ++ t) := by rw [ht]; exact take_drop_append _ _ _
    exact docContent_agree hL (List.take_append_drop _ _).symm hj k1 d1 d2

/-- **A world built by events is a sheaf.** Its sections glue into exactly one
section over the named document versions it holds: one content for each,
whichever copy it is read from. -/
theorem world_sheaf {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) :
    ∃ g, Glues (sections w) g ∧ ∀ g', Glues (sections w) g' → g' = g :=
  sheaf (world_compatible hash hs)

/-- A new number is new content: below a point, no earlier document version of
the same object has the same content. -/
def NewContent : LocalCond history (Content D) :=
  fun x f => ∀ y (hy : history.le y x), y.doc ≠ x.doc → f y hy ≠ f x (history.refl x)

/-- Each object version satisfies it (section 7.3). -/
theorem objSec_newContent {o : Obj D} (hwf : WellFormed o.versions) (n : Nat) :
    (objSec o n).Satisfies history (held_open o n) NewContent := by
  intro x hx y hy hne heq
  have hyx := held_open o n hy hx
  obtain ⟨v, hv, rfl⟩ := (held_iff hwf n x).mp hx
  obtain ⟨u, hu, rfl⟩ := (held_iff hwf n y).mp hyx
  have heq' : objSec o n (o.name u) hyx = objSec o n (o.name v) hx := heq
  rw [objSec_piece hwf hu, objSec_piece hwf hv] at heq'
  exact hne (one_content_one_number hwf (List.mem_of_mem_take hu)
    (List.mem_of_mem_take hv) (content_eq_iff.mp heq'))

/-- **So does the glued section**, which takes its values from many copies. -/
theorem world_newContent {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) {g : Sec (HeldIn w) (Content D)}
    (hg : Glues (sections w) g) : g.Satisfies history (heldIn_open w) NewContent :=
  glue_satisfies history (fun i => held_open i.obj i.version) hg NewContent
    fun i => objSec_newContent ((Events.sound hash hs).1 _ _ _ i.live).history i.version

end OpenSheaf.Sheaf
