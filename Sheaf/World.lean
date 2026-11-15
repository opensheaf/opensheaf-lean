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
abbrev cover (w : World D) (i : Source w) : Name → Prop := Covers i.obj i.version

/-- The section of a source. -/
abbrev sections (w : World D) (i : Source w) : Sec (cover w i) (Content D) :=
  objSec i.obj i.version

/-- The named document versions held anywhere in a world. -/
def HeldIn (w : World D) : Name → Prop := Union (cover w)

theorem heldIn_open (w : World D) : deposit.IsOpen (HeldIn w) :=
  deposit.union_open fun i => covers_open i.obj i.version

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

/-- Copies that agree, and well-formed histories, give compatible sections. -/
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

/-- **The sections of a world are compatible.** -/
theorem world_compatible {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) :
    Compatible (sections w) :=
  compatible_of_agree (fun _ _ _ hl => ((Events.sound hash hs).1 _ _ _ hl).history)
    (Events.copiesAgree hash hs)

/-- **The sections of a world built by events glue** into exactly one
section over the named document versions it holds: one content for each,
whichever copy it is read from. -/
theorem world_glues {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) :
    ∃ g, Glues (sections w) g ∧ ∀ g', Glues (sections w) g' → g' = g :=
  sheaf (world_compatible hash hs)

/-- A live copy, kept anywhere, holds the named document version `x` with the
object version `v`. -/
def Holds (w : World D) (x : Name) (v : Version D) : Prop :=
  ∃ b i c, lookup w b i = some (.live c) ∧ v ∈ c.versions ∧ c.name v = x

/-- What the model keeps through every event. -/
abbrev Kept (w : World D) : Prop := SoundWorld hash w ∧ MirrorsOk w ∧ CopiesAgree w

theorem Events.kept {w : World D} (hs : Events hash (fun _ => (none : Option (Archive D))) w) :
    Kept hash w :=
  ⟨Events.sound hash hs, Events.mirrorsOk hash hs, Events.copiesAgree hash hs⟩

theorem heldIn_of_live {w : World D} (hw : SoundWorld hash w) {b : ArchiveId} {i : ObjectId}
    {c : Obj D} (hl : lookup w b i = some (.live c)) {v : Version D} (hv : v ∈ c.versions) :
    HeldIn w (c.name v) :=
  ⟨⟨b, i, c, hl, c.versions.length⟩,
    (covers_iff (hw.1 _ _ _ hl).history _ _).mpr ⟨v, by rw [List.take_length]; exact hv, rfl⟩⟩

theorem heldIn_iff {w : World D} (hw : SoundWorld hash w) (x : Name) :
    HeldIn w x ↔ ∃ v, Holds w x v := by
  constructor
  · rintro ⟨⟨b, i, c, hl, n⟩, hx⟩
    obtain ⟨v, hv, rfl⟩ := (covers_iff (hw.1 _ _ _ hl).history n _).mp hx
    exact ⟨v, b, i, c, hl, List.mem_of_mem_take hv, rfl⟩
  · rintro ⟨v, b, i, c, hl, hv, rfl⟩
    exact heldIn_of_live hash hw hl hv

/-- Two versions holding the same named document version have the same
content. -/
theorem holds_agree {w : World D} (hw : SoundWorld hash w) (hca : CopiesAgree w) {x : Name}
    {v v' : Version D} (h : Holds w x v) (h' : Holds w x v') : sameContent v v' = true := by
  obtain ⟨b, i, c, hl, hv, rfl⟩ := h
  obtain ⟨b', i', c', hl', hv', hn⟩ := h'
  simp only [Obj.name, Name.mk.injEq] at hn
  obtain ⟨ha, hi, hd⟩ := hn
  rcases hca _ _ _ _ _ _ hl' hl ha hi with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact one_number_one_content (hw.1 _ _ _ hl).history
      (hv) (by rw [ht]; exact List.mem_append_left _ hv') hd.symm
  · exact one_number_one_content (hw.1 _ _ _ hl').history
      (by rw [ht]; exact List.mem_append_left _ hv) hv' hd.symm

/-- The value of a glued section is the content of any version holding the
point. -/
theorem glue_value {w : World D} (hw : SoundWorld hash w) {g : Sec (HeldIn w) (Content D)}
    (hg : Glues (sections w) g) {x : Name} {v : Version D} (h : Holds w x v)
    (hx : HeldIn w x) : g x hx = v.content := by
  obtain ⟨b, i, c, hl, hv, rfl⟩ := h
  have hwf := (hw.1 _ _ _ hl).history
  have hc : Covers c c.versions.length (c.name v) :=
    (covers_iff hwf _ _).mpr ⟨v, by rw [List.take_length]; exact hv, rfl⟩
  have := congrFun (congrFun (hg ⟨b, i, c, hl, c.versions.length⟩) (c.name v)) hc
  exact this.trans (objSec_piece hwf (by rw [List.take_length]; exact hv) hc)

/-- A new number is new content: below a point, no earlier document version of
the same object has the same content. -/
def NewContent : LocalCond deposit (Content D) :=
  fun x f => ∀ y (hy : deposit.le y x), y.doc ≠ x.doc → f y hy ≠ f x (deposit.refl x)

/-- Each object version satisfies it (section 7.3). -/
theorem objSec_newContent {o : Obj D} (hwf : WellFormed o.versions) (n : Nat) :
    (objSec o n).Satisfies deposit (covers_open o n) NewContent := by
  intro x hx y hy hne heq
  have hyx := covers_open o n hy hx
  obtain ⟨v, hv, rfl⟩ := (covers_iff hwf n x).mp hx
  obtain ⟨u, hu, rfl⟩ := (covers_iff hwf n y).mp hyx
  have heq' : objSec o n (o.name u) hyx = objSec o n (o.name v) hx := heq
  rw [objSec_piece hwf hu, objSec_piece hwf hv] at heq'
  exact hne (one_content_one_number hwf (List.mem_of_mem_take hu)
    (List.mem_of_mem_take hv) (content_eq_iff.mp heq'))

/-- **So does the glued section**, which takes its values from many copies. -/
theorem world_newContent {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) {g : Sec (HeldIn w) (Content D)}
    (hg : Glues (sections w) g) : g.Satisfies deposit (heldIn_open w) NewContent :=
  glue_satisfies deposit (fun i => covers_open i.obj i.version) hg NewContent
    fun i => objSec_newContent ((Events.sound hash hs).1 _ _ _ i.live).history i.version

end OpenSheaf.Sheaf
