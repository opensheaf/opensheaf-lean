-- Generated from literate-sheaf/40-world.md by opensheaf-literate: edit the document, not this file.
import Sheaf.Object

namespace OpenSheaf.Sheaf

variable {D : Type}

/-- A source of sections: a live copy of a line, not a key log, kept
somewhere, and one of its object versions. -/
structure Source (w : World D) where
  archive : ArchiveId
  line : LineId
  obj : Obj D
  live : lookup w archive (.line line) = some (.live obj)
  kind : obj.kind ≠ .owner
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

variable [DecidableEq D] (E : Env D)

/-- For each line, a genesis record and the history its owner signs. -/
abbrev Histories (D : Type) := LineId → Option (Genesis D) × List (Version D)

/-- Owners sign the histories `H`, and no copy held in `w` collides with them. -/
def Honest (H : Histories D) (w : World D) : Prop :=
  (∀ l, SignsHistory E w l (H l).1 (H l).2) ∧ ∀ l, NoCollisionWith E w l (H l).1 (H l).2

omit [DecidableEq D] in
theorem Honest.one {H : Histories D} {w : World D} (h : Honest E H w) (l : LineId) :
    OneHistory E w l :=
  ⟨_, _, h.1 l, h.2 l⟩

omit [DecidableEq D] in
theorem Honest.back {H : Histories D} {w w' : World D} (hs : Steps w w')
    (h : Honest E H w') : Honest E H w :=
  ⟨fun l => (h.1 l).back E hs, fun l => (h.2 l).back E hs⟩

theorem honest_comparable {H : Histories D} {w w' : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w)
    (hs' : Events E (fun _ => (none : Option (Archive D))) w')
    (hh : Honest E H w) (hh' : Honest E H w') {b b' : ArchiveId} {l : LineId} {o o' : Obj D}
    (hl : lookup w b (.line l) = some (.live o)) (hl' : lookup w' b' (.line l) = some (.live o'))
    (hk : o.kind ≠ .owner) (hk' : o'.kind ≠ .owner) : Comparable o.versions o'.versions := by
  obtain ⟨_, h⟩ := Events.prefix_history E hs (hh.1 l) (hh.2 l) hl hk
  obtain ⟨_, h'⟩ := Events.prefix_history E hs' (hh'.1 l) (hh'.2 l) hl' hk'
  have e1 := List.take_append_drop o.versions.length (H l).2
  have e2 := List.take_append_drop o'.versions.length (H l).2
  rw [← h] at e1; rw [← h'] at e2
  exact comparable_of_prefixes e1.symm e2.symm

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

/-- Live objects, stored under their identifiers, with well-formed histories
unless they are key logs. -/
def WFObjects (w : World D) : Prop :=
  ∀ b i c, lookup w b i = some (.live c) → c.id = i ∧ (c.kind ≠ .owner → WellFormed c.versions)

/-- Copies that agree, and well-formed histories, give compatible sections. -/
theorem compatible_of_agree {w : World D} (hwf : WFObjects w)
    (hca : ∀ l, CopiesAgree w l) : Compatible (sections w) := by
  intro i j x ⟨o1, k1, d1⟩ ⟨o2, _, d2⟩
  have hl : i.line = j.line := by
    have h1 := (hwf _ _ _ i.live).1
    have h2 := (hwf _ _ _ j.live).1
    exact ObjectId.line.inj (h1.symm.trans (o1.symm.trans (o2.trans h2)))
  have hjl := j.live
  rw [← hl] at hjl
  have hc := hca i.line _ _ _ _ i.live hjl i.kind j.kind
  simp only [sections, objSec]
  rcases hc with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hi : j.obj.versions = i.obj.versions.take i.version ++
        (i.obj.versions.drop i.version ++ t) := by rw [ht]; exact take_drop_append _ _ _
    exact docContent_agree ((hwf _ _ _ j.live).2 j.kind) hi (List.take_append_drop _ _).symm k1 d1 d2
  · have hj : i.obj.versions = j.obj.versions.take j.version ++
        (j.obj.versions.drop j.version ++ t) := by rw [ht]; exact take_drop_append _ _ _
    exact docContent_agree ((hwf _ _ _ i.live).2 i.kind) (List.take_append_drop _ _).symm hj k1 d1 d2

theorem SoundWorld.wfObjects {w : World D} (hw : SoundWorld E w) : WFObjects w :=
  fun _ _ _ hl => ⟨(hw.1 _ _ _ hl).id, (hw.1 _ _ _ hl).history⟩

/-- **The sections of a world are compatible**, when its owners are honest. -/
theorem world_compatible {w : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w) {H : Histories D} (hh : Honest E H w) :
    Compatible (sections w) :=
  compatible_of_agree (SoundWorld.wfObjects E (Events.sound E hs)) fun l => Events.copiesAgree E hs (hh.one E l)

/-- **The sections of a world built by events glue** into exactly one
section over the named document versions it holds, when its owners are
honest: one content for each, whichever copy it is read from. -/
theorem world_glues {w : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w) {H : Histories D} (hh : Honest E H w) :
    ∃ g, Glues (sections w) g ∧ ∀ g', Glues (sections w) g' → g' = g :=
  sheaf (world_compatible E hs hh)

/-- **Only a fork stops the sections from gluing.** If the sections of a world
built by events are not compatible, two copies of some line, neither of which
extends the other, both end in versions signed with current keys of the
owner's key log as the world holds it. -/
theorem no_glue_fork {w : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w) (hnc : ¬ Compatible (sections w)) :
    ∃ l b b' o o', lookup w b (.line l) = some (.live o) ∧
      lookup w b' (.line l) = some (.live o') ∧ ¬ Comparable o.versions o'.versions ∧
      HeadSigned E w l o ∧ HeadSigned E w l o' := by
  apply Classical.byContradiction
  intro hno
  apply hnc
  apply compatible_of_agree (SoundWorld.wfObjects E (Events.sound E hs))
  intro l b b' o o' hl hl' hk hk'
  apply Classical.byContradiction
  intro hfork
  obtain ⟨h1, h2, _⟩ := Events.fork_signed E hs hl hl' hk hk' hfork
  exact hno ⟨l, b, b', o, o', hl, hl', hfork, h1, h2⟩

/-- A live copy of a line, not a key log, kept anywhere, holds the named
document version `x` with the object version `v`. -/
def Holds (w : World D) (x : Name) (v : Version D) : Prop :=
  ∃ b l c, lookup w b (.line l) = some (.live c) ∧ c.kind ≠ .owner ∧ v ∈ c.versions ∧
    c.name v = x

/-- What the later chapters need of a world: a sound world, whose copies of
each line agree. -/
abbrev Kept (w : World D) : Prop := SoundWorld E w ∧ ∀ l, CopiesAgree w l

theorem Events.kept {w : World D} (hs : Events E (fun _ => (none : Option (Archive D))) w)
    {H : Histories D} (hh : Honest E H w) : Kept E w :=
  ⟨Events.sound E hs, fun l => Events.copiesAgree E hs (hh.one E l)⟩

theorem heldIn_of_live {w : World D} (hw : SoundWorld E w) {b : ArchiveId} {l : LineId}
    {c : Obj D} (hl : lookup w b (.line l) = some (.live c)) (hk : c.kind ≠ .owner)
    {v : Version D} (hv : v ∈ c.versions) : HeldIn w (c.name v) :=
  ⟨⟨b, l, c, hl, hk, c.versions.length⟩,
    (covers_iff ((hw.1 _ _ _ hl).history hk) _ _).mpr
      ⟨v, by rw [List.take_length]; exact hv, rfl⟩⟩

theorem heldIn_iff {w : World D} (hw : SoundWorld E w) (x : Name) :
    HeldIn w x ↔ ∃ v, Holds w x v := by
  constructor
  · rintro ⟨⟨b, l, c, hl, hk, n⟩, hx⟩
    obtain ⟨v, hv, rfl⟩ := (covers_iff ((hw.1 _ _ _ hl).history hk) n _).mp hx
    exact ⟨v, b, l, c, hl, hk, List.mem_of_mem_take hv, rfl⟩
  · rintro ⟨v, b, l, c, hl, hk, hv, rfl⟩
    exact heldIn_of_live E hw hl hk hv

/-- Two versions holding the same named document version have the same
content. -/
theorem holds_agree {w : World D} (hw : SoundWorld E w) (hca : ∀ l, CopiesAgree w l)
    {x : Name} {v v' : Version D} (h : Holds w x v) (h' : Holds w x v') :
    sameContent v v' = true := by
  obtain ⟨b, l, c, hl, hk, hv, rfl⟩ := h
  obtain ⟨b', l', c', hl', hk', hv', hn⟩ := h'
  simp only [Obj.name, Name.mk.injEq] at hn
  obtain ⟨hi, hd⟩ := hn
  have hll : l' = l := by
    have h1 := (hw.1 _ _ _ hl).id
    have h2 := (hw.1 _ _ _ hl').id
    exact ObjectId.line.inj (h2.symm.trans (hi.trans h1))
  subst hll
  rcases hca l' _ _ _ _ hl' hl hk' hk with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact one_number_one_content ((hw.1 _ _ _ hl).history hk)
      (hv) (by rw [ht]; exact List.mem_append_left _ hv') hd.symm
  · exact one_number_one_content ((hw.1 _ _ _ hl').history hk')
      (by rw [ht]; exact List.mem_append_left _ hv) hv' hd.symm

/-- The value of a glued section is the content of any version holding the
point. -/
theorem glue_value {w : World D} (hw : SoundWorld E w) {g : Sec (HeldIn w) (Content D)}
    (hg : Glues (sections w) g) {x : Name} {v : Version D} (h : Holds w x v)
    (hx : HeldIn w x) : g x hx = v.content := by
  obtain ⟨b, l, c, hl, hk, hv, rfl⟩ := h
  have hwf := (hw.1 _ _ _ hl).history hk
  have hc : Covers c c.versions.length (c.name v) :=
    (covers_iff hwf _ _).mpr ⟨v, by rw [List.take_length]; exact hv, rfl⟩
  have := congrFun (congrFun (hg ⟨b, l, c, hl, hk, c.versions.length⟩) (c.name v)) hc
  exact this.trans (objSec_piece hwf (by rw [List.take_length]; exact hv) hc)

/-- A new number is new content: below a point, no earlier document version of
the same object has the same content. -/
def NewContent : LocalCond deposit (Content D) :=
  fun x f => ∀ y (hy : deposit.le y x), y.doc ≠ x.doc → f y hy ≠ f x (deposit.refl x)

/-- Each object version satisfies it (section 4.2). -/
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
    (hs : Events E (fun _ => (none : Option (Archive D))) w) {g : Sec (HeldIn w) (Content D)}
    (hg : Glues (sections w) g) : g.Satisfies deposit (heldIn_open w) NewContent :=
  glue_satisfies deposit (fun i => covers_open i.obj i.version) hg NewContent
    fun i => objSec_newContent (((Events.sound E hs).1 _ _ _ i.live).history i.kind) i.version

end OpenSheaf.Sheaf
