-- Generated from literate-sheaf/40-world.md by opensheaf-literate: edit the document, not this file.
import Sheaf.Object
import OpenSheaf.Copies

namespace OpenSheaf.Sheaf

variable {D : Type}

/-- One list is a prefix of the other. -/
def Comparable {α : Type} (l l' : List α) : Prop :=
  (∃ t, l' = l ++ t) ∨ (∃ t, l = l' ++ t)

theorem Comparable.symm {α : Type} {l l' : List α} (h : Comparable l l') : Comparable l' l :=
  h.elim Or.inr Or.inl

theorem comparable_of_prefixes {α : Type} {l1 l2 t1 t2 L : List α} (h1 : L = l1 ++ t1)
    (h2 : L = l2 ++ t2) : Comparable l1 l2 := by
  rcases List.append_eq_append_iff.mp (h1.symm.trans h2) with ⟨a, ha, _⟩ | ⟨c, hc, _⟩
  · exact Or.inl ⟨a, ha⟩
  · exact Or.inr ⟨c, hc⟩

/-- Comparable with a list, comparable with each of its prefixes. -/
theorem Comparable.of_prefix {α : Type} {m o L t : List α} (h : Comparable m L)
    (ho : L = o ++ t) : Comparable m o := by
  rcases h with ⟨t', ht'⟩ | ⟨t', ht'⟩
  · exact comparable_of_prefixes ht' ho
  · exact Or.inr ⟨t ++ t', by rw [ht', ho, List.append_assoc]⟩

/-- **Copies agree.** Any two live objects with the same name, wherever they
are kept, have histories of which one is a prefix of the other. -/
def CopiesAgree (w : World D) : Prop :=
  ∀ b x m b' x' m', lookup w b x = some (.live m) → lookup w b' x' = some (.live m') →
    m.archive = m'.archive → m.id = m'.id → Comparable m.versions m'.versions

theorem copiesAgree_setEntry {w : World D} {a : ArchiveId} {ar : Archive D}
    {oid : ObjectId} {o : Obj D} (ha : w a = some ar) (hw : CopiesAgree w)
    (hnew : ∀ b x m, lookup w b x = some (.live m) → ¬ (b = a ∧ x = oid) →
      m.archive = o.archive → m.id = o.id → Comparable m.versions o.versions) :
    CopiesAgree (setEntry w a oid (.live o)) := by
  intro b x m b' x' m' hl hl' h1 h2
  rw [lookup_setEntry ha] at hl hl'
  by_cases hc : b = a ∧ x = oid <;> by_cases hc' : b' = a ∧ x' = oid
  · rw [if_yes hc] at hl; rw [if_yes hc'] at hl'
    cases hl; cases hl'
    exact Or.inl ⟨[], by simp⟩
  · rw [if_yes hc] at hl; rw [if_no hc'] at hl'
    cases hl
    exact (hnew _ _ _ hl' hc' h1.symm h2.symm).symm
  · rw [if_no hc] at hl; rw [if_yes hc'] at hl'
    cases hl'
    exact hnew _ _ _ hl hc h1 h2
  · rw [if_no hc] at hl; rw [if_no hc'] at hl'
    exact hw _ _ _ _ _ _ hl hl' h1 h2

variable (hash : Hash D)

/-- A takedown keeps copies in agreement: it only removes one. -/
theorem takedown_copiesAgree {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) (hw : CopiesAgree w) :
    CopiesAgree (takedown hash w a oid o) :=
  fun _ _ _ _ _ _ h h' => hw _ _ _ _ _ _ (lookup_takedown hash hl h).2 (lookup_takedown hash hl h').2

variable [DecidableEq D]

/-- Valid steps keep copies in agreement. -/
theorem ValidStep.copiesAgree {w w' : World D} (hs : ValidStep hash w w')
    (hsound : SoundWorld hash w) (hmir : MirrorsOk w) (hw : CopiesAgree w) :
    CopiesAgree w' := by
  cases hs with
  | newArchive a ar ha hempty =>
    intro b x m b' x' m' hl hl'
    rw [lookup_newArchive ha hempty] at hl hl'
    exact hw _ _ _ _ _ _ hl hl'
  | create a ar oid o ha ho hwf _ hhome _ =>
    have hnone : lookup w a oid = none := by simp [lookup, ha, ho]
    apply copiesAgree_setEntry ha hw
    intro b x m hl hne h1 h2
    have hmid : m.id = x := (hsound.1 _ _ _ hl).id
    rcases hhome with hh | ⟨orig, hlo, harch, t, ht⟩
    · exfalso
      by_cases hb : b = a
      · exact hne ⟨hb, by rw [← hmid, h2, hwf.id]⟩
      · have hma : m.archive = a := h1.trans hh
        have := (hmir b x m hl (by rw [hma]; exact fun e => hb e.symm)).1
        rw [hma, h2, hwf.id] at this
        exact this hnone
    · have hoid : orig.id = o.id := (hsound.1 _ _ _ hlo).id
      exact (hw _ _ _ _ _ _ hl hlo (h1.trans harch.symm) (h2.trans hoid.symm)).of_prefix ht
  | append a ar oid o y ha ho _ _ _ _ _ hhome _ =>
    have hlo : lookup w a oid = some (.live o) := by simp [lookup, ha, ho]
    have hoid : o.id = oid := (hsound.1 _ _ _ hlo).id
    apply copiesAgree_setEntry ha hw
    intro b x m hl hne h1 h2
    have hmid : m.id = x := (hsound.1 _ _ _ hl).id
    rcases hhome with hh | ⟨orig, hlo', harch, t, ht⟩
    · by_cases hb : b = a
      · exact absurd ⟨hb, by rw [← hmid]; exact h2.trans hoid⟩ hne
      · have hma : m.archive = a := h1.trans hh
        obtain ⟨_, hpre⟩ := hmir b x m hl (by rw [hma]; exact fun e => hb e.symm)
        have hlo2 : lookup w m.archive m.id = some (.live o) := by
          rw [hma, show m.id = oid from h2.trans hoid]; exact hlo
        obtain ⟨_, t, ht⟩ := hpre o hlo2
        exact Or.inl ⟨t ++ [y], by simp [Obj.append, ht]⟩
    · have hoid' : orig.id = (o.append y).id := (hsound.1 _ _ _ hlo').id
      exact (hw _ _ _ _ _ _ hl hlo' (h1.trans harch.symm) (h2.trans hoid'.symm)).of_prefix ht

/-- What events keep, together. -/
def Kept (w : World D) : Prop := SoundWorld hash w ∧ MirrorsOk w ∧ CopiesAgree w

theorem Event.kept {w w' : World D} (he : Event hash w w') (hw : Kept hash w) :
    Kept hash w' := by
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨he.sound hash h1, he.mirrorsOk hash h2, ?_⟩
  cases he with
  | step hs => exact ValidStep.copiesAgree hash hs h1 h2 h3
  | takedown a oid o hl => exact takedown_copiesAgree hash hl h3

/-- **Copies agree in every world built by events.** -/
theorem Events.copiesAgree {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) : CopiesAgree w :=
  (hs.invariant _ (fun he hw => Event.kept hash he hw)
    ⟨SoundWorld.empty hash, fun _ _ _ h => by simp [lookup] at h,
     fun _ _ _ _ _ _ h => by simp [lookup] at h⟩).2.2

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

omit [DecidableEq D] in
theorem heldIn_open (w : World D) : history.IsOpen (HeldIn w) :=
  history.union_open fun i => held_open i.obj i.version

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
