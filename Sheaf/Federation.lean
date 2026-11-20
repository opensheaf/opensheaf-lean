-- Generated from literate-sheaf/76-federation.md by opensheaf-literate: edit the document, not this file.
import Sheaf.Local

namespace OpenSheaf.Sheaf

variable {D : Type}

/-- Two worlds side by side: the archives of the first, then those of the
second. -/
def World.union (w1 w2 : World D) : World D :=
  fun a => match w1 a with
    | some ar => some ar
    | none => w2 a

/-- No archive is in both worlds. -/
def SeparateWorlds (w1 w2 : World D) : Prop := ∀ a, w1 a = none ∨ w2 a = none

theorem lookup_union_left {w1 w2 : World D} {a : ArchiveId} {i : ObjectId} {e : Entry D}
    (h : lookup w1 a i = some e) : lookup (World.union w1 w2) a i = some e := by
  unfold lookup World.union at *
  cases h1 : w1 a with
  | none => rw [h1] at h; cases h
  | some ar => rw [h1] at h; exact h

theorem lookup_union_right {w1 w2 : World D} (hd : SeparateWorlds w1 w2) {a : ArchiveId}
    {i : ObjectId} {e : Entry D} (h : lookup w2 a i = some e) :
    lookup (World.union w1 w2) a i = some e := by
  have h2 : w2 a ≠ none := by
    intro h2; unfold lookup at h; rw [h2] at h; cases h
  have h1 : w1 a = none := (hd a).resolve_right h2
  unfold lookup World.union at *
  rw [h1]; exact h

theorem lookup_union_cases {w1 w2 : World D} {a : ArchiveId} {i : ObjectId} {e : Entry D}
    (h : lookup (World.union w1 w2) a i = some e) :
    lookup w1 a i = some e ∨ lookup w2 a i = some e := by
  unfold lookup World.union at *
  cases h1 : w1 a with
  | none => rw [h1] at h; exact Or.inr h
  | some ar => rw [h1] at h; exact Or.inl h

theorem archive_of_lookup {w : World D} {a : ArchiveId} {i : ObjectId} {e : Entry D}
    (h : lookup w a i = some e) : w a ≠ none := by
  obtain ⟨ar, ha⟩ := lookup_some_archive h
  rw [ha]; simp

variable [DecidableEq D] (E : Env D)

theorem copies_comparable {w1 w2 : World D}
    (hs1 : Events E (fun _ => (none : Option (Archive D))) w1)
    (hs2 : Events E (fun _ => (none : Option (Archive D))) w2) {H : Histories D}
    (hh1 : Honest E H w1) (hh2 : Honest E H w2) {l : LineId}
    {b b' : ArchiveId} {o o' : Obj D} (hl : lookup w1 b (.line l) = some (.live o))
    (hl' : lookup w2 b' (.line l) = some (.live o')) (hk : o.kind ≠ .owner)
    (hk' : o'.kind ≠ .owner) : Comparable o.versions o'.versions :=
  honest_comparable E hs1 hs2 hh1 hh2 hl hl' hk hk'

/-- **Separate worlds glue**, when owners are honest. -/
theorem separate_glue {w1 w2 : World D}
    (hs1 : Events E (fun _ => (none : Option (Archive D))) w1)
    (hs2 : Events E (fun _ => (none : Option (Archive D))) w2) {H : Histories D}
    (hh1 : Honest E H w1) (hh2 : Honest E H w2) :
    ∃ g, Glues (sections (World.union w1 w2)) g ∧
      ∀ g', Glues (sections (World.union w1 w2)) g' → g' = g := by
  apply sheaf
  apply compatible_of_agree
  · intro b i c hl
    rcases lookup_union_cases hl with hl | hl
    · exact SoundWorld.wfObjects E (Events.sound E hs1) _ _ _ hl
    · exact SoundWorld.wfObjects E (Events.sound E hs2) _ _ _ hl
  · intro l b b' m m' hl hl' hk hk'
    rcases lookup_union_cases hl with hl | hl <;> rcases lookup_union_cases hl' with hl' | hl'
    · exact Events.copiesAgree E hs1 (hh1.one E l) _ _ _ _ hl hl' hk hk'
    · exact copies_comparable E hs1 hs2 hh1 hh2 hl hl' hk hk'
    · exact (copies_comparable E hs1 hs2 hh1 hh2 hl' hl hk' hk).symm
    · exact Events.copiesAgree E hs2 (hh2.one E l) _ _ _ _ hl hl' hk hk'

omit [DecidableEq D] in
def Source.left {w1 w2 : World D} (i : Source w1) : Source (World.union w1 w2) :=
  ⟨i.archive, i.line, i.obj, lookup_union_left i.live, i.kind, i.version⟩

omit [DecidableEq D] in
def Source.right {w1 w2 : World D} (hd : SeparateWorlds w1 w2) (i : Source w2) :
    Source (World.union w1 w2) :=
  ⟨i.archive, i.line, i.obj, lookup_union_right hd i.live, i.kind, i.version⟩

omit [DecidableEq D] in
theorem union_restricts_left {w1 w2 : World D}
    {g : Sec (HeldIn (World.union w1 w2)) (Content D)}
    (hg : Glues (sections (World.union w1 w2)) g) :
    Glues (sections w1) (g.restrict fun _ ⟨i, hx⟩ => ⟨Source.left i, hx⟩) := by
  intro i
  funext x hx
  exact congrFun (congrFun (hg (Source.left i)) x) hx

omit [DecidableEq D] in
theorem union_restricts_right {w1 w2 : World D} (hd : SeparateWorlds w1 w2)
    {g : Sec (HeldIn (World.union w1 w2)) (Content D)}
    (hg : Glues (sections (World.union w1 w2)) g) :
    Glues (sections w2) (g.restrict fun _ ⟨i, hx⟩ => ⟨Source.right hd i, hx⟩) := by
  intro i
  funext x hx
  exact congrFun (congrFun (hg (Source.right hd i)) x) hx

end OpenSheaf.Sheaf
