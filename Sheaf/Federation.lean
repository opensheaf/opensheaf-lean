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

variable [DecidableEq D] (hash : Hash D)

theorem Events.names_exist {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) {b : ArchiveId}
    {i : ObjectId} {c : Obj D} (hl : lookup w b i = some (.live c)) : w c.archive ≠ none := by
  by_cases hb : c.archive = b
  · rw [hb]; exact archive_of_lookup hl
  · obtain ⟨hne, _⟩ := Events.mirrorsOk hash hs b i c hl hb
    intro h; apply hne; simp [lookup, h]

theorem Events.pins_exist {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) {b : ArchiveId}
    {i : ObjectId} {c : Obj D} (hl : lookup w b i = some (.live c)) {v : Version D}
    (hv : v ∈ c.versions) {p : Pin D} (hp : p ∈ v.pins) : w p.archive ≠ none := by
  rcases (Events.sound hash hs).2 _ _ _ hl v hv p hp with ⟨u, hu⟩ | hr
  · unfold resolve at hu
    obtain ⟨o, ho⟩ := resolveEntry_ok_live hash hu
    exact archive_of_lookup ho
  · obtain ⟨n, d, ht⟩ := (resolve_removed_iff hash).mp hr
    exact archive_of_lookup ht

/-- **Separate worlds share no named document version.** -/
theorem no_shared_names {w1 w2 : World D} (hd : SeparateWorlds w1 w2)
    (hs1 : Events hash (fun _ => (none : Option (Archive D))) w1)
    (hs2 : Events hash (fun _ => (none : Option (Archive D))) w2)
    {x : Name} {v v' : Version D} (h1 : Holds w1 x v) (h2 : Holds w2 x v') : False := by
  obtain ⟨b, i, c, hl, _, rfl⟩ := h1
  obtain ⟨b', i', c', hl', _, hx⟩ := h2
  have ha : c'.archive = c.archive := congrArg Name.archive hx
  rcases hd c.archive with h | h
  · exact Events.names_exist hash hs1 hl h
  · exact Events.names_exist hash hs2 hl' (ha ▸ h)

/-- **No pin held in one world names an archive of the other.** -/
theorem no_cross_pins {w1 w2 : World D} (hd : SeparateWorlds w1 w2)
    (hs2 : Events hash (fun _ => (none : Option (Archive D))) w2) {b : ArchiveId}
    {i : ObjectId} {c : Obj D} (hl : lookup w2 b i = some (.live c)) {v : Version D}
    (hv : v ∈ c.versions) {p : Pin D} (hp : p ∈ v.pins) : w1 p.archive = none :=
  (hd p.archive).resolve_right (Events.pins_exist hash hs2 hl hv hp)

/-- **Separate worlds glue**, with no condition. -/
theorem separate_glue {w1 w2 : World D} (hd : SeparateWorlds w1 w2)
    (hs1 : Events hash (fun _ => (none : Option (Archive D))) w1)
    (hs2 : Events hash (fun _ => (none : Option (Archive D))) w2) :
    ∃ g, Glues (sections (World.union w1 w2)) g ∧
      ∀ g', Glues (sections (World.union w1 w2)) g' → g' = g := by
  apply sheaf
  apply compatible_of_agree
  · intro b i c hl
    rcases lookup_union_cases hl with hl | hl
    · exact ((Events.sound hash hs1).1 _ _ _ hl).history
    · exact ((Events.sound hash hs2).1 _ _ _ hl).history
  · intro b x m b' x' m' hl hl' ha _
    have c1 := Events.copiesAgree hash hs1
    have c2 := Events.copiesAgree hash hs2
    rcases lookup_union_cases hl with hl | hl <;> rcases lookup_union_cases hl' with hl' | hl'
    · exact c1 _ _ _ _ _ _ hl hl' ha ‹_›
    · exfalso
      rcases hd m.archive with h | h
      · exact Events.names_exist hash hs1 hl h
      · exact Events.names_exist hash hs2 hl' (ha ▸ h)
    · exfalso
      rcases hd m.archive with h | h
      · exact Events.names_exist hash hs1 hl' (ha ▸ h)
      · exact Events.names_exist hash hs2 hl h
    · exact c2 _ _ _ _ _ _ hl hl' ha ‹_›

omit [DecidableEq D] in
def Source.left {w1 w2 : World D} (i : Source w1) : Source (World.union w1 w2) :=
  ⟨i.archive, i.id, i.obj, lookup_union_left i.live, i.version⟩

omit [DecidableEq D] in
def Source.right {w1 w2 : World D} (hd : SeparateWorlds w1 w2) (i : Source w2) :
    Source (World.union w1 w2) :=
  ⟨i.archive, i.id, i.obj, lookup_union_right hd i.live, i.version⟩

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
