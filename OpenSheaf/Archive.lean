-- Generated from literate/30-archive.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Object

namespace OpenSheaf

/-- What an archive keeps under an object identifier: an object, or the
tombstone of an object taken down, with the digests of its inventories
(section 11.3). -/
inductive Entry (D : Type)
  | live (o : Obj D)
  | tomb (digests : List D)

/-- An archive (section 5). -/
structure Archive (D : Type) where
  id : ArchiveId
  entries : ObjectId → Option (Entry D)

/-- The archives, by identifier. -/
abbrev World (D : Type) := ArchiveId → Option (Archive D)

/-- The result of resolving a pin (section 14). -/
inductive Resolution (D : Type)
  | ok (v : Version D)
  | removed
  | mismatch
  | missing

variable {D : Type}

/-- The entry of an object, if its archive and the object exist. -/
def lookup (w : World D) (a : ArchiveId) (oid : ObjectId) : Option (Entry D) :=
  match w a with
  | none => none
  | some ar => ar.entries oid

/-- Replace the entry of an object of an existing archive. -/
def setEntry (w : World D) (a : ArchiveId) (oid : ObjectId) (e : Entry D) : World D :=
  fun b => if b = a then
      (w b).map fun ar => { ar with entries := fun x => if x = oid then some e else ar.entries x }
    else w b

theorem lookup_setEntry {w : World D} {a : ArchiveId} {ar : Archive D} {oid : ObjectId}
    {e : Entry D} (ha : w a = some ar) (b : ArchiveId) (x : ObjectId) :
    lookup (setEntry w a oid e) b x = if b = a ∧ x = oid then some e else lookup w b x := by
  unfold lookup setEntry
  by_cases hb : b = a
  · subst hb
    by_cases hx : x = oid <;> simp [ha, hx]
  · simp [hb]

theorem lookup_some_archive {w : World D} {a : ArchiveId} {oid : ObjectId} {e : Entry D}
    (h : lookup w a oid = some e) : ∃ ar, w a = some ar := by
  unfold lookup at h
  split at h
  · contradiction
  · exact ⟨_, by assumption⟩

section Resolve

variable [DecidableEq D] (hash : Hash D)

/-- Resolve a pin against an entry. -/
def resolveEntry : Option (Entry D) → Pin D → Resolution D
  | none, _ => .missing
  | some (.tomb ds), p => if p.digest ∈ ds then .removed else .mismatch
  | some (.live o), p =>
    match o.versionAt p.version with
    | none => .missing
    | some v => if hash (o.inventory p.version) = p.digest then .ok v else .mismatch

/-- Resolve a pin in a world. -/
def resolve (w : World D) (p : Pin D) : Resolution D :=
  resolveEntry hash (lookup w p.archive p.object) p

/-- A version found through a live entry is the version at the pinned number,
and the digest matches. -/
theorem resolveEntry_live_ok {o : Obj D} {p : Pin D} {v : Version D}
    (h : resolveEntry hash (some (.live o)) p = .ok v) :
    o.versionAt p.version = some v ∧ hash (o.inventory p.version) = p.digest := by
  simp only [resolveEntry] at h
  cases hv : o.versionAt p.version with
  | none => simp [hv] at h
  | some v' =>
    simp only [hv] at h
    by_cases hd : hash (o.inventory p.version) = p.digest
    · simp [hd] at h; subst h; exact ⟨rfl, hd⟩
    · simp [hd] at h

theorem resolveEntry_live_of {o : Obj D} {p : Pin D} {v : Version D}
    (hv : o.versionAt p.version = some v) (hd : hash (o.inventory p.version) = p.digest) :
    resolveEntry hash (some (.live o)) p = .ok v := by
  simp [resolveEntry, hv, hd]

/-- A pin of an object that keeps the prefix of the history up to the pinned
version resolves to the same version. -/
theorem resolveEntry_prefix {o o' : Obj D} {pre t t' : List (Version D)} {p : Pin D}
    {v : Version D} (ho : o.versions = pre ++ t) (ho' : o'.versions = pre ++ t')
    (hn : p.version ≤ pre.length) (h : resolveEntry hash (some (.live o)) p = .ok v) :
    resolveEntry hash (some (.live o')) p = .ok v := by
  obtain ⟨hv, hd⟩ := resolveEntry_live_ok hash h
  exact resolveEntry_live_of hash (versionAt_prefix ho ho' hn hv)
    (by rw [inventory_prefix ho ho' hn]; exact hd)

/-- Appending a version to an object does not change what its pins resolve
to. -/
theorem resolveEntry_append {o : Obj D} {x : Version D} {p : Pin D} {v : Version D}
    (h : resolveEntry hash (some (.live o)) p = .ok v) :
    resolveEntry hash (some (.live (o.append x))) p = .ok v := by
  obtain ⟨hv, _⟩ := resolveEntry_live_ok hash h
  exact resolveEntry_prefix hash (t := []) (by simp) rfl (Obj.versionAt_bounds hv).2 h

end Resolve

/-- The changes of the archives that keep every object version: a new
archive, a new object, a new object version. Takedown is not a step. -/
inductive Step : World D → World D → Prop
  | newArchive (w : World D) (a : ArchiveId) (ar : Archive D) (h : w a = none) :
      Step w (fun b => if b = a then some ar else w b)
  | create (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
      (ha : w a = some ar) (ho : ar.entries oid = none) :
      Step w (setEntry w a oid (.live o))
  | append (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
      (x : Version D) (ha : w a = some ar) (ho : ar.entries oid = some (.live o)) :
      Step w (setEntry w a oid (.live (o.append x)))

/-- Any number of steps. -/
inductive Steps : World D → World D → Prop
  | refl (w : World D) : Steps w w
  | tail {w w' w'' : World D} : Steps w w' → Step w' w'' → Steps w w''

section Immutability

variable [DecidableEq D] (hash : Hash D)

/-- **Immutability.** No step changes what a pin resolves to. -/
theorem Step.resolve_ok {w w' : World D} (hs : Step w w') {p : Pin D} {v : Version D}
    (h : resolve hash w p = .ok v) : resolve hash w' p = .ok v := by
  unfold resolve at *
  cases hs with
  | newArchive a ar ha =>
    have : lookup (fun b => if b = a then some ar else w b) p.archive p.object =
        lookup w p.archive p.object := by
      by_cases hb : p.archive = a
      · subst hb
        simp [lookup, ha] at h ⊢
        simp [resolveEntry] at h
      · simp [lookup, hb]
    rw [this]; exact h
  | create a ar oid o ha ho =>
    rw [lookup_setEntry ha]
    split
    · rename_i hx
      obtain ⟨rfl, rfl⟩ := hx
      simp [lookup, ha, ho, resolveEntry] at h
    · exact h
  | append a ar oid o x ha ho =>
    rw [lookup_setEntry ha]
    split
    · rename_i hx
      obtain ⟨rfl, rfl⟩ := hx
      have hl : lookup w p.archive p.object = some (.live o) := by simp [lookup, ha, ho]
      rw [hl] at h
      exact resolveEntry_append hash h
    · exact h

/-- Immutability over any number of steps. -/
theorem Steps.resolve_ok {w w' : World D} (hs : Steps w w')
    {p : Pin D} {v : Version D} (h : resolve hash w p = .ok v) : resolve hash w' p = .ok v := by
  induction hs with
  | refl => exact h
  | tail _ hstep ih => exact Step.resolve_ok hash hstep ih

/-- The digests of all the inventories of an object, kept by its tombstone. -/
def tombstone (o : Obj D) : List D :=
  (List.range o.versions.length).map fun i => hash (o.inventory (i + 1))

/-- Take an object down (section 11.2): its entry becomes a tombstone. -/
def takedown (w : World D) (a : ArchiveId) (oid : ObjectId) (o : Obj D) : World D :=
  setEntry w a oid (.tomb (tombstone hash o))

/-- A pin of a version that was taken down resolves to `removed`: verifiers
report it as removed, not as wrong (section 14). -/
theorem takedown_removed {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) {p : Pin D} {v : Version D}
    (hp : p.archive = a ∧ p.object = oid) (h : resolve hash w p = .ok v) :
    resolve hash (takedown hash w a oid o) p = .removed := by
  obtain ⟨ar, ha⟩ := lookup_some_archive hl
  unfold resolve at *
  obtain ⟨rfl, rfl⟩ := hp
  rw [hl] at h
  obtain ⟨hv, hd⟩ := resolveEntry_live_ok hash h
  obtain ⟨h1, h2⟩ := Obj.versionAt_bounds hv
  unfold takedown
  rw [lookup_setEntry ha]
  simp only [and_self, ite_true, resolveEntry]
  have : p.digest ∈ tombstone hash o := by
    unfold tombstone
    refine List.mem_map.mpr ⟨p.version - 1, List.mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_add_cancel h1]; exact hd
  simp [this]

/-- A takedown changes nothing else. -/
theorem takedown_other {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) {p : Pin D}
    (hp : ¬ (p.archive = a ∧ p.object = oid)) :
    resolve hash (takedown hash w a oid o) p = resolve hash w p := by
  obtain ⟨ar, ha⟩ := lookup_some_archive hl
  unfold resolve takedown
  rw [lookup_setEntry ha]
  split
  · rename_i hc; exact absurd hc hp
  · rfl

end Immutability

end OpenSheaf
