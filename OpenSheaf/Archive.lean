-- Generated from literate/30-archive.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Object

namespace OpenSheaf

/-- What an archive keeps under an object identifier: an object, or the
tombstone of an object taken down, with its last version and the digest of
that version's inventory (section 11.3). -/
inductive Entry (D : Type)
  | live (o : Obj D)
  | tomb (lastVersion : Nat) (digest : D)

/-- An agent: a depositor, named as in the inventory (section 7.1). -/
abbrev Agent := String

/-- An archive (section 5), with the agents who may act for its owner. -/
structure Archive (D : Type) where
  id : ArchiveId
  entries : ObjectId → Option (Entry D)
  writers : List Agent := []

/-- The archives, by identifier. -/
abbrev World (D : Type) := ArchiveId → Option (Archive D)

/-- The result of resolving a pin (section 14). -/
inductive Resolution (D : Type)
  | ok (v : Version D)
  | removed
  | mismatch
  | unavailable
  deriving DecidableEq, Repr

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

theorem if_yes {α : Type} {c : Prop} [Decidable c] {x y : α} (h : c) :
    (if c then x else y) = x := by simp [h]

theorem if_no {α : Type} {c : Prop} [Decidable c] {x y : α} (h : ¬ c) :
    (if c then x else y) = y := by simp [h]

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
  | none, _ => .unavailable
  | some (.tomb _ _), _ => .removed
  | some (.live o), p =>
    match o.versionAt p.version with
    | none => .unavailable
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
    {v : Version D} (hid : o'.archive = o.archive ∧ o'.id = o.id)
    (ho : o.versions = pre ++ t) (ho' : o'.versions = pre ++ t')
    (hn : p.version ≤ pre.length) (h : resolveEntry hash (some (.live o)) p = .ok v) :
    resolveEntry hash (some (.live o')) p = .ok v := by
  obtain ⟨hv, hd⟩ := resolveEntry_live_ok hash h
  exact resolveEntry_live_of hash (versionAt_prefix ho ho' hn hv)
    (by rw [inventory_prefix hid ho ho' hn]; exact hd)

/-- Appending a version to an object does not change what its pins resolve
to. -/
theorem resolveEntry_append {o : Obj D} {x : Version D} {p : Pin D} {v : Version D}
    (h : resolveEntry hash (some (.live o)) p = .ok v) :
    resolveEntry hash (some (.live (o.append x))) p = .ok v := by
  obtain ⟨hv, _⟩ := resolveEntry_live_ok hash h
  exact resolveEntry_prefix hash (o := o) (o' := o.append x) (t := []) ⟨rfl, rfl⟩
    (by simp) rfl (Obj.versionAt_bounds hv).2 h

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

/-- **Immutability.** No step changes the version a pin resolves to. -/
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

/-- The tombstone of an object: its last version and that version's digest. -/
def tombstone (o : Obj D) : Entry D :=
  .tomb o.versions.length (hash (o.inventory o.versions.length))

/-- Take an object down (section 11.2): its entry becomes a tombstone. -/
def takedown (w : World D) (a : ArchiveId) (oid : ObjectId) (o : Obj D) : World D :=
  setEntry w a oid (tombstone hash o)

/-- Every pin of an object taken down resolves to `removed` (section 11.3). -/
theorem takedown_removed {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) {p : Pin D}
    (hp : p.archive = a ∧ p.object = oid) :
    resolve hash (takedown hash w a oid o) p = .removed := by
  obtain ⟨ar, ha⟩ := lookup_some_archive hl
  unfold resolve takedown tombstone
  rw [lookup_setEntry ha]
  simp only [hp, and_self, ite_true]
  rfl

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
