-- Generated from literate/30-archive.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Object

namespace OpenSheaf

/-- What an archive keeps under an object identifier: an object, or the
tombstone of an object taken down, with its last version and the digest of
that version's inventory (section 13.3). -/
inductive Entry (D : Type)
  | live (o : Obj D)
  | tomb (lastVersion : Nat) (digest : D)

/-- An archive (section 3): its objects and tombstones, and the owners it
hosts. -/
structure Archive (D : Type) where
  entries : ObjectId → Option (Entry D)
  owners : List OwnerName := []

/-- The archives, by location. -/
abbrev World (D : Type) := ArchiveId → Option (Archive D)

/-- The result of resolving a pin (section 8.5). -/
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

/-- The owners archive `a` hosts, if it exists. -/
def ownersOf (w : World D) (a : ArchiveId) : Option (List OwnerName) :=
  (w a).map (·.owners)

theorem ownersOf_setEntry (w : World D) (a : ArchiveId) (oid : ObjectId) (e : Entry D)
    (c : ArchiveId) : ownersOf (setEntry w a oid e) c = ownersOf w c := by
  unfold ownersOf setEntry
  by_cases hc : c = a
  · subst hc; cases w c <;> simp
  · simp [hc]

theorem lookup_newArchive {w : World D} {a : ArchiveId} {ar : Archive D} (h : w a = none)
    (hempty : ∀ x, ar.entries x = none) :
    lookup (fun b => if b = a then some ar else w b) = lookup w := by
  funext b x
  by_cases hb : b = a
  · subst hb; simp [lookup, h, hempty]
  · simp [lookup, hb]

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

/-- Resolve a pin against the copy of its line kept by archive `b`. -/
def resolveAt (w : World D) (b : ArchiveId) (p : Pin D) : Resolution D :=
  resolveEntry hash (lookup w b (.line p.line)) p

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

theorem resolveEntry_ok_live {e : Option (Entry D)} {p : Pin D} {u : Version D}
    (h : resolveEntry hash e p = .ok u) : ∃ c, e = some (.live c) := by
  match e, h with
  | some (.live c), _ => exact ⟨c, rfl⟩
  | none, h => simp [resolveEntry] at h
  | some (.tomb _ _), h => simp [resolveEntry] at h

theorem resolveAt_removed_iff {w : World D} {b : ArchiveId} {p : Pin D} :
    resolveAt hash w b p = .removed ↔ ∃ n d, lookup w b (.line p.line) = some (.tomb n d) := by
  unfold resolveAt
  constructor
  · intro h
    match he : lookup w b (.line p.line), h with
    | some (.tomb n d), _ => exact ⟨n, d, rfl⟩
    | none, h => simp [resolveEntry] at h
    | some (.live o), h =>
      simp only [resolveEntry] at h
      split at h
      · cases h
      · split at h <;> cases h
  · rintro ⟨n, d, h⟩
    rw [h]; rfl

/-- A pin of an object that keeps the prefix of the history up to the pinned
version resolves to the same version. -/
theorem resolveEntry_prefix {o o' : Obj D} {pre t t' : List (Version D)} {p : Pin D}
    {v : Version D} (hid : o'.id = o.id ∧ o'.genesis = o.genesis)
    (ho : o.versions = pre ++ t) (ho' : o'.versions = pre ++ t')
    (hn : p.version ≤ pre.length) (h : resolveEntry hash (some (.live o)) p = .ok v) :
    resolveEntry hash (some (.live o')) p = .ok v := by
  obtain ⟨hv, hd⟩ := resolveEntry_live_ok hash h
  exact resolveEntry_live_of hash (versionAt_prefix ho ho' hn hv)
    (by rw [inventory_prefix hid ho ho' hn]; exact hd)

/-- Appending a version to an object does not change what its pins resolve
to. -/
theorem resolveEntry_append {o : Obj D} {x : Version D} {ss : List (Sig D)} {p : Pin D}
    {v : Version D} (h : resolveEntry hash (some (.live o)) p = .ok v) :
    resolveEntry hash (some (.live (o.append x ss))) p = .ok v := by
  obtain ⟨hv, _⟩ := resolveEntry_live_ok hash h
  exact resolveEntry_prefix hash (o := o) (o' := o.append x ss) (t := []) ⟨rfl, rfl⟩
    (by simp) rfl (Obj.versionAt_bounds hv).2 h

theorem resolveEntry_witness {o : Obj D} {ss : List (Sig D)} {p : Pin D} {v : Version D}
    (h : resolveEntry hash (some (.live o)) p = .ok v) :
    resolveEntry hash (some (.live { o with sigs := o.sigs ++ ss })) p = .ok v := h

/-- The rank of a result: a version, a mismatch, `removed`, `unavailable`. -/
def Resolution.rank : Resolution D → Nat
  | .ok _ => 3
  | .mismatch => 2
  | .removed => 1
  | .unavailable => 0

/-- The best of a list of results, the first among equals. -/
def pick : List (Resolution D) → Resolution D
  | [] => .unavailable
  | r :: rs => if (pick rs).rank ≤ r.rank then r else pick rs

/-- Resolve a pin through its hints (section 12.3). -/
def resolve (w : World D) (p : Pin D) : Resolution D :=
  pick (p.hints.map fun b => resolveAt hash w b p)

omit [DecidableEq D] in
theorem pick_mem {rs : List (Resolution D)} (h : rs ≠ []) : pick rs ∈ rs := by
  induction rs with
  | nil => exact absurd rfl h
  | cons r rs ih =>
    simp only [pick]
    split
    · exact List.mem_cons_self ..
    · cases rs with
      | nil => simp [pick, Resolution.rank] at *
      | cons r' rs' => exact List.mem_cons_of_mem _ (ih (by simp))

omit [DecidableEq D] in
theorem pick_rank_ge {rs : List (Resolution D)} {r : Resolution D} (h : r ∈ rs) :
    r.rank ≤ (pick rs).rank := by
  induction rs with
  | nil => cases h
  | cons r' rs ih =>
    simp only [pick]
    rcases List.mem_cons.mp h with rfl | h
    · split <;> omega
    · have := ih h; split <;> omega

omit [DecidableEq D] in
theorem pick_ok_of_mem {rs : List (Resolution D)} {v : Version D} (h : .ok v ∈ rs) :
    ∃ u, pick rs = .ok u := by
  have hr := pick_rank_ge h
  cases hp : pick rs with
  | ok u => exact ⟨u, rfl⟩
  | _ => rw [hp] at hr; simp [Resolution.rank] at hr

theorem resolve_ok_at {w : World D} {p : Pin D} {v : Version D}
    (h : resolve hash w p = .ok v) : ∃ b ∈ p.hints, resolveAt hash w b p = .ok v := by
  unfold resolve at h
  have hne : p.hints.map (fun b => resolveAt hash w b p) ≠ [] := by
    intro he; rw [he] at h; simp [pick] at h
  have := pick_mem hne
  rw [h] at this
  obtain ⟨b, hb, hr⟩ := List.mem_map.mp this
  exact ⟨b, hb, hr⟩

theorem resolve_ok_of_at {w : World D} {p : Pin D} {b : ArchiveId} (hb : b ∈ p.hints)
    {v : Version D} (h : resolveAt hash w b p = .ok v) : ∃ u, resolve hash w p = .ok u :=
  pick_ok_of_mem (List.mem_map.mpr ⟨b, hb, h⟩)

/-- The pin resolves at one of its hints. -/
def Found (w : World D) (p : Pin D) : Prop :=
  ∃ b ∈ p.hints, ∃ t, resolveAt hash w b p = .ok t

theorem found_iff {w : World D} {p : Pin D} :
    Found hash w p ↔ ∃ t, resolve hash w p = .ok t := by
  constructor
  · rintro ⟨b, hb, t, ht⟩; exact resolve_ok_of_at hash hb ht
  · rintro ⟨t, ht⟩
    obtain ⟨b, hb, h⟩ := resolve_ok_at hash ht
    exact ⟨b, hb, t, h⟩

end Resolve

/-- The changes of the archives that keep every object version: a new
archive, a new object, a new object version, new witnesses. Takedown is not
a step. -/
inductive Step : World D → World D → Prop
  | newArchive (w : World D) (a : ArchiveId) (ar : Archive D) (h : w a = none) :
      Step w (fun b => if b = a then some ar else w b)
  | create (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
      (ha : w a = some ar) (ho : ar.entries oid = none) :
      Step w (setEntry w a oid (.live o))
  | append (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
      (x : Version D) (ss : List (Sig D)) (ha : w a = some ar)
      (ho : ar.entries oid = some (.live o)) :
      Step w (setEntry w a oid (.live (o.append x ss)))
  | witness (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
      (ss : List (Sig D)) (ha : w a = some ar) (ho : ar.entries oid = some (.live o)) :
      Step w (setEntry w a oid (.live { o with sigs := o.sigs ++ ss }))

/-- Any number of steps of the relation `r`. -/
inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop
  | refl (a : α) : Star r a a
  | tail {a b c : α} : Star r a b → r b c → Star r a c

/-- Any number of steps. -/
abbrev Steps : World D → World D → Prop := Star Step

theorem Star.invariant {α : Type} {r : α → α → Prop} (P : α → Prop)
    (hP : ∀ {a b}, r a b → P a → P b) {a b : α} (h : Star r a b) (ha : P a) : P b := by
  induction h with
  | refl => exact ha
  | tail _ hr ih => exact hP hr ih

theorem Star.trans {α : Type} {r : α → α → Prop} {a b c : α} (h1 : Star r a b)
    (h2 : Star r b c) : Star r a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hr ih => exact .tail ih hr

theorem Star.mono {α : Type} {r s : α → α → Prop} (hrs : ∀ {a b}, r a b → s a b)
    {a b : α} (h : Star r a b) : Star s a b := by
  induction h with
  | refl => exact .refl _
  | tail _ hr ih => exact .tail ih (hrs hr)

theorem Step.owners_kept {w w' : World D} (hs : Step w w') {a : ArchiveId}
    {os : List OwnerName} (h : ownersOf w a = some os) : ownersOf w' a = some os := by
  cases hs with
  | newArchive b ar hb =>
    have : a ≠ b := by rintro rfl; simp [ownersOf, hb] at h
    unfold ownersOf at h ⊢
    simp only [this, ite_false]; exact h
  | create => rw [ownersOf_setEntry]; exact h
  | append => rw [ownersOf_setEntry]; exact h
  | witness => rw [ownersOf_setEntry]; exact h

section Immutability

variable [DecidableEq D] (hash : Hash D)

/-- **Immutability.** No step changes the version a pin resolves to at an
archive. -/
theorem Step.resolveAt_ok {w w' : World D} (hs : Step w w') {b : ArchiveId} {p : Pin D}
    {v : Version D} (h : resolveAt hash w b p = .ok v) : resolveAt hash w' b p = .ok v := by
  unfold resolveAt at *
  cases hs with
  | newArchive a ar ha =>
    have : lookup (fun c => if c = a then some ar else w c) b (.line p.line) =
        lookup w b (.line p.line) := by
      by_cases hb : b = a
      · subst hb
        simp [lookup, ha] at h ⊢
        simp [resolveEntry] at h
      · simp [lookup, hb]
    rw [this]; exact h
  | create a ar oid o ha ho =>
    rw [lookup_setEntry ha]
    split
    · rename_i hx
      obtain ⟨rfl, hx⟩ := hx
      rw [← hx] at ho
      simp [lookup, ha, ho, resolveEntry] at h
    · exact h
  | append a ar oid o x ss ha ho =>
    rw [lookup_setEntry ha]
    split
    · rename_i hx
      obtain ⟨rfl, hx⟩ := hx
      rw [← hx] at ho
      have hl : lookup w b (.line p.line) = some (.live o) := by simp [lookup, ha, ho]
      rw [hl] at h
      exact resolveEntry_append hash h
    · exact h
  | witness a ar oid o ss ha ho =>
    rw [lookup_setEntry ha]
    split
    · rename_i hx
      obtain ⟨rfl, hx⟩ := hx
      rw [← hx] at ho
      have hl : lookup w b (.line p.line) = some (.live o) := by simp [lookup, ha, ho]
      rw [hl] at h
      exact resolveEntry_witness hash h
    · exact h

/-- Immutability over any number of steps. -/
theorem Steps.resolveAt_ok {w w' : World D} (hs : Steps w w') {b : ArchiveId}
    {p : Pin D} {v : Version D} (h : resolveAt hash w b p = .ok v) :
    resolveAt hash w' b p = .ok v :=
  hs.invariant (fun w => resolveAt hash w b p = .ok v)
    (fun hs => Step.resolveAt_ok hash hs) h

theorem Step.found {w w' : World D} (hs : Step w w') {p : Pin D} (h : Found hash w p) :
    Found hash w' p := by
  obtain ⟨b, hb, t, ht⟩ := h
  exact ⟨b, hb, t, hs.resolveAt_ok hash ht⟩

theorem Steps.found {w w' : World D} (hs : Steps w w') {p : Pin D} (h : Found hash w p) :
    Found hash w' p :=
  hs.invariant (fun w => Found hash w p) (fun hs => Step.found hash hs) h

/-- The tombstone of an object: its last version and that version's digest. -/
def tombstone (o : Obj D) : Entry D :=
  .tomb o.versions.length (hash (o.inventory o.versions.length))

/-- Take an object down (section 13.2): its entry becomes a tombstone. -/
def takedown (w : World D) (a : ArchiveId) (oid : ObjectId) (o : Obj D) : World D :=
  setEntry w a oid (tombstone hash o)

omit [DecidableEq D] in
theorem lookup_takedown_eq {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) (b : ArchiveId) (x : ObjectId) :
    lookup (takedown hash w a oid o) b x =
      if b = a ∧ x = oid then some (tombstone hash o) else lookup w b x := by
  obtain ⟨ar, ha⟩ := lookup_some_archive hl
  exact lookup_setEntry ha b x

omit [DecidableEq D] in
theorem lookup_takedown {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) {b : ArchiveId} {x : ObjectId} {o' : Obj D}
    (h : lookup (takedown hash w a oid o) b x = some (.live o')) :
    ¬ (b = a ∧ x = oid) ∧ lookup w b x = some (.live o') := by
  rw [lookup_takedown_eq hash hl] at h
  split at h
  · cases h
  · rename_i hc; exact ⟨hc, h⟩

/-- At the archive, every pin of a line taken down resolves to `removed`
(section 13.3). -/
theorem takedown_removed {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) {p : Pin D} (hp : ObjectId.line p.line = oid) :
    resolveAt hash (takedown hash w a oid o) a p = .removed := by
  unfold resolveAt
  rw [lookup_takedown_eq hash hl, if_yes ⟨rfl, hp⟩]
  rfl

/-- A takedown changes nothing else. -/
theorem takedown_other {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) {b : ArchiveId} {p : Pin D}
    (hp : ¬ (b = a ∧ ObjectId.line p.line = oid)) :
    resolveAt hash (takedown hash w a oid o) b p = resolveAt hash w b p := by
  unfold resolveAt
  rw [lookup_takedown_eq hash hl, if_no hp]

end Immutability

end OpenSheaf
