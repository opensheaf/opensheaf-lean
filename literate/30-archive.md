# Archives and pins

A world is the set of archives, each keeping objects by identifier
(sections 3 and 4). A pin resolves at an archive when the archive keeps a
copy of the line and the inventory of the pinned version has the digest of
the pin (sections 4 and 12.3). This chapter defines resolution, at one
archive and through the hints of a pin, the steps by which archives
change, and proves the two properties on which pins rely:

- **immutability**: once a pin resolves to a version at an archive, no step
  changes the version it resolves to there; so a pin found at one of its
  hints stays found;
- **takedown is detected**: the one change that removes versions (section
  13.2) leaves a tombstone, and pins of the line taken down resolve to
  `removed` at that archive, not to an error.

    -- in OpenSheaf/Archive.lean:
    import OpenSheaf.Object

    namespace OpenSheaf

## Archives and the world

Under an object identifier, an archive keeps either the object or, after a
takedown, its tombstone (section 13.3). The tombstone records the last
object version and the digest of its inventory (and, in the specification,
the identifier, kind, name, owner, genesis name, a date and a reason, which
the model leaves out: it keeps the tombstone under the identifier).

    /-- What an archive keeps under an object identifier: an object, or the
    tombstone of an object taken down, with its last version and the digest of
    that version's inventory (section 13.3). -/
    inductive Entry (D : Type)
      | live (o : Obj D)
      | tomb (lastVersion : Nat) (digest : D)

An archive "holds the lines that owners write there ... and copies of
lines written elsewhere", and "decides only which owners it hosts and how they
deposit" (section 3). The model records the owners an archive hosts, its
`owners` (section 3.1), as a list fixed when the archive is created; a copy
of a line whose owner the archive does not host is a **mirror** (section
11). Who deposits is not the archive's to decide: a version belongs to its
owner when the owner's keys sign it ([chapter 5](38-lines.md)).

    /-- An archive (section 3): its objects and tombstones, and the owners it
    hosts. -/
    structure Archive (D : Type) where
      entries : ObjectId → Option (Entry D)
      owners : List OwnerName := []

    /-- The archives, by location. -/
    abbrev World (D : Type) := ArchiveId → Option (Archive D)

A verifier resolving a pin at an archive reaches one of four results: the
object version; `removed`, for a line taken down; `mismatch`, when the
digest is not that of the inventory; `unavailable`, when the archive or the
line cannot be found there (section 8.5). The model also reports
`unavailable` for a version number that the copy does not have: a copy
that stops early is older, not wrong (section 7.4).

Section 8.5 has seven statuses; the model's resolution has four, and
leaves signatures to the valid steps. A copy found that matches the pin is
`ok`, whether the version is **verified** or **contested** (section 7.3);
an **unchecked** version, whose key log the reader cannot reach, and a
version that is **not a version** of its line (section 7.3) are not
reported as such: in the worlds the model builds, every version held was
signed when it was added ([chapter 8](47-acts.md)), and a signature whose
key-log version is not reached simply does not count
([chapter 5](38-lines.md)).

    /-- The result of resolving a pin (section 8.5). -/
    inductive Resolution (D : Type)
      | ok (v : Version D)
      | removed
      | mismatch
      | unavailable
      deriving DecidableEq, Repr

    variable {D : Type}

Two helpers: finding the entry of an object, and replacing it. Replacing an
entry is the only way the model changes an object of an existing archive:
the steps that create objects or add versions, and the takedown below, are
written with it.

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

Two small helpers for `if`, whose library names (`if_pos`, `if_neg`) this
version of Lean deprecates:

    theorem if_yes {α : Type} {c : Prop} [Decidable c] {x y : α} (h : c) :
        (if c then x else y) = x := by simp [h]

    theorem if_no {α : Type} {c : Prop} [Decidable c] {x y : α} (h : ¬ c) :
        (if c then x else y) = y := by simp [h]

After replacing the entry of `oid` in `a`, looking up `oid` in `a` gives the
new entry, and looking up anything else gives what it gave before.
`setEntry` changes only entries: the owners an archive hosts, fixed when it
is created, are never changed by a step.

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

Adding an empty archive under a free location changes no lookup.

    theorem lookup_newArchive {w : World D} {a : ArchiveId} {ar : Archive D} (h : w a = none)
        (hempty : ∀ x, ar.entries x = none) :
        lookup (fun b => if b = a then some ar else w b) = lookup w := by
      funext b x
      by_cases hb : b = a
      · subst hb; simp [lookup, h, hempty]
      · simp [lookup, hb]

## Resolution

Resolution compares digests, so it needs `D` to have decidable equality, and
it needs the digest function `hash`. A pin names a line, and is resolved
against the copy of that line an archive keeps: "any copy whose bytes match
the pin will do" (section 8.5).

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

A pin resolves through a live entry exactly when the pinned version exists
and the digest matches. The two directions are used throughout.

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

A tombstone, or no entry, never gives a version: every version found comes
from a live object.

    theorem resolveEntry_ok_live {e : Option (Entry D)} {p : Pin D} {u : Version D}
        (h : resolveEntry hash e p = .ok u) : ∃ c, e = some (.live c) := by
      match e, h with
      | some (.live c), _ => exact ⟨c, rfl⟩
      | none, h => simp [resolveEntry] at h
      | some (.tomb _ _), h => simp [resolveEntry] at h

And a pin reports `removed` at an archive exactly when the archive has a
tombstone of its line.

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

With the lemmas of [chapter 2](20-object.md): a pin of a version within a
kept prefix of the same object still resolves, to the same version.
Appending a version is the case where the whole history is the prefix.

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

Witnesses are not part of any version: adding them changes nothing that a
pin resolves to.

    theorem resolveEntry_witness {o : Obj D} {ss : List (Sig D)} {p : Pin D} {v : Version D}
        (h : resolveEntry hash (some (.live o)) p = .ok v) :
        resolveEntry hash (some (.live { o with sigs := o.sigs ++ ss })) p = .ok v := h

## Resolution through the hints

A resolver "tries, in any order, the locations it has" (section 12.3); the
model tries the hints of the pin, in their order, and keeps the best
result: a version, then a mismatch (a copy found that does not match),
then `removed` (no copy found, and a tombstone), then `unavailable`
(section 8.5). Among results of the same rank, the first wins. So a copy
that matches decides the status, whatever other locations serve; the
specification reports the copies that do not match apart, with their
location (#37), which the model does not record. Which
version is found does not depend on where it was found unless two copies
disagree, which [chapter 9](48-copies.md) shows cannot happen while the
owner signs one history and inventories do not collide.

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

The best result is one of the results, and a list with a version among its
results gives a version.

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

A version found through the hints was found at one of them, and a version
found at one of them makes the resolution find one.

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

A pin is **found** when one of its hints gives a version. This is the
form in which the model states that a pin resolves: unlike the result of
`resolve`, it does not depend on which hint answers first.

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

## Steps

The specification lets archives change in four ways that keep every object
version: a new archive appears, an archive creates an object, an archive
adds a version to one of its objects, with its signature files, and an
archive adds witnesses to an object, which "MAY be added at any time"
(section 7.2). Every operation of an owner or a
custodian is one of these: a deposit, a description-only version, a
withdrawal, a new version of a collection, a branch, an owner's first key
log, a new version of a key log, a copy of a line (new objects). A
takedown, and the rewriting or deletion of a draft, are not steps; they are
treated apart, below and in [chapter 10](50-drafts.md).

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

The model has several kinds of step (valid steps, takedowns, the steps of
drafts, in the next chapters), and for each it needs sequences of them.
One definition serves for all: `Star r` is any number of steps of the
relation `r`, the last one added at the end.

    /-- Any number of steps of the relation `r`. -/
    inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop
      | refl (a : α) : Star r a a
      | tail {a b c : α} : Star r a b → r b c → Star r a c

    /-- Any number of steps. -/
    abbrev Steps : World D → World D → Prop := Star Step

Three facts about sequences, used for every kind of step. A property kept
by each step is kept by any number of them; sequences can be joined; and a
sequence of steps of one kind is a sequence of another, when each step of
the first kind is one of the second.

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

## Immutability

The main theorem of the chapter. The proof is by cases on the step. A new
archive, or a new object, appears where a pin could not have resolved
before, so pins that resolved are untouched. A new version is appended
after the pinned one, and `resolveEntry_append` applies; new witnesses
change no version.

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

By induction, the same holds over any number of steps; and a pin found at
one of its hints stays found.

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

Note what the proof did not use: any property of `hash`. Pins stay valid
because archives only add versions, not because digests are hard to forge.
The digests matter for a different question: whether a copy of a line,
received from anywhere, is the version pinned. [Chapter 9](48-copies.md)
answers it, under a hypothesis on `hash` and on what the owner signs.

## Takedown

A takedown (section 13.2) deletes an object from an archive, "whatever its
reason", and leaves a tombstone (section 13.3).

    /-- The tombstone of an object: its last version and that version's digest. -/
    def tombstone (o : Obj D) : Entry D :=
      .tomb o.versions.length (hash (o.inventory o.versions.length))

    /-- Take an object down (section 13.2): its entry becomes a tombstone. -/
    def takedown (w : World D) (a : ArchiveId) (oid : ObjectId) (o : Obj D) : World D :=
      setEntry w a oid (tombstone hash o)

A takedown replaces the entry of the object taken down by its tombstone, and
leaves every other entry as it was.

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

"A line, or a version of it no later than `lastVersion`, of which no copy
is found but a tombstone is, is reported as removed" (section 13.3): at the
archive, every pin of the line now resolves to `removed`, whatever its
version and digest. The tombstone keeps only the last digest, so a verifier
cannot tell there a pin of a version that existed from a pin that never
named one; the tombstone keeps one pin (#33), and the archive's `sha512/`
index keeps every digest (section 12.5), which the model leaves out.

    /-- At the archive, every pin of a line taken down resolves to `removed`
    (section 13.3). -/
    theorem takedown_removed {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl : lookup w a oid = some (.live o)) {p : Pin D} (hp : ObjectId.line p.line = oid) :
        resolveAt hash (takedown hash w a oid o) a p = .removed := by
      unfold resolveAt
      rw [lookup_takedown_eq hash hl, if_yes ⟨rfl, hp⟩]
      rfl

And a takedown changes nothing else: pins resolve as before at every other
archive, and pins of other lines at the same archive. It removes one
object: "others holding the same files, such as a branch holding its parent
version (section 9), are taken down on their own" (section 13.2), and so
are copies of the line in other archives.

    /-- A takedown changes nothing else. -/
    theorem takedown_other {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl : lookup w a oid = some (.live o)) {b : ArchiveId} {p : Pin D}
        (hp : ¬ (b = a ∧ ObjectId.line p.line = oid)) :
        resolveAt hash (takedown hash w a oid o) b p = resolveAt hash w b p := by
      unfold resolveAt
      rw [lookup_takedown_eq hash hl, if_no hp]

    end Immutability

    end OpenSheaf
