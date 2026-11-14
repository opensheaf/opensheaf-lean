# Mirrors and accepted copies

The specification has two kinds of copy (sections 10.3 to 10.5):

- a **mirror** copies a whole object, byte for byte, under the same
  identifier, into another archive. It is the same object, and is brought up
  to date only by copying the new versions of the original, so its history
  is always a prefix of the original's. A member entry may list archives
  holding mirrors, so that the member can be resolved when its own archive
  does not answer;
- an **accepted copy** is a new object of a selection's archive, whose first
  version holds exactly the files of the revision vetted. It has its own
  inventories, and "cannot stand for the original in the resolution of a
  pin".

This chapter proves that the two behave as the specification says. A
mirror resolves exactly the pins of the original that it has copied, and
nothing else, so a reader can use it without trusting it. An accepted copy
survives a takedown of the original, and is never taken for it. Two of
these statements are the first of the model that need a hypothesis on the
digest function: they are about copies that come from anywhere, and only
the digests tie them to the original.

    -- in OpenSheaf/Copies.lean:
    import OpenSheaf.Worlds

    namespace OpenSheaf

    variable {D : Type} [DecidableEq D] (hash : Hash D)

## Mirrors agree with the original

A mirror's history is a prefix of the original's. The prefix lemma of
[chapter 3](30-archive.md) gives both directions: a pin of the original
resolves on the mirror to the same version, if the mirror has copied that
version; and whatever a pin resolves to on the mirror, it resolves to the
same on the original.

    /-- A mirror resolves the pins of the original that it has copied. -/
    theorem mirror_agrees {o m : Obj D} {t : List (Version D)} (hm : o.versions = m.versions ++ t)
        {p : Pin D} {v : Version D} (hp : p.version ≤ m.versions.length)
        (h : resolveEntry hash (some (.live o)) p = .ok v) :
        resolveEntry hash (some (.live m)) p = .ok v :=
      resolveEntry_prefix hash hm (t' := []) (by simp) hp h

    /-- A mirror shows nothing that the original does not. -/
    theorem mirror_sound {o m : Obj D} {t : List (Version D)} (hm : o.versions = m.versions ++ t)
        {p : Pin D} {v : Version D} (h : resolveEntry hash (some (.live m)) p = .ok v) :
        resolveEntry hash (some (.live o)) p = .ok v := by
      obtain ⟨hv, _⟩ := resolveEntry_live_ok hash h
      exact resolveEntry_prefix hash (t := []) (by simp) hm (Obj.versionAt_bounds hv).2 h

## Any copy, from anywhere

A reader who fetches an object from an archive they do not trust, or from a
disk found in a drawer, has no reason to believe that it is a mirror. The
pin is enough, provided the digest function has no collisions: if the copy
resolves the pin at all, it resolves it to the version of the original.
This is the use of SHA-512 in the specification, and the first statement
of the model that needs it.

    /-- **A pin authenticates any copy.** With a collision-free digest, a copy
    that resolves a pin resolves it to the original's version. -/
    theorem copy_authentic (hinj : ∀ l l', hash l = hash l' → l = l') {o c : Obj D}
        {p : Pin D} {v u : Version D} (ho : resolveEntry hash (some (.live o)) p = .ok v)
        (hc : resolveEntry hash (some (.live c)) p = .ok u) : u = v := by
      obtain ⟨hvo, hdo⟩ := resolveEntry_live_ok hash ho
      obtain ⟨hvc, hdc⟩ := resolveEntry_live_ok hash hc
      have heq : c.inventory p.version = o.inventory p.version := hinj _ _ (hdc.trans hdo.symm)
      obtain ⟨h1, _⟩ := Obj.versionAt_bounds hvo
      unfold Obj.versionAt at hvo hvc
      have hne : p.version ≠ 0 := by omega
      simp only [hne, ite_false] at hvo hvc
      unfold Obj.inventory at heq
      have key : ∀ l : List (Version D), l[p.version - 1]? = (l.take p.version)[p.version - 1]? := by
        intro l; rw [List.getElem?_take]; simp; omega
      rw [key, heq, ← key] at hvc
      rw [hvo] at hvc
      cases hvc
      rfl

## Resolution through mirrors

Section 6.4: a client fetches the pinned version from the member's archive;
"if this fails, [it] tries the mirrors listed in the member", and "any copy
whose bytes match the pinned digest is acceptable: integrity comes from the
pin, not from the place". The model follows it: resolution through mirrors
takes the first copy that gives the version, the member's own archive
first, and otherwise reports what the member's own archive said.

    /-- Resolve a pin against the copy kept by archive `b`. -/
    def resolveAt (w : World D) (b : ArchiveId) (p : Pin D) : Resolution D :=
      resolveEntry hash (lookup w b p.object) p

    /-- The first version found, if any. -/
    def firstOk : List (Resolution D) → Option (Resolution D)
      | [] => none
      | .ok v :: _ => some (.ok v)
      | _ :: rs => firstOk rs

    /-- Resolve a pin through the mirrors `ms` (section 6.4). -/
    def resolveVia (w : World D) (p : Pin D) (ms : List ArchiveId) : Resolution D :=
      (firstOk ((p.archive :: ms).map fun b => resolveAt hash w b p)).getD (resolve hash w p)

When the member's own archive gives the version, the mirrors are not
consulted.

    theorem resolveVia_own {w : World D} {p : Pin D} (ms : List ArchiveId) {v : Version D}
        (h : resolve hash w p = .ok v) : resolveVia hash w p ms = .ok v := by
      have : resolveAt hash w p.archive p = .ok v := h
      simp [resolveVia, this, firstOk]

When it does not (the archive is gone, the object is lost or corrupted), a
mirror holding the pinned version gives it.

    /-- **A mirror stands in for the member's archive.** -/
    theorem resolveVia_mirror {w : World D} {p : Pin D} {b : ArchiveId} {ms : List ArchiveId}
        {m : Obj D} {v : Version D} (hown : ∀ u, resolve hash w p ≠ .ok u)
        (hb : lookup w b p.object = some (.live m))
        (hm : resolveEntry hash (some (.live m)) p = .ok v) :
        resolveVia hash w p (b :: ms) = .ok v := by
      have h2 : resolveAt hash w b p = .ok v := by
        simp only [resolveAt, hb]; exact hm
      simp only [resolveVia, List.map_cons]
      cases h : resolveAt hash w p.archive p with
      | ok u => exact absurd h (hown u)
      | _ => simp [firstOk, h2]

Whatever copy answers, the answer is right: with a collision-free digest,
a version found through mirrors is the version of the original, by
`copy_authentic`. A tombstone never gives a version, so every answer comes
from a live copy.

    theorem resolveEntry_ok_live {e : Option (Entry D)} {p : Pin D} {u : Version D}
        (h : resolveEntry hash e p = .ok u) : ∃ c, e = some (.live c) := by
      match e, h with
      | some (.live c), _ => exact ⟨c, rfl⟩
      | none, h => simp [resolveEntry] at h
      | some (.tomb _ _), h => simp [resolveEntry] at h

    omit [DecidableEq D] in
    theorem firstOk_mem {rs : List (Resolution D)} {u : Version D}
        (h : firstOk rs = some (.ok u)) : Resolution.ok u ∈ rs := by
      induction rs with
      | nil => simp [firstOk] at h
      | cons r rs ih =>
        cases r with
        | ok v => simp [firstOk] at h; subst h; simp
        | _ => simp only [firstOk] at h; exact List.mem_cons_of_mem _ (ih h)

    /-- **Resolution through mirrors is sound**: what it finds is the original's
    version, whoever holds the copy. -/
    theorem resolveVia_sound (hinj : ∀ l l', hash l = hash l' → l = l') {w : World D}
        {p : Pin D} {ms : List ArchiveId} {o : Obj D} {u v : Version D}
        (ho : resolveEntry hash (some (.live o)) p = .ok v)
        (h : resolveVia hash w p ms = .ok u) : u = v := by
      unfold resolveVia at h
      cases hf : firstOk ((p.archive :: ms).map fun b => resolveAt hash w b p) with
      | none =>
        rw [hf] at h
        simp only [Option.getD_none] at h
        obtain ⟨c, hc⟩ := resolveEntry_ok_live hash h
        unfold resolve at h
        rw [hc] at h
        exact copy_authentic hash hinj ho h
      | some r =>
        rw [hf] at h
        simp only [Option.getD_some] at h
        subst h
        obtain ⟨b, _, hb⟩ := List.mem_map.mp (firstOk_mem hf)
        unfold resolveAt at hb
        obtain ⟨c, hc⟩ := resolveEntry_ok_live hash hb
        rw [hc] at hb
        exact copy_authentic hash hinj ho hb

## Accepted copies

An accepted copy is a new document of the selection's archive. Its first
version holds the files of the revision vetted, as document version 1, with
the description and the depositor of the selection.

    /-- The accepted copy of the revision `v`, as object `cid` (section 10.5). -/
    def acceptedCopy (cid : ObjectId) (v : Version D) (description curator message : String) :
        Obj D :=
      { id := cid, kind := .document,
        versions := [{ documentVersion := 1, files := v.files, description,
                       depositor := curator, message }] }

It holds exactly the files vetted, and it is a well-formed object, so that
creating it is a valid step whenever the identifier is free.

    omit [DecidableEq D] in
    theorem acceptedCopy_files (cid : ObjectId) (v : Version D) (d c m : String) :
        ∀ x ∈ (acceptedCopy cid v d c m).versions, x.files = v.files := by
      simp [acceptedCopy]

    theorem acceptedCopy_wf (cid : ObjectId) (v : Version D) (d c m : String) :
        (acceptedCopy cid v d c m).WF cid :=
      ⟨rfl, by simp [acceptedCopy], WellFormed.single rfl, by simp [acceptedCopy]⟩

The copy is kept by the selection's archive, so a takedown of the original
leaves it alone: this is what accepted copies are for.

    /-- **An accepted copy survives the original.** -/
    theorem acceptedCopy_survives {w : World D} {a s : ArchiveId} {oid cid : ObjectId}
        {o : Obj D} (hl : lookup w a oid = some (.live o)) (hdiff : ¬ (s = a ∧ cid = oid))
        {q : Pin D} (hq : q.archive = s ∧ q.object = cid) :
        resolve hash (takedown hash w a oid o) q = resolve hash w q :=
      takedown_other hash hl (by rw [hq.1, hq.2]; exact hdiff)

And it is never taken for the original. With a collision-free digest, a pin
of the original cannot resolve on the copy, since the copy's first version
differs from the original's (it has another description and depositor, if
nothing else). This is why section 10.5 forbids listing an accepted copy
among the mirrors: it would not help, and the model shows it.

    /-- **An accepted copy is not a mirror.** -/
    theorem acceptedCopy_not_mirror (hinj : ∀ l l', hash l = hash l' → l = l') {o c : Obj D}
        (hfirst : c.versions.head? ≠ o.versions.head?) {p : Pin D} {v u : Version D}
        (ho : resolveEntry hash (some (.live o)) p = .ok v) :
        resolveEntry hash (some (.live c)) p ≠ .ok u := by
      intro hc
      obtain ⟨hvo, hdo⟩ := resolveEntry_live_ok hash ho
      obtain ⟨_, hdc⟩ := resolveEntry_live_ok hash hc
      have heq : c.inventory p.version = o.inventory p.version := hinj _ _ (hdc.trans hdo.symm)
      obtain ⟨h1, _⟩ := Obj.versionAt_bounds hvo
      apply hfirst
      unfold Obj.inventory at heq
      have key : ∀ l : List (Version D), l.head? = (l.take p.version).head? := by
        intro l; rw [List.head?_take]; simp; omega
      rw [key, heq, ← key]

    end OpenSheaf
