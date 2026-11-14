# Mirrors and accepted copies

The specification has two kinds of copy (sections 10.3 to 10.5), and a rule
for resolving pins through them (section 6.4):

- a **mirror** copies a whole object, byte for byte, under the same
  identifier, into another archive. It is the same object, and is brought up
  to date only by copying the new versions of the original, so its history
  is always a prefix of the original's. A member entry may list archives
  holding mirrors, so that the member can be resolved when its own archive
  fails;
- an **accepted copy** is a new object of a selection's archive, whose first
  version holds exactly the files of the revision vetted. It has its own
  inventories, and "cannot stand for the original in the resolution of a
  pin".

This chapter proves that the two behave as the specification says. A
mirror resolves exactly the pins of the original that it has copied, and
nothing else. Any copy, mirror or not, trusted or not, resolves a pin only
to the original's version, unless the digests collide. An accepted copy
survives a takedown of the original, and, unless the digests collide, is
never taken for it.

    -- in OpenSheaf/Copies.lean:
    import OpenSheaf.Worlds

    namespace OpenSheaf

    variable {D : Type} [DecidableEq D] (hash : Hash D)

## Collisions

The statements about copies that come from anywhere need a hypothesis on
the digest: only the digest ties a copy to the original. The tempting
hypothesis, that `hash` is injective, cannot hold for a real digest: there
are infinitely many inventories and only finitely many SHA-512 digests, so
some inventories share a digest. What cryptography offers is that nobody
can *find* two such inventories. The model therefore assumes, each time,
only that the two inventories being compared do not collide: if their
digests are equal, so are they. This is the hypothesis a reader relies on
when they accept a copy because its digest matches.

    omit [DecidableEq D] in
    /-- The inventories `i` and `j` do not collide. -/
    def NoCollision (i j : Inventory D) : Prop := hash i = hash j → i = j

The same four theorems use it: `copy_authentic`, `resolveVia_sound`,
`acceptedCopy_not_mirror` here, and `tamper_detected` in
[chapter 9](65-impossible.md). No other theorem of the model assumes
anything about `hash`.

## Mirrors agree with the original

A mirror is the same object: same archive in its `object.json`, same
identifier. Its history is a prefix of the original's. The prefix lemma of
[chapter 3](30-archive.md) gives both directions: a pin of the original
resolves on the mirror to the same version, if the mirror has copied that
version; and whatever a pin resolves to on the mirror, it resolves to the
same on the original. Both assume that the copy really is a mirror (the
hypotheses `hid` and `hm`): they are about honest mirrors. A copy that may
not be one is the subject of the next section.

    /-- A mirror resolves the pins of the original that it has copied. -/
    theorem mirror_agrees {o m : Obj D} {t : List (Version D)}
        (hid : m.archive = o.archive ∧ m.id = o.id) (hm : o.versions = m.versions ++ t)
        {p : Pin D} {v : Version D} (hp : p.version ≤ m.versions.length)
        (h : resolveEntry hash (some (.live o)) p = .ok v) :
        resolveEntry hash (some (.live m)) p = .ok v :=
      resolveEntry_prefix hash hid hm (t' := []) (by simp) hp h

    /-- A mirror shows nothing that the original does not. -/
    theorem mirror_sound {o m : Obj D} {t : List (Version D)}
        (hid : m.archive = o.archive ∧ m.id = o.id) (hm : o.versions = m.versions ++ t)
        {p : Pin D} {v : Version D} (h : resolveEntry hash (some (.live m)) p = .ok v) :
        resolveEntry hash (some (.live o)) p = .ok v := by
      obtain ⟨hv, _⟩ := resolveEntry_live_ok hash h
      exact resolveEntry_prefix hash (o := m) (o' := o) (t := []) ⟨hid.1.symm, hid.2.symm⟩
        (by simp) hm (Obj.versionAt_bounds hv).2 h

## Mirrors stay mirrors

The two theorems above assume that the copy is a mirror. Valid steps make
sure of it: a mirror is created as a copy of a prefix of a live original,
and grows only by copying the original's next version
([chapter 5](45-worlds.md)). The invariant: every object kept by an archive
other than its own has an original, under the same identifier in its own
archive, which is not empty (it may have been taken down); and when the
original is live, it belongs to that archive and its history extends the
mirror's.

    /-- Every mirror is a prefix of its original. -/
    def MirrorsOk (w : World D) : Prop :=
      ∀ b x m, lookup w b x = some (.live m) → m.archive ≠ b →
        lookup w m.archive m.id ≠ none ∧
        ∀ o, lookup w m.archive m.id = some (.live o) →
          o.archive = m.archive ∧ ∃ t, o.versions = m.versions ++ t

Two facts about every step: an entry that is not empty stays so, and a live
entry after the step is the one before, or it with one more version.

    omit [DecidableEq D] in
    theorem Step.ne_none {w w' : World D} (hs : Step w w') {b : ArchiveId} {x : ObjectId}
        (h : lookup w b x ≠ none) : lookup w' b x ≠ none := by
      rcases hs.lookup_cases b x with h1 | h1 | ⟨o, v, _, h2⟩
      · rw [h1]; exact h
      · exact absurd h1 h
      · rw [h2]; simp

    omit [DecidableEq D] in
    theorem Step.live_back {w w' : World D} (hs : Step w w') {b : ArchiveId} {x : ObjectId}
        {o' : Obj D} (h : lookup w' b x = some (.live o')) (hne : lookup w b x ≠ none) :
        lookup w b x = some (.live o') ∨
          ∃ o v, lookup w b x = some (.live o) ∧ o' = o.append v := by
      rcases hs.lookup_cases b x with h1 | h1 | ⟨o, v, h1, h2⟩
      · left; rw [← h1]; exact h
      · exact absurd h1 hne
      · right
        rw [h2] at h
        exact ⟨o, v, h1, (Entry.live.inj (Option.some.inj h)).symm⟩

A mirror that the step did not touch stays a prefix of its original, which
can only have grown.

    omit [DecidableEq D] in
    theorem Step.mirror_kept {w w' : World D} (hs : Step w w') (hw : MirrorsOk w)
        {b : ArchiveId} {x : ObjectId} {m : Obj D} (hl : lookup w b x = some (.live m))
        (hb : m.archive ≠ b) :
        lookup w' m.archive m.id ≠ none ∧
        ∀ o, lookup w' m.archive m.id = some (.live o) →
          o.archive = m.archive ∧ ∃ t, o.versions = m.versions ++ t := by
      obtain ⟨hne, hpre⟩ := hw b x m hl hb
      refine ⟨hs.ne_none hne, fun o ho => ?_⟩
      rcases hs.live_back ho hne with h1 | ⟨o0, v, h1, rfl⟩
      · exact hpre o h1
      · obtain ⟨harch, t, ht⟩ := hpre o0 h1
        exact ⟨harch, t ++ [v], by simp [Obj.append, ht]⟩

    /-- **Valid steps keep mirrors mirrors.** -/
    theorem ValidStep.mirrorsOk {w w' : World D} (hs : ValidStep hash w w') (hw : MirrorsOk w) :
        MirrorsOk w' := by
      intro b x m hl hb
      have hstep := hs.toStep hash
      cases hs with
      | newArchive a ar ha hempty =>
        by_cases hba : b = a
        · subst hba; simp [lookup, hempty] at hl
        · have hl0 : lookup w b x = some (.live m) := by simpa [lookup, hba] using hl
          exact hstep.mirror_kept hw hl0 hb
      | create a ar oid o ha ho _ _ hhome =>
        rw [lookup_setEntry ha] at hl
        split at hl
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases hl
          rcases hhome with h | ⟨_, orig, hlo, harch, t, ht⟩
          · exact absurd h hb
          · have hsite : ¬ (m.archive = b ∧ m.id = x) := fun h => hb h.1
            have hlo' : lookup (setEntry w b x (.live m)) m.archive m.id = some (.live orig) := by
              rw [lookup_setEntry ha, if_no hsite]; exact hlo
            refine ⟨by rw [hlo']; simp, fun o2 ho2 => ?_⟩
            rw [hlo'] at ho2
            cases ho2
            exact ⟨harch, t, ht⟩
        · exact hstep.mirror_kept hw hl hb
      | append a ar oid o y ha ho _ _ _ _ _ hhome =>
        rw [lookup_setEntry ha] at hl
        split at hl
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases hl
          rcases hhome with h | ⟨orig, hlo, harch, t, ht⟩
          · exact absurd h hb
          · have hsite : ¬ ((o.append y).archive = b ∧ (o.append y).id = x) := fun h => hb h.1
            have hlo' : lookup (setEntry w b x (.live (o.append y))) (o.append y).archive
                (o.append y).id = some (.live orig) := by
              rw [lookup_setEntry ha, if_no hsite]; exact hlo
            refine ⟨by rw [hlo']; simp, fun o2 ho2 => ?_⟩
            rw [hlo'] at ho2
            cases ho2
            exact ⟨harch, t, by simp [Obj.append, ht]⟩
        · exact hstep.mirror_kept hw hl hb

A takedown keeps the invariant as well: it leaves every other entry as it
was, and the entry it changes becomes a tombstone, which is not empty.

    omit [DecidableEq D] in
    theorem takedown_mirrorsOk {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl : lookup w a oid = some (.live o)) (hw : MirrorsOk w) :
        MirrorsOk (takedown hash w a oid o) := by
      obtain ⟨ar, ha⟩ := lookup_some_archive hl
      intro b x m hm hb
      obtain ⟨_, hm0⟩ := lookup_takedown hash hl hm
      obtain ⟨hne, hpre⟩ := hw b x m hm0 hb
      refine ⟨?_, fun o2 ho2 => hpre o2 (lookup_takedown hash hl ho2).2⟩
      unfold takedown tombstone
      rw [lookup_setEntry ha]
      split
      · simp
      · exact hne

    theorem Event.mirrorsOk {w w' : World D} (he : Event hash w w') (hw : MirrorsOk w) :
        MirrorsOk w' := by
      cases he with
      | step hs => exact hs.mirrorsOk hash hw
      | takedown a oid o hl => exact takedown_mirrorsOk hash hl hw

    theorem Events.mirrorsOk {w : World D}
        (hs : Events hash (fun _ => (none : Option (Archive D))) w) : MirrorsOk w := by
      induction hs with
      | refl => intro b x m h; simp [lookup] at h
      | tail _ he ih => exact he.mirrorsOk hash ih

The theorem the invariant is for: in any world built by events, a mirror
resolves the pins of its live original that it has copied, to the same
version.

    /-- **Mirrors agree with their originals**, in every world built by events. -/
    theorem Events.mirror_resolves {w : World D}
        (hs : Events hash (fun _ => (none : Option (Archive D))) w)
        {b : ArchiveId} {x : ObjectId} {m o : Obj D} (hm : lookup w b x = some (.live m))
        (hb : m.archive ≠ b) (ho : lookup w m.archive m.id = some (.live o))
        {p : Pin D} {v : Version D} (hp : p.version ≤ m.versions.length)
        (h : resolveEntry hash (some (.live o)) p = .ok v) :
        resolveEntry hash (some (.live m)) p = .ok v := by
      obtain ⟨harch, t, ht⟩ := (Events.mirrorsOk hash hs b x m hm hb).2 o ho
      have hid : o.id = m.id := ((Events.sound hash hs).1 _ _ _ ho).id
      exact mirror_agrees hash ⟨harch.symm, hid.symm⟩ ht hp h

## Any copy, from anywhere

A reader who fetches an object from an archive they do not trust, or from a
disk found in a drawer, has no reason to believe that it is a mirror. The
pin is enough, unless the copy's inventory collides with the original's: if
the copy resolves the pin at all, it resolves it to the version of the
original. This is the use of SHA-512 in the specification.

    /-- **A pin authenticates any copy**, unless the inventories collide. -/
    theorem copy_authentic {o c : Obj D} {p : Pin D} {v u : Version D}
        (hcol : NoCollision hash (c.inventory p.version) (o.inventory p.version))
        (ho : resolveEntry hash (some (.live o)) p = .ok v)
        (hc : resolveEntry hash (some (.live c)) p = .ok u) : u = v := by
      obtain ⟨hvo, hdo⟩ := resolveEntry_live_ok hash ho
      obtain ⟨hvc, hdc⟩ := resolveEntry_live_ok hash hc
      have heq : c.inventory p.version = o.inventory p.version := hcol (hdc.trans hdo.symm)
      have heqv : c.versions.take p.version = o.versions.take p.version :=
        congrArg Inventory.versions heq
      obtain ⟨h1, _⟩ := Obj.versionAt_bounds hvo
      unfold Obj.versionAt at hvo hvc
      have hne : p.version ≠ 0 := by omega
      simp only [hne, ite_false] at hvo hvc
      have key : ∀ l : List (Version D), l[p.version - 1]? = (l.take p.version)[p.version - 1]? := by
        intro l; rw [List.getElem?_take]; simp; omega
      rw [key, heqv, ← key] at hvc
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

When it does not (the archive is gone, the object is lost or corrupted),
the first mirror that gives the pinned version gives the answer: the
mirrors listed before it are passed over when they give no version. First,
a list of results with no version in front does not change the first
version found.

    omit [DecidableEq D] in
    theorem firstOk_append {rs rs' : List (Resolution D)}
        (h : ∀ r ∈ rs, ∀ u, r ≠ .ok u) : firstOk (rs ++ rs') = firstOk rs' := by
      induction rs with
      | nil => rfl
      | cons r rs ih =>
        cases r with
        | ok u => exact absurd rfl (h _ (List.mem_cons_self ..) u)
        | _ => exact ih fun r hr => h r (List.mem_cons_of_mem _ hr)

    /-- **A mirror stands in for the member's archive**, when the member's
    archive and the mirrors listed before it give no version. -/
    theorem resolveVia_mirror {w : World D} {p : Pin D} {b : ArchiveId}
        {pre post : List ArchiveId} {m : Obj D} {v : Version D}
        (hbefore : ∀ b' ∈ p.archive :: pre, ∀ u, resolveAt hash w b' p ≠ .ok u)
        (hb : lookup w b p.object = some (.live m))
        (hm : resolveEntry hash (some (.live m)) p = .ok v) :
        resolveVia hash w p (pre ++ b :: post) = .ok v := by
      have h2 : resolveAt hash w b p = .ok v := by
        simp only [resolveAt, hb]; exact hm
      unfold resolveVia
      rw [← List.cons_append, List.map_append,
        firstOk_append (fun r hr u => by
          obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hr
          exact hbefore b' hb' u)]
      simp [firstOk, h2]

Whatever copy answers, the answer is right: a version found through the
mirrors is the version of the original, unless one of the copies consulted
collides with it (`copy_authentic`). A tombstone never gives a version, so
every answer comes from a live copy.

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
    version, whoever holds the copy, unless a copy consulted collides. -/
    theorem resolveVia_sound {w : World D} {p : Pin D} {ms : List ArchiveId} {o : Obj D}
        {u v : Version D}
        (hcol : ∀ b ∈ p.archive :: ms, ∀ c, lookup w b p.object = some (.live c) →
          NoCollision hash (c.inventory p.version) (o.inventory p.version))
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
        exact copy_authentic hash (hcol _ (List.mem_cons_self ..) c hc) ho h
      | some r =>
        rw [hf] at h
        simp only [Option.getD_some] at h
        subst h
        obtain ⟨b, hbm, hb⟩ := List.mem_map.mp (firstOk_mem hf)
        unfold resolveAt at hb
        obtain ⟨c, hc⟩ := resolveEntry_ok_live hash hb
        rw [hc] at hb
        exact copy_authentic hash (hcol b hbm c hc) ho hb

## Accepted copies

An accepted copy is a new document of the selection's archive `s`, under a
new identifier `cid`. Its first version holds the files of the revision
vetted, as document version 1; its description, depositor and message are
the selection's, given as parameters.

    omit [DecidableEq D] in
    /-- The first version of an accepted copy of `v`. -/
    def copyVersion (v : Version D) (description curator message : String) : Version D :=
      { documentVersion := 1, files := v.files, description, depositor := curator, message }

    omit [DecidableEq D] in
    /-- The accepted copy of the revision `v`, as object `cid` of archive `s`
    (section 10.5). -/
    def acceptedCopy (s : ArchiveId) (cid : ObjectId) (v : Version D)
        (description curator message : String) : Obj D :=
      { archive := s, id := cid, kind := .document,
        versions := [copyVersion v description curator message] }

It holds exactly the files vetted. It is a well-formed object without pins,
so creating it is a valid step whenever the identifier is free in the
selection's archive.

    omit [DecidableEq D] in
    theorem acceptedCopy_files (s : ArchiveId) (cid : ObjectId) (v : Version D) (d c m : String) :
        ∀ x ∈ (acceptedCopy s cid v d c m).versions, x.files = v.files := by
      simp [acceptedCopy, copyVersion]

    theorem acceptedCopy_wf (s : ArchiveId) (cid : ObjectId) (v : Version D) (d c m : String) :
        (acceptedCopy s cid v d c m).WF cid :=
      ⟨rfl, by simp [acceptedCopy], WellFormed.single rfl, by simp [acceptedCopy, copyVersion],
        by simp [acceptedCopy, copyVersion, Version.membersOk]⟩

    theorem acceptedCopy_valid {w : World D} {s : ArchiveId} {ar : Archive D} {cid : ObjectId}
        (hs : w s = some ar) (hfree : ar.entries cid = none) (v : Version D) (d c m : String) :
        ValidStep hash w (setEntry w s cid (.live (acceptedCopy s cid v d c m))) :=
      .create w s ar cid _ hs hfree (acceptedCopy_wf s cid v d c m)
        (by simp [acceptedCopy, copyVersion, Version.pins]) (Or.inl rfl)

The copy is kept by the selection's archive, so a takedown of the original
leaves it alone: its pin still resolves to its first version. This is what
accepted copies are for.

    /-- **An accepted copy survives the original.** -/
    theorem acceptedCopy_survives {w : World D} {a s : ArchiveId} {oid cid : ObjectId}
        {o : Obj D} {v : Version D} {d c m : String} (hl : lookup w a oid = some (.live o))
        (hc : lookup w s cid = some (.live (acceptedCopy s cid v d c m)))
        (hdiff : ¬ (s = a ∧ cid = oid)) :
        resolve hash (takedown hash w a oid o)
            ⟨s, cid, 1, hash ((acceptedCopy s cid v d c m).inventory 1)⟩ =
          .ok (copyVersion v d c m) := by
      rw [takedown_other hash hl hdiff]
      unfold resolve
      simp only [hc]
      exact resolveEntry_live_of hash (by simp [Obj.versionAt, acceptedCopy]) rfl

And it is never taken for the original. Its inventories name another object
(another archive, or another identifier), so they differ from the
original's, and, unless they collide, so do their digests: a pin of the
original cannot resolve on the copy. This is why section 10.5 forbids
listing an accepted copy among the mirrors.

    /-- **An accepted copy is not a mirror.** -/
    theorem acceptedCopy_not_mirror {o c : Obj D} {p : Pin D} {v u : Version D}
        (hother : ¬ (c.archive = o.archive ∧ c.id = o.id))
        (hcol : NoCollision hash (c.inventory p.version) (o.inventory p.version))
        (ho : resolveEntry hash (some (.live o)) p = .ok v) :
        resolveEntry hash (some (.live c)) p ≠ .ok u := by
      intro hc
      obtain ⟨_, hdo⟩ := resolveEntry_live_ok hash ho
      obtain ⟨_, hdc⟩ := resolveEntry_live_ok hash hc
      have heq := hcol (hdc.trans hdo.symm)
      exact hother ⟨congrArg Inventory.archive heq, congrArg Inventory.id heq⟩

    end OpenSheaf
