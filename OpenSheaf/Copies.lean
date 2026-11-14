-- Generated from literate/48-copies.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Worlds

namespace OpenSheaf

variable {D : Type} [DecidableEq D] (hash : Hash D)

omit [DecidableEq D] in
/-- The inventories `i` and `j` do not collide. -/
def NoCollision (i j : Inventory D) : Prop := hash i = hash j → i = j

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

theorem resolveVia_own {w : World D} {p : Pin D} (ms : List ArchiveId) {v : Version D}
    (h : resolve hash w p = .ok v) : resolveVia hash w p ms = .ok v := by
  have : resolveAt hash w p.archive p = .ok v := h
  simp [resolveVia, this, firstOk]

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

omit [DecidableEq D] in
theorem acceptedCopy_files (s : ArchiveId) (cid : ObjectId) (v : Version D) (d c m : String) :
    ∀ x ∈ (acceptedCopy s cid v d c m).versions, x.files = v.files := by
  simp [acceptedCopy, copyVersion]

theorem acceptedCopy_wf (s : ArchiveId) (cid : ObjectId) (v : Version D) (d c m : String) :
    (acceptedCopy s cid v d c m).WF cid :=
  ⟨rfl, by simp [acceptedCopy], WellFormed.single rfl, by simp [acceptedCopy, copyVersion]⟩

theorem acceptedCopy_valid {w : World D} {s : ArchiveId} {ar : Archive D} {cid : ObjectId}
    (hs : w s = some ar) (hfree : ar.entries cid = none) (v : Version D) (d c m : String) :
    ValidStep hash w (setEntry w s cid (.live (acceptedCopy s cid v d c m))) :=
  .create w s ar cid _ hs hfree (acceptedCopy_wf s cid v d c m)
    (by simp [acceptedCopy, copyVersion, Version.pins])

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
