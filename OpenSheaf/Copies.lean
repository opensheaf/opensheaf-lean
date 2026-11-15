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

/-- Every mirror is a prefix of its original. -/
def MirrorsOk (w : World D) : Prop :=
  ∀ b x m, lookup w b x = some (.live m) → m.archive ≠ b →
    lookup w m.archive m.id ≠ none ∧
    ∀ o, lookup w m.archive m.id = some (.live o) →
      o.archive = m.archive ∧ ∃ t, o.versions = m.versions ++ t

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

omit [DecidableEq D] in
theorem mirror_written {w : World D} {b : ArchiveId} {ar : Archive D} {x : ObjectId}
    (ha : w b = some ar) {m : Obj D} (hb : m.archive ≠ b) (hm : MirrorOf w m) :
    lookup (setEntry w b x (.live m)) m.archive m.id ≠ none ∧
    ∀ o, lookup (setEntry w b x (.live m)) m.archive m.id = some (.live o) →
      o.archive = m.archive ∧ ∃ t, o.versions = m.versions ++ t := by
  obtain ⟨orig, hlo, harch, t, ht⟩ := hm
  have hlo' : lookup (setEntry w b x (.live m)) m.archive m.id = some (.live orig) := by
    rw [lookup_setEntry ha, if_no fun h => hb h.1]; exact hlo
  refine ⟨by rw [hlo']; simp, fun o2 ho2 => ?_⟩
  rw [hlo'] at ho2
  cases ho2
  exact ⟨harch, t, ht⟩

/-- **Valid steps keep mirrors mirrors.** -/
theorem ValidStep.mirrorsOk {w w' : World D} (hs : ValidStep hash w w') (hw : MirrorsOk w) :
    MirrorsOk w' := by
  intro b x m hl hb
  have hstep := hs.toStep hash
  cases hs with
  | newArchive a ar ha hempty =>
    rw [lookup_newArchive ha hempty] at hl
    exact hstep.mirror_kept hw hl hb
  | create a ar oid o ha ho _ _ hhome =>
    rw [lookup_setEntry ha] at hl
    split at hl
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases hl
      exact mirror_written ha hb (hhome.resolve_left hb)
    · exact hstep.mirror_kept hw hl hb
  | append a ar oid o y ha ho _ _ _ _ _ hhome =>
    rw [lookup_setEntry ha] at hl
    split at hl
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases hl
      exact mirror_written ha hb (hhome.resolve_left hb)
    · exact hstep.mirror_kept hw hl hb

omit [DecidableEq D] in
theorem takedown_mirrorsOk {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) (hw : MirrorsOk w) :
    MirrorsOk (takedown hash w a oid o) := by
  intro b x m hm hb
  obtain ⟨_, hm0⟩ := lookup_takedown hash hl hm
  obtain ⟨hne, hpre⟩ := hw b x m hm0 hb
  refine ⟨?_, fun o2 ho2 => hpre o2 (lookup_takedown hash hl ho2).2⟩
  rw [lookup_takedown_eq hash hl]
  split
  · simp
  · exact hne

theorem Event.mirrorsOk {w w' : World D} (he : Event hash w w') (hw : MirrorsOk w) :
    MirrorsOk w' := by
  cases he with
  | step hs => exact hs.mirrorsOk hash hw
  | takedown a oid o hl => exact takedown_mirrorsOk hash hl hw

theorem Events.mirrorsOk {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) : MirrorsOk w :=
  hs.invariant _ (·.mirrorsOk hash) fun b x m h => by simp [lookup] at h

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

omit [DecidableEq D] in
/-- **Copies agree.** Any two live objects with the same name, wherever they
are kept, have histories of which one is a prefix of the other. -/
def CopiesAgree (w : World D) : Prop :=
  ∀ b x m b' x' m', lookup w b x = some (.live m) → lookup w b' x' = some (.live m') →
    m.archive = m'.archive → m.id = m'.id → Comparable m.versions m'.versions

omit [DecidableEq D] in
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

omit [DecidableEq D] in
theorem takedown_copiesAgree {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) (hw : CopiesAgree w) :
    CopiesAgree (takedown hash w a oid o) :=
  fun _ _ _ _ _ _ h h' => hw _ _ _ _ _ _ (lookup_takedown hash hl h).2 (lookup_takedown hash hl h').2

theorem Event.copiesAgree {w w' : World D} (he : Event hash w w')
    (hw : SoundWorld hash w ∧ MirrorsOk w ∧ CopiesAgree w) :
    SoundWorld hash w' ∧ MirrorsOk w' ∧ CopiesAgree w' := by
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨he.sound hash h1, he.mirrorsOk hash h2, ?_⟩
  cases he with
  | step hs => exact hs.copiesAgree hash h1 h2 h3
  | takedown a oid o hl => exact takedown_copiesAgree hash hl h3

/-- **Copies agree in every world built by events**, takedowns included. -/
theorem Events.copiesAgree {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) : CopiesAgree w :=
  (hs.invariant _ (fun he hw => Event.copiesAgree hash he hw)
    ⟨SoundWorld.empty hash, fun _ _ _ h => by simp [lookup] at h,
     fun _ _ _ _ _ _ h => by simp [lookup] at h⟩).2.2

/-- **A pin authenticates any copy**, unless the inventories collide. -/
theorem copy_authentic {o c : Obj D} {p : Pin D} {v u : Version D}
    (hcol : NoCollision hash (c.inventory p.version) (o.inventory p.version))
    (ho : resolveEntry hash (some (.live o)) p = .ok v)
    (hc : resolveEntry hash (some (.live c)) p = .ok u) : u = v := by
  obtain ⟨hvo, hdo⟩ := resolveEntry_live_ok hash ho
  obtain ⟨hvc, hdc⟩ := resolveEntry_live_ok hash hc
  have heq : c.inventory p.version = o.inventory p.version := hcol (hdc.trans hdo.symm)
  rw [versionAt_congr_take (congrArg Inventory.versions heq), hvo] at hvc
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
/-- The first version of an accepted copy of `v`, whose pin is `src`. -/
def copyVersion (v : Version D) (src : Pin D) (description curator message : String) :
    Version D :=
  { documentVersion := 1, files := v.files, description, refs := v.refs, source := some src,
    depositor := curator, message }

omit [DecidableEq D] in
/-- The accepted copy of the revision `v`, pinned by `src`, as object `cid` of
archive `s` (section 10.5). -/
def acceptedCopy (s : ArchiveId) (cid : ObjectId) (src : Pin D) (v : Version D)
    (description curator message : String) : Obj D :=
  { archive := s, id := cid, kind := .document,
    versions := [copyVersion v src description curator message] }

omit [DecidableEq D] in
theorem acceptedCopy_files (s : ArchiveId) (cid : ObjectId) (src : Pin D) (v : Version D)
    (d c m : String) : ∀ x ∈ (acceptedCopy s cid src v d c m).versions, x.files = v.files := by
  simp [acceptedCopy, copyVersion]

theorem acceptedCopy_wf (s : ArchiveId) (cid : ObjectId) (src : Pin D) (v : Version D)
    (d c m : String) : (acceptedCopy s cid src v d c m).WF cid :=
  ⟨rfl, by simp [acceptedCopy], WellFormed.single rfl, by simp [acceptedCopy, copyVersion],
    by simp [acceptedCopy, copyVersion, Version.membersOk], StatusOk.single _⟩

theorem acceptedCopy_valid {w : World D} {s : ArchiveId} {ar : Archive D} {cid : ObjectId}
    (hs : w s = some ar) (hfree : ar.entries cid = none) (src : Pin D) (v : Version D)
    (d c m : String) (hrefs : ∀ r ∈ v.refs, Held hash w r.pin) :
    ValidStep hash w (setEntry w s cid (.live (acceptedCopy s cid src v d c m))) :=
  .create w s ar cid _ hs hfree (acceptedCopy_wf s cid src v d c m)
    (by
      intro x hx p hp
      simp only [acceptedCopy, List.mem_singleton] at hx
      subst hx
      simp only [copyVersion, Version.pins, List.nil_append, List.mem_map] at hp
      obtain ⟨r, hr, rfl⟩ := hp
      exact hrefs r hr)
    (Or.inl rfl) (fun _ => by simp [HeadFollows, acceptedCopy, copyVersion, Version.FollowsHeads])

/-- The first version of `c` holds exactly the files of its source. -/
def CopyChecks (w : World D) (c : Obj D) : Prop :=
  ∀ x src, c.versionAt 1 = some x → x.source = some src →
    ∃ v, resolve hash w src = .ok v ∧ x.files = v.files

/-- **An accepted copy passes the check of section 14.** -/
theorem acceptedCopy_checks {w w' : World D} (hs : Steps w w') {src : Pin D} {v : Version D}
    (hsrc : resolve hash w src = .ok v) {c : Obj D} {d cu m : String}
    (h1 : c.versionAt 1 = some (copyVersion v src d cu m)) : CopyChecks hash w' c := by
  intro x p hx hp
  rw [h1] at hx
  cases hx
  simp only [copyVersion, Option.some.injEq] at hp
  subst hp
  exact ⟨v, Steps.resolve_ok hash hs hsrc, rfl⟩

/-- **An accepted copy survives the original.** -/
theorem acceptedCopy_survives {w : World D} {a s : ArchiveId} {oid cid : ObjectId}
    {o c : Obj D} {x : Version D} (hl : lookup w a oid = some (.live o))
    (hc : lookup w s cid = some (.live c)) (h1 : c.versionAt 1 = some x)
    (hdiff : ¬ (s = a ∧ cid = oid)) :
    resolve hash (takedown hash w a oid o) ⟨s, cid, 1, hash (c.inventory 1)⟩ = .ok x := by
  rw [takedown_other hash hl hdiff]
  unfold resolve
  simp only [hc]
  exact resolveEntry_live_of hash h1 rfl

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
