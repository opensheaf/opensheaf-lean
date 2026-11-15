-- Generated from literate/65-impossible.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Copies

namespace OpenSheaf

variable {D : Type} [DecidableEq D] (hash : Hash D)

/-- **A pin cannot change its meaning.** -/
theorem pin_meaning_fixed {w w' : World D} (hs : Steps w w') {p : Pin D} {v u : Version D}
    (hp : resolve hash w p = .ok v) (hne : u ≠ v) : resolve hash w' p ≠ .ok u := by
  rw [Steps.resolve_ok hash hs hp]
  intro h
  cases h
  exact hne rfl

omit [DecidableEq D] in
/-- **History cannot be rewritten by any steps.** -/
theorem history_not_rewritten {w w' : World D} (hs : Steps w w') {a : ArchiveId}
    {oid : ObjectId} {o o' : Obj D} (hl : lookup w a oid = some (.live o))
    (hl' : lookup w' a oid = some (.live o'))
    (hrew : o'.versions.take o.versions.length ≠ o.versions) : False := by
  obtain ⟨o2, h2, _, _, t, ht⟩ := Steps.live_grows hs hl
  rw [hl'] at h2
  cases h2
  apply hrew
  rw [ht, List.take_append_of_le_length (Nat.le_refl _), List.take_length]

/-- **Tampering is detected.** If an archive replaces an object by one whose
history differs up to version `p.version`, a pin of that version made
before resolves to no version at all. -/
theorem tamper_detected {w : World D}
    {a : ArchiveId} {oid : ObjectId} {o o' : Obj D} (hl : lookup w a oid = some (.live o))
    {p : Pin D} {v : Version D} (hpa : p.archive = a ∧ p.object = oid)
    (hp : resolve hash w p = .ok v) (hdiff : o'.inventory p.version ≠ o.inventory p.version)
    (hcol : NoCollision hash (o'.inventory p.version) (o.inventory p.version))
    (u : Version D) : resolve hash (setEntry w a oid (.live o')) p ≠ .ok u := by
  obtain ⟨ar, ha⟩ := lookup_some_archive hl
  intro h
  unfold resolve at h hp
  rw [lookup_setEntry ha] at h
  simp only [hpa, and_self, ite_true] at h
  rw [hpa.1, hpa.2, hl] at hp
  obtain ⟨_, hd⟩ := resolveEntry_live_ok hash hp
  obtain ⟨_, hd'⟩ := resolveEntry_live_ok hash h
  exact hdiff (hcol (hd'.trans hd.symm))

omit [DecidableEq D] in
/-- **A tombstoned identifier is never reused.** -/
theorem no_reuse {w w' : World D} (hs : Steps w w') {a : ArchiveId} {oid : ObjectId}
    {n : Nat} {d : D} (h : lookup w a oid = some (.tomb n d)) (o : Obj D) :
    lookup w' a oid ≠ some (.live o) := by
  rw [Steps.tomb_stays hs h]
  intro h'
  cases h'

/-- **One document version, one content.** -/
theorem one_number_one_content {l : List (Version D)} (h : WellFormed l)
    {v u : Version D} (hv : v ∈ l) (hu : u ∈ l)
    (heq : v.documentVersion = u.documentVersion) : sameContent v u = true := by
  induction l using snoc_induction generalizing v u with
  | nil => cases hv
  | snoc l x ih =>
    obtain ⟨hwf, hx⟩ := h.init
    have key : ∀ y ∈ l, y.documentVersion = x.documentVersion → sameContent y x = true := by
      intro y hy hyx
      rcases hx with ⟨z, hz, hzx, hxz⟩ | ⟨_, hxn⟩
      · have hyz := ih hwf hy hz (hyx.trans hxz)
        rw [sameContent_iff] at hyz hzx ⊢
        exact ⟨fun f => (hyz.1 f).trans (hzx.1 f), hyz.2.trans hzx.2⟩
      · have := le_docCount hy; omega
    simp only [List.mem_append, List.mem_singleton] at hv hu
    rcases hv with hv | rfl <;> rcases hu with hu | rfl
    · exact ih hwf hv hu heq
    · exact key v hv heq
    · have := key u hu heq.symm
      rw [sameContent_iff] at this ⊢
      exact ⟨fun f => (this.1 f).symm, this.2.symm⟩
    · exact sameContent_self _

theorem sameContent_symm {v u : Version D} (h : sameContent v u = true) :
    sameContent u v = true := by
  rw [sameContent_iff] at *
  exact ⟨fun f => (h.1 f).symm, h.2.symm⟩

theorem sameContent_trans {v u t : Version D} (h1 : sameContent v u = true)
    (h2 : sameContent u t = true) : sameContent v t = true := by
  rw [sameContent_iff] at *
  exact ⟨fun f => (h1.1 f).trans (h2.1 f), h1.2.trans h2.2⟩

/-- **One content, one document version.** -/
theorem one_content_one_number {l : List (Version D)} (h : WellFormed l)
    {v u : Version D} (hv : v ∈ l) (hu : u ∈ l) (heq : sameContent v u = true) :
    v.documentVersion = u.documentVersion := by
  induction l using snoc_induction generalizing v u with
  | nil => cases hv
  | snoc l x ih =>
    obtain ⟨hwf, hx⟩ := h.init
    have key : ∀ y ∈ l, sameContent y x = true → y.documentVersion = x.documentVersion := by
      intro y hy hyx
      rcases hx with ⟨z, hz, hzx, hxz⟩ | ⟨hnew, _⟩
      · exact (ih hwf hy hz (sameContent_trans hyx (sameContent_symm hzx))).trans hxz.symm
      · rw [hnew y hy] at hyx; cases hyx
    simp only [List.mem_append, List.mem_singleton] at hv hu
    rcases hv with hv | rfl <;> rcases hu with hu | rfl
    · exact ih hwf hv hu heq
    · exact key v hv heq
    · exact (key u hu (sameContent_symm heq)).symm
    · rfl

/-- **Document versions have no gaps.** -/
theorem no_gaps {l : List (Version D)} (h : WellFormed l) {k : Nat} (hk1 : 1 ≤ k)
    (hk : k ≤ docCount l) : ∃ v ∈ l, v.documentVersion = k := by
  induction l using snoc_induction generalizing k with
  | nil => simp [docCount] at hk; omega
  | snoc l x ih =>
    obtain ⟨hwf, hx⟩ := h.init
    rw [docCount_append] at hk
    by_cases hkl : k ≤ docCount l
    · obtain ⟨v, hv, hvk⟩ := ih hwf hk1 hkl
      exact ⟨v, by simp [hv], hvk⟩
    · rcases hx with ⟨z, hz, _, hxz⟩ | ⟨_, hxn⟩
      · have := le_docCount hz; omega
      · exact ⟨x, by simp, by omega⟩

/-- Document versions are numbered from 1. -/
theorem doc_pos {l : List (Version D)} (h : WellFormed l) {v : Version D} (hv : v ∈ l) :
    1 ≤ v.documentVersion := by
  induction l using snoc_induction generalizing v with
  | nil => cases hv
  | snoc l x ih =>
    obtain ⟨hwf, hx⟩ := h.init
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact ih hwf hv
    · rcases hx with ⟨z, hz, _, hxz⟩ | ⟨_, hxn⟩
      · rw [hxz]; exact ih hwf hz
      · omega

/-- Version `n` of object `oid` of archive `a`. -/
abbrev Site := ArchiveId × ObjectId × Nat

/-- A version exists at the site. -/
def Live (w : World D) (s : Site) : Prop :=
  ∃ o v, lookup w s.1 s.2.1 = some (.live o) ∧ o.versionAt s.2.2 = some v

/-- The version at `s` holds a pin that resolves, to the version at `t`. -/
def PinsTo (w : World D) (s t : Site) : Prop :=
  ∃ o v p, lookup w s.1 s.2.1 = some (.live o) ∧ o.versionAt s.2.2 = some v ∧
    p ∈ v.pins ∧ (∃ u, resolve hash w p = .ok u) ∧ t = (p.archive, p.object, p.version)

/-- A chain of one or more steps of a relation. -/
inductive Chain {α : Type} (r : α → α → Prop) : α → α → Prop
  | single {a b : α} : r a b → Chain r a b
  | cons {a b c : α} : r a b → Chain r b c → Chain r a c

theorem live_of_resolve {w : World D} {p : Pin D} {u : Version D}
    (h : resolve hash w p = .ok u) : Live w (p.archive, p.object, p.version) := by
  unfold resolve at h
  obtain ⟨c, hc⟩ := resolveEntry_ok_live hash h
  rw [hc] at h
  exact ⟨c, u, hc, (resolveEntry_live_ok hash h).1⟩

/-- A numbering of the versions in which pins go down. -/
def Ranked (w : World D) : Prop :=
  ∃ (rank : Site → Nat) (N : Nat), (∀ s, Live w s → rank s < N) ∧
    ∀ s t, PinsTo hash w s t → rank t < rank s

theorem Ranked.chain_lt {w : World D} {rank : Site → Nat}
    (hr : ∀ s t, PinsTo hash w s t → rank t < rank s) {s t : Site}
    (h : Chain (PinsTo hash w) s t) : rank t < rank s := by
  induction h with
  | single h => exact hr _ _ h
  | cons h _ ih => exact Nat.lt_trans ih (hr _ _ h)

theorem Ranked.no_cycle {w : World D} (hr : Ranked hash w) (s : Site) :
    ¬ Chain (PinsTo hash w) s s := by
  obtain ⟨rank, _, _, hdown⟩ := hr
  intro h
  exact Nat.lt_irrefl _ (Ranked.chain_lt hash hdown h)

theorem pinsTo_old {w w' : World D} (hw : SoundWorld hash w) (hstep : Step w w')
    {s t : Site} {o : Obj D} {v : Version D} {p : Pin D}
    (hl : lookup w s.1 s.2.1 = some (.live o)) (hv : o.versionAt s.2.2 = some v)
    (hp : p ∈ v.pins) (ht : t = (p.archive, p.object, p.version)) {u : Version D}
    (hu : resolve hash w' p = .ok u) : PinsTo hash w s t := by
  rcases hw.2 _ _ _ hl v (versionAt_mem hv) p hp with ⟨u', hu'⟩ | hr
  · exact ⟨o, v, p, hl, hv, hp, ⟨u', hu'⟩, ht⟩
  · rw [Step.resolve_removed hash hstep hr] at hu; cases hu

theorem ValidStep.new_pins {w w' : World D} (hs : ValidStep hash w w') {b : ArchiveId}
    {x : ObjectId} {n : Nat} {o' : Obj D} {v : Version D}
    (hl' : lookup w' b x = some (.live o')) (hv : o'.versionAt n = some v)
    (hnew : ¬ Live w (b, x, n)) {p : Pin D} (hp : p ∈ v.pins) :
    Held hash w p := by
  cases hs with
  | newArchive a ar ha hempty =>
    rw [lookup_newArchive ha hempty] at hl'
    exact absurd ⟨o', v, hl', hv⟩ hnew
  | create a ar oid o ha ho _ hpins _ =>
    rw [lookup_setEntry ha] at hl'
    split at hl'
    · cases hl'; exact (hpins v (versionAt_mem hv) p hp).held
    · exact absurd ⟨o', v, hl', hv⟩ hnew
  | append a ar oid o y ha ho _ _ _ _ hpins _ =>
    rw [lookup_setEntry ha] at hl'
    split at hl'
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases hl'
      rcases versionAt_append hv with hv | ⟨_, rfl⟩
      · exact absurd ⟨o, v, by simp [lookup, ha, ho], hv⟩ hnew
      · exact (hpins p hp).held
    · exact absurd ⟨o', v, hl', hv⟩ hnew

theorem ValidStep.ranked {w w' : World D} (hs : ValidStep hash w w') (hw : SoundWorld hash w)
    (hr : Ranked hash w) : Ranked hash w' := by
  classical
  obtain ⟨rank, N, hlive, hdown⟩ := hr
  have hstep := hs.toStep hash
  refine ⟨fun s => if Live w s then rank s else N, N + 1, fun s _ => ?_, ?_⟩
  · dsimp only; split
    · exact Nat.lt_succ_of_lt (hlive s ‹_›)
    · exact Nat.lt_succ_self N
  · rintro ⟨b, x, n⟩ t ⟨o', v, p, hl', hv, hp, ⟨u, hu⟩, ht⟩
    dsimp only
    by_cases hold : Live w (b, x, n)
    · obtain ⟨o, v0, hl, hv0⟩ := hold
      obtain ⟨o2, h2, _, _, t2, ht2⟩ := hstep.live_grows hl
      rw [hl'] at h2; cases h2
      have := versionAt_prefix (t := []) (by simp) ht2 (Obj.versionAt_bounds hv0).2 hv0
      rw [hv] at this; cases this
      have hpt := pinsTo_old hash hw hstep hl hv0 hp ht hu
      have htl : Live w t := by
        obtain ⟨_, _, q, _, _, _, ⟨u', hu'⟩, hq⟩ := hpt
        rw [hq]; exact live_of_resolve hash hu'
      rw [if_yes htl, if_yes (show Live w (b, x, n) from ⟨o, v, hl, hv0⟩)]
      exact hdown _ _ hpt
    · rcases hs.new_pins hash hl' hv hold hp with ⟨u0, hu0⟩ | hr0
      · have htl : Live w t := ht ▸ live_of_resolve hash hu0
        rw [if_yes htl, if_no hold]
        exact hlive t htl
      · rw [Step.resolve_removed hash hstep hr0] at hu; cases hu

theorem takedown_ranked {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) (hr : Ranked hash w) :
    Ranked hash (takedown hash w a oid o) := by
  obtain ⟨rank, N, hlive, hdown⟩ := hr
  refine ⟨rank, N, fun s ⟨o', v, h, hv⟩ =>
    hlive s ⟨o', v, (lookup_takedown hash hl h).2, hv⟩, ?_⟩
  rintro s t ⟨o', v, p, h, hv, hp, ⟨u, hu⟩, ht⟩
  have hpa : ¬ (p.archive = a ∧ p.object = oid) := by
    intro hpa; rw [takedown_removed hash hl hpa] at hu; cases hu
  rw [takedown_other hash hl hpa] at hu
  exact hdown s t ⟨o', v, p, (lookup_takedown hash hl h).2, hv, hp, ⟨u, hu⟩, ht⟩

theorem Events.ranked {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) :
    SoundWorld hash w ∧ Ranked hash w := by
  refine hs.invariant (fun w => SoundWorld hash w ∧ Ranked hash w) ?_
    ⟨SoundWorld.empty hash, fun _ => 0, 0, ?_, ?_⟩
  · intro _ _ he ih
    cases he with
    | step hs => exact ⟨hs.sound hash ih.1, hs.ranked hash ih.1 ih.2⟩
    | takedown a oid o hl => exact ⟨takedown_sound hash hl ih.1, takedown_ranked hash hl ih.2⟩
  · rintro s ⟨o, v, hl, _⟩; simp [lookup] at hl
  · rintro s t ⟨o, v, p, hl, _⟩; simp [lookup] at hl

/-- **Pins cannot form cycles** (section 10.2), in any world built by events
(valid steps and takedowns), whatever the digest function. -/
theorem no_cycles_events {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) (s : Site) :
    ¬ Chain (PinsTo hash w) s s :=
  (hs.ranked hash).2.no_cycle hash s

theorem ValidSteps.toEvents {w w' : World D} (hs : ValidSteps hash w w') :
    Events hash w w' :=
  hs.mono .step

/-- **Pins cannot form cycles**, in any world built by valid steps. -/
theorem no_cycles {w : World D}
    (hs : ValidSteps hash (fun _ => (none : Option (Archive D))) w) (s : Site) :
    ¬ Chain (PinsTo hash w) s s :=
  no_cycles_events hash hs.toEvents s

/-- The head of a live object is withdrawn. -/
def HeadWithdrawn (w : World D) (a : ArchiveId) (oid : ObjectId) : Prop :=
  ∃ o, lookup w a oid = some (.live o) ∧ headStatus o.versions = .withdrawn

/-- **A withdrawal cannot be undone** by valid steps. -/
theorem ValidStep.withdrawn_stays {w w' : World D} (hs : ValidStep hash w w')
    {a : ArchiveId} {oid : ObjectId} (h : HeadWithdrawn w a oid) : HeadWithdrawn w' a oid := by
  obtain ⟨o, hl, hst⟩ := h
  cases hs with
  | newArchive b ar hb hempty =>
    exact ⟨o, by rw [lookup_newArchive hb hempty]; exact hl, hst⟩
  | create b ar c o' hb hc _ _ =>
    refine ⟨o, ?_, hst⟩
    rw [lookup_setEntry hb]
    split
    · rename_i hbc
      obtain ⟨rfl, rfl⟩ := hbc
      simp [lookup, hb, hc] at hl
    · exact hl
  | append b ar c o' y hb hc _ hst' _ _ =>
    by_cases hbc : a = b ∧ oid = c
    · obtain ⟨rfl, rfl⟩ := hbc
      have hoo : some (Entry.live o') = some (Entry.live o) := by
        rw [← hl]; simp [lookup, hb, hc]
      have := Entry.live.inj (Option.some.inj hoo)
      subst this
      refine ⟨o'.append y, by rw [lookup_setEntry hb]; simp, ?_⟩
      simp [headStatus, Obj.append, hst' hst]
    · exact ⟨o, by rw [lookup_setEntry hb, if_no hbc]; exact hl, hst⟩

theorem ValidSteps.withdrawn_stays {w w' : World D} (hs : ValidSteps hash w w')
    {a : ArchiveId} {oid : ObjectId} (h : HeadWithdrawn w a oid) : HeadWithdrawn w' a oid :=
  hs.invariant _ (·.withdrawn_stays hash) h

end OpenSheaf
