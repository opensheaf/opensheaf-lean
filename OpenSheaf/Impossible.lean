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

section Numbers

omit [DecidableEq D] in
theorem snoc_induction {α : Type} {motive : List α → Prop} (nil : motive [])
    (snoc : ∀ l x, motive l → motive (l ++ [x])) (l : List α) : motive l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons x r ih => rw [List.reverse_cons]; exact snoc _ _ ih

theorem WellFormed.init {l : List (Version D)} {x : Version D}
    (h : WellFormed (l ++ [x])) : WellFormed l ∧ Extends l x := by
  constructor
  · intro i hi
    have := h i (by simp; omega)
    rwa [List.take_append_of_le_length (Nat.le_of_lt hi), List.getElem_append_left hi] at this
  · have := h l.length (by simp)
    simpa using this

omit [DecidableEq D] in
theorem docCount_append (l : List (Version D)) (x : Version D) :
    docCount (l ++ [x]) = max (docCount l) x.documentVersion := by
  induction l with
  | nil => simp [docCount]
  | cons v l ih => simp only [List.cons_append, docCount, ih, Nat.max_assoc]

omit [DecidableEq D] in
theorem le_docCount {l : List (Version D)} {v : Version D} (h : v ∈ l) :
    v.documentVersion ≤ docCount l := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    simp only [docCount]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

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

end Numbers

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

omit [DecidableEq D] in
theorem versionAt_append {o : Obj D} {x v : Version D} {n : Nat}
    (h : (o.append x).versionAt n = some v) :
    o.versionAt n = some v ∨ (n = o.versions.length + 1 ∧ v = x) := by
  unfold Obj.versionAt Obj.append at *
  split at h
  · contradiction
  · rename_i hn
    simp only [hn, ite_false]
    by_cases hlt : n - 1 < o.versions.length
    · left; rwa [List.getElem?_append_left hlt] at h
    · right
      rw [List.getElem?_append_right (by omega)] at h
      have : n - 1 - o.versions.length = 0 := by
        cases hk : n - 1 - o.versions.length with
        | zero => rfl
        | succ k => rw [hk] at h; simp at h
      rw [this] at h
      simp at h
      exact ⟨by omega, h.symm⟩

omit [DecidableEq D] in
theorem versionAt_mem {o : Obj D} {n : Nat} {v : Version D} (h : o.versionAt n = some v) :
    v ∈ o.versions := by
  unfold Obj.versionAt at h
  split at h
  · contradiction
  · exact List.mem_of_getElem? h

omit [DecidableEq D] in
theorem not_live_next {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) : ¬ Live w (a, oid, o.versions.length + 1) := by
  rintro ⟨o', v, hl', hv⟩
  rw [hl] at hl'
  cases hl'
  simp [Obj.versionAt] at hv

omit [DecidableEq D] in
theorem not_live_empty {w : World D} {a : ArchiveId} {oid : ObjectId}
    (hl : lookup w a oid = none) (n : Nat) : ¬ Live w (a, oid, n) := by
  rintro ⟨o', v, hl', _⟩
  rw [hl] at hl'
  cases hl'

theorem pinsTo_old {w w' : World D} (hw : SoundWorld hash w) (hstep : Step w w')
    {s t : Site} {o : Obj D} {v : Version D} {p : Pin D}
    (hl : lookup w s.1 s.2.1 = some (.live o)) (hv : o.versionAt s.2.2 = some v)
    (hp : p ∈ v.pins) (ht : t = (p.archive, p.object, p.version)) {u : Version D}
    (hu : resolve hash w' p = .ok u) : PinsTo hash w s t := by
  rcases hw.2 _ _ _ hl v (versionAt_mem hv) p hp with ⟨u', hu'⟩ | hr
  · exact ⟨o, v, p, hl, hv, hp, ⟨u', hu'⟩, ht⟩
  · rw [Step.resolve_removed hash hstep hr] at hu; cases hu

theorem ValidStep.ranked {w w' : World D} (hs : ValidStep hash w w') (hw : SoundWorld hash w)
    (hr : Ranked hash w) : Ranked hash w' := by
  obtain ⟨rank, N, hlive, hdown⟩ := hr
  have hstep := hs.toStep hash
  cases hs with
  | newArchive a ar ha hempty =>
    have back : ∀ b x e, lookup (fun c => if c = a then some ar else w c) b x = some e →
        lookup w b x = some e := by
      intro b x e h
      by_cases hb : b = a
      · subst hb; simp [lookup, hempty] at h
      · simpa [lookup, hb] using h
    refine ⟨rank, N, fun s ⟨o, v, hl, hv⟩ => hlive s ⟨o, v, back _ _ _ hl, hv⟩, ?_⟩
    rintro s t ⟨o, v, p, hl, hv, hp, ⟨u, hu⟩, ht⟩
    exact hdown s t (pinsTo_old hash hw hstep (back _ _ _ hl) hv hp ht hu)
  | create a ar oid o ha ho hwf hpins _ =>
    have hnone : lookup w a oid = none := by simp [lookup, ha, ho]
    refine ⟨fun s => if s.1 = a ∧ s.2.1 = oid then N else rank s, N + 1, ?_, ?_⟩
    · rintro ⟨b, x, n⟩ ⟨o1, v, hl, hv⟩
      rw [lookup_setEntry ha] at hl
      dsimp only
      split
      · omega
      · rename_i hc
        rw [if_no hc] at hl
        exact Nat.lt_succ_of_lt (hlive _ ⟨o1, v, hl, hv⟩)
    · rintro ⟨b, x, n⟩ t ⟨o1, v, p, hl, hv, hp, ⟨u, hu⟩, ht⟩
      rw [lookup_setEntry ha] at hl
      have htold : ∀ (h : PinsTo hash w (b, x, n) t),
          ¬ (t.1 = a ∧ t.2.1 = oid) := by
        rintro h ⟨h1, h2⟩
        obtain ⟨_, _, q, _, _, _, ⟨u', hu'⟩, hq⟩ := h
        have := live_of_resolve hash hu'
        rw [← hq] at this
        obtain ⟨t1, t2, t3⟩ := t
        simp only at h1 h2
        subst h1 h2
        exact not_live_empty hnone _ this
      dsimp only
      split at hl
      · rename_i hc
        cases hl
        obtain ⟨u0, hu0⟩ := hpins v (versionAt_mem hv) p hp
        have hlt := live_of_resolve hash hu0
        rw [← ht] at hlt
        have htn : ¬ (t.1 = a ∧ t.2.1 = oid) := by
          rintro ⟨h1, h2⟩
          obtain ⟨t1, t2, t3⟩ := t
          simp only at h1 h2
          subst h1 h2
          exact not_live_empty hnone _ hlt
        rw [if_yes hc, if_no htn]
        exact hlive _ hlt
      · rename_i hc
        have hpt := pinsTo_old hash hw hstep hl hv hp ht hu
        rw [if_no hc, if_no (htold hpt)]
        exact hdown _ _ hpt
  | append a ar oid o x ha ho hf _ hk _ hpins _ =>
    have hlo : lookup w a oid = some (.live o) := by simp [lookup, ha, ho]
    let new : Site := (a, oid, o.versions.length + 1)
    have hnew : ∀ t, Live w t → t ≠ new := by
      rintro t h rfl
      exact not_live_next hlo h
    refine ⟨fun s => if s = new then N else rank s, N + 1, ?_, ?_⟩
    · rintro ⟨b, y, n⟩ ⟨o1, v, hl, hv⟩
      rw [lookup_setEntry ha] at hl
      dsimp only
      split
      · omega
      · rename_i hsn
        apply Nat.lt_succ_of_lt
        apply hlive
        split at hl
        · rename_i hc
          cases hl
          rcases versionAt_append hv with hv | ⟨hn, _⟩
          · obtain ⟨h1, h2⟩ := hc
            subst h1 h2
            exact ⟨o, v, hlo, hv⟩
          · obtain ⟨h1, h2⟩ := hc
            subst h1 h2 hn
            exact absurd rfl hsn
        · exact ⟨o1, v, hl, hv⟩
    · rintro ⟨b, y, n⟩ t ⟨o1, v, p, hl, hv, hp, ⟨u, hu⟩, ht⟩
      rw [lookup_setEntry ha] at hl
      dsimp only
      split at hl
      · rename_i hc
        obtain ⟨h1, h2⟩ := hc
        subst h1 h2
        cases hl
        rcases versionAt_append hv with hv | ⟨hn, hvx⟩
        · have hpt := pinsTo_old hash hw hstep hlo hv hp ht hu
          have hsn : ((b, y, n) : Site) ≠ new := hnew _ ⟨o, v, hlo, hv⟩
          have htn : t ≠ new := by
            obtain ⟨_, _, q, _, _, _, ⟨u', hu'⟩, hq⟩ := hpt
            have := live_of_resolve hash hu'
            rw [← hq] at this
            exact hnew _ this
          rw [if_no hsn, if_no htn]
          exact hdown _ _ hpt
        · subst hvx
          obtain ⟨u0, hu0⟩ := hpins p hp
          have hlt := live_of_resolve hash hu0
          rw [← ht] at hlt
          have hsn : ((b, y, n) : Site) = new := by simp only at hn; simp [new, hn]
          rw [if_yes hsn, if_no (hnew _ hlt)]
          exact hlive _ hlt
      · rename_i hc
        have hpt := pinsTo_old hash hw hstep hl hv hp ht hu
        have hsn : ((b, y, n) : Site) ≠ new := by
          intro h
          simp only [new, Prod.mk.injEq] at h
          exact hc ⟨h.1, h.2.1⟩
        have htn : t ≠ new := by
          obtain ⟨_, _, q, _, _, _, ⟨u', hu'⟩, hq⟩ := hpt
          have := live_of_resolve hash hu'
          rw [← hq] at this
          exact hnew _ this
        rw [if_no hsn, if_no htn]
        exact hdown _ _ hpt

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
  induction hs with
  | refl =>
    refine ⟨⟨(WFWorld.empty hash).1, fun _ _ _ h => by simp [lookup] at h⟩,
      fun _ => 0, 0, ?_, ?_⟩
    · rintro s ⟨o, v, hl, _⟩; simp [lookup] at hl
    · rintro s t ⟨o, v, p, hl, _⟩; simp [lookup] at hl
  | tail _ he ih =>
    cases he with
    | step hs => exact ⟨hs.sound hash ih.1, hs.ranked hash ih.1 ih.2⟩
    | takedown a oid o hl => exact ⟨takedown_sound hash hl ih.1, takedown_ranked hash hl ih.2⟩

/-- **Pins cannot form cycles** (section 10.2), in any world built by events
(valid steps and takedowns), whatever the digest function. -/
theorem no_cycles_events {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) (s : Site) :
    ¬ Chain (PinsTo hash w) s s :=
  (hs.ranked hash).2.no_cycle hash s

theorem ValidSteps.toEvents {w w' : World D} (hs : ValidSteps hash w w') :
    Events hash w w' := by
  induction hs with
  | refl => exact .refl _
  | tail _ hstep ih => exact .tail ih (.step hstep)

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
  | newArchive b ar hb _ =>
    refine ⟨o, ?_, hst⟩
    by_cases hab : a = b
    · subst hab; simp [lookup, hb] at hl
    · simpa [lookup, hab] using hl
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
    {a : ArchiveId} {oid : ObjectId} (h : HeadWithdrawn w a oid) : HeadWithdrawn w' a oid := by
  induction hs with
  | refl => exact h
  | tail _ hstep ih => exact hstep.withdrawn_stays hash ih

end OpenSheaf
