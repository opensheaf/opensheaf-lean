-- Generated from literate/65-impossible.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Patterns

namespace OpenSheaf

variable {D : Type} [DecidableEq D] (E : Env D)

/-- **A pin cannot change its meaning** at an archive. -/
theorem pin_meaning_fixed {w w' : World D} (hs : Steps w w') {b : ArchiveId} {p : Pin D}
    {v u : Version D} (hp : resolveAt E.hash w b p = .ok v) (hne : u ≠ v) :
    resolveAt E.hash w' b p ≠ .ok u := by
  rw [Steps.resolveAt_ok E.hash hs hp]
  intro h
  cases h
  exact hne rfl

/-- **A pin cannot change its meaning** through its hints, when its owner signs
one history. -/
theorem pin_meaning_fixed_hints {w w' : World D}
    (hw' : Events E (fun _ => (none : Option (Archive D))) w') (hs : Steps w w') {p : Pin D}
    (h1 : OneHistory E w' p.line) (hnk : p.line ≠ keyLogLine p.line.owner) {v u : Version D}
    (hp : resolve E.hash w p = .ok v) (hne : u ≠ v) : resolve E.hash w' p ≠ .ok u := by
  rw [Steps.resolve_ok E hw' hs h1 hnk hp]
  intro h
  cases h
  exact hne rfl

omit [DecidableEq D] in
/-- **History cannot be rewritten by any steps.** -/
theorem history_not_rewritten {w w' : World D} (hs : Steps w w') {a : ArchiveId}
    {oid : ObjectId} {o o' : Obj D} (hl : lookup w a oid = some (.live o))
    (hl' : lookup w' a oid = some (.live o'))
    (hrew : o'.versions.take o.versions.length ≠ o.versions) : False := by
  obtain ⟨o2, h2, hg⟩ := Steps.live_grows hs hl
  obtain ⟨t, ht⟩ := hg.versions
  rw [hl'] at h2
  cases h2
  apply hrew
  rw [ht, List.take_append_of_le_length (Nat.le_refl _), List.take_length]

/-- **Tampering is detected.** If an archive replaces a copy by one whose
history differs up to version `p.version`, a pin of that version made before
resolves there to no version at all. -/
theorem tamper_detected {w : World D}
    {a : ArchiveId} {o o' : Obj D} {p : Pin D} (hl : lookup w a (.line p.line) = some (.live o))
    {v : Version D} (hp : resolveAt E.hash w a p = .ok v)
    (hdiff : o'.inventory p.version ≠ o.inventory p.version)
    (hcol : NoCollision E (o'.inventory p.version) (o.inventory p.version))
    (u : Version D) : resolveAt E.hash (setEntry w a (.line p.line) (.live o')) a p ≠ .ok u := by
  obtain ⟨ar, ha⟩ := lookup_some_archive hl
  intro h
  unfold resolveAt at h hp
  rw [lookup_setEntry ha] at h
  simp only [and_self, ite_true] at h
  rw [hl] at hp
  obtain ⟨_, hd⟩ := resolveEntry_live_ok E.hash hp
  obtain ⟨_, hd'⟩ := resolveEntry_live_ok E.hash h
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

/-- **Consecutive document versions differ.** -/
theorem next_number_new_content {l : List (Version D)} (h : WellFormed l)
    {v u : Version D} (hv : v ∈ l) (hu : u ∈ l)
    (hn : u.documentVersion = v.documentVersion + 1) : sameContent v u = false := by
  induction l using snoc_induction generalizing v u with
  | nil => cases hv
  | snoc l x ih =>
    obtain ⟨hwf, hx⟩ := h.init
    simp only [List.mem_append, List.mem_singleton] at hv hu
    rcases hv with hv | hv <;> rcases hu with hu | hu
    · exact ih hwf hv hu hn
    · rw [hu] at hn ⊢
      rcases hx with ⟨z, hz, hzx, hxz⟩ | ⟨hnew, hxn⟩
      · cases hc : sameContent v x
        · rfl
        · have h1 := ih hwf hv hz (by omega)
          rw [sameContent_trans hc (sameContent_symm hzx)] at h1
          cases h1
      · exact hnew v hv (by omega)
    · rw [hv] at hn ⊢
      rcases hx with ⟨z, hz, hzx, hxz⟩ | ⟨_, hxn⟩
      · cases hc : sameContent x u
        · rfl
        · have h1 := ih hwf hz hu (by omega)
          rw [sameContent_trans hzx hc] at h1
          cases h1
      · have := le_docCount hu; omega
    · rw [hv, hu] at hn; omega

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

/-- A version of the line `l` at number `n` exists, in some archive. -/
def Live (w : World D) (s : LineId × Nat) : Prop :=
  ∃ b o v, lookup w b (.line s.1) = some (.live o) ∧ o.versionAt s.2 = some v

/-- A version at the site `s`, kept somewhere, holds a pin of the site `t`; the
line of `s` is not a key log. -/
def PinsTo (w : World D) (s t : LineId × Nat) : Prop :=
  s.1 ≠ keyLogLine s.1.owner ∧ ∃ b o v p, lookup w b (.line s.1) = some (.live o) ∧
    o.versionAt s.2 = some v ∧ p ∈ v.pins ∧ t = (p.line, p.version)

/-- A chain of one or more steps of a relation. -/
inductive Chain {α : Type} (r : α → α → Prop) : α → α → Prop
  | single {a b : α} : r a b → Chain r a b
  | cons {a b c : α} : r a b → Chain r b c → Chain r a c

theorem live_of_found {w : World D} {p : Pin D} (h : Found E.hash w p) :
    Live w (p.line, p.version) := by
  obtain ⟨b, _, u, hu⟩ := h
  unfold resolveAt at hu
  obtain ⟨c, hc⟩ := resolveEntry_ok_live E.hash hu
  rw [hc] at hu
  exact ⟨b, c, u, hc, (resolveEntry_live_ok E.hash hu).1⟩

/-- A numbering of the sites in which pins go down. -/
def Ranked (w : World D) : Prop :=
  ∃ (rank : LineId × Nat → Nat) (N : Nat), (∀ s, Live w s → rank s < N) ∧
    ∀ s t, PinsTo w s t → rank t < rank s

omit [DecidableEq D] in
theorem Ranked.chain_lt {w : World D} {rank : LineId × Nat → Nat}
    (hr : ∀ s t, PinsTo w s t → rank t < rank s) {s t : LineId × Nat}
    (h : Chain (PinsTo w) s t) : rank t < rank s := by
  induction h with
  | single h => exact hr _ _ h
  | cons h _ ih => exact Nat.lt_trans ih (hr _ _ h)

omit [DecidableEq D] in
theorem Ranked.no_cycle {w : World D} (hr : Ranked w) (s : LineId × Nat) :
    ¬ Chain (PinsTo w) s s := by
  obtain ⟨rank, _, _, hdown⟩ := hr
  intro h
  exact Nat.lt_irrefl _ (Ranked.chain_lt hdown h)

/-- After a valid step, a version is one the copy had, at the same number, or
its pins were checked by the step. -/
theorem ValidStep.old_or_checked {w w' : World D} (hs : ValidStep E w w')
    {b : ArchiveId} {x : ObjectId} {n : Nat} {o' : Obj D} {v : Version D}
    (hl' : lookup w' b x = some (.live o')) (hv : o'.versionAt n = some v) :
    (∃ o, lookup w b x = some (.live o) ∧ o.versionAt n = some v) ∨
      ∀ p ∈ v.pins, PinOk E w p := by
  rcases hs.live_cases E hl' with hl0 | ⟨_, _, _, ⟨_, hpins⟩ | ⟨o, y, ss, hlo, rfl, hpins⟩⟩ |
      ⟨o, ss, hlo, rfl, _⟩
  · exact Or.inl ⟨o', hl0, hv⟩
  · exact Or.inr fun p hp => hpins v (versionAt_mem hv) p hp
  · rcases versionAt_append hv with hv | ⟨_, rfl⟩
    · exact Or.inl ⟨o, hlo, hv⟩
    · exact Or.inr hpins
  · exact Or.inl ⟨o, hlo, hv⟩

theorem WFWorld.pinOk_found {w : World D} (hw : WFWorld E w) {p : Pin D}
    (h : PinOk E w p) : Found E.hash w p := by
  rcases h.2 with hf | ⟨⟨b, _, hr⟩, _⟩
  · exact hf
  · obtain ⟨n, d, hl⟩ := (resolveAt_removed_iff E.hash).mp hr
    exact absurd hl (hw.2.2 _ _ _ _)

theorem ValidStep.ranked {w w' : World D} (hs : ValidStep E w w') (hw : WFWorld E w)
    (hw' : Events E (fun _ => (none : Option (Archive D))) w')
    (hh : ∀ l, l ≠ keyLogLine l.owner → OneHistory E w' l) (hr : Ranked w) : Ranked w' := by
  classical
  obtain ⟨rank, N, hlive, hdown⟩ := hr
  have hstep := hs.toStep E
  refine ⟨fun s => if Live w s then rank s else N, N + 1, fun s _ => ?_, ?_⟩
  · dsimp only; split
    · exact Nat.lt_succ_of_lt (hlive s ‹_›)
    · exact Nat.lt_succ_self N
  · rintro ⟨l, n⟩ t ⟨hnk, b, o', v, p, hl', hv, hp, ht⟩
    dsimp only
    have htl : ∀ q ∈ v.pins, PinOk E w q → Live w (q.line, q.version) :=
      fun q _ hq => live_of_found E (hw.pinOk_found E hq)
    rcases hs.old_or_checked E hl' hv with ⟨o, hl, hvo⟩ | hchk
    · -- an old version, in its copy: its pin went down already
      have hpt : PinsTo w (l, n) t := ⟨hnk, b, o, v, p, hl, hvo, hp, ht⟩
      have hold : Live w (l, n) := ⟨b, o, v, hl, hvo⟩
      have htl' : Live w t := by
        rw [ht]
        exact live_of_found E (hw.2.1 _ _ _ hl v (versionAt_mem hvo) p hp)
      rw [if_yes htl', if_yes hold]
      exact hdown _ _ hpt
    · have htl' : Live w t := by rw [ht]; exact htl p hp (hchk p hp)
      by_cases hold : Live w (l, n)
      · -- a new version at an old site: the site's version elsewhere
        obtain ⟨b0, o0, v0, hl0, hv0⟩ := hold
        obtain ⟨o0', hl0', hg0⟩ := hstep.live_grows hl0
        obtain ⟨t0, ht0⟩ := hg0.versions
        have hv0' : o0'.versionAt n = some v0 :=
          versionAt_prefix (t := []) (by simp) ht0 (Obj.versionAt_bounds hv0).2 hv0
        have hk1 : o'.kind ≠ .owner := fun hk => hnk (Events.keyLog_line E hw' hl' hk)
        have hk0 : o0'.kind ≠ .owner := fun hk => hnk (Events.keyLog_line E hw' hl0' hk)
        have heq : v0 = v := (Events.copiesAgree E hw' (hh l hnk) b0 b o0' o' hl0' hl' hk0 hk1).versionAt
          hv0' hv
        subst heq
        have hpt : PinsTo w (l, n) t := ⟨hnk, b0, o0, v0, p, hl0, hv0, hp, ht⟩
        rw [if_yes htl', if_yes ⟨b0, o0, v0, hl0, hv0⟩]
        exact hdown _ _ hpt
      · rw [if_yes htl', if_no hold]
        exact hlive t htl'

theorem ValidSteps.ranked {w : World D}
    (hs : ValidSteps E (fun _ => (none : Option (Archive D))) w)
    (hh : ∀ l, l ≠ keyLogLine l.owner → OneHistory E w l) :
    WFWorld E w ∧ Ranked w := by
  induction hs with
  | refl => exact ⟨WFWorld.empty E, fun _ => 0, 0, by
      rintro s ⟨b, o, v, hl, _⟩; simp [lookup] at hl, by
      rintro s t ⟨_, b, o, v, p, hl, _⟩; simp [lookup] at hl⟩
  | tail hprev hstep ih =>
    have ih' := ih fun l hl => (hh l hl).back E (.tail (.refl _) (hstep.toStep E))
    exact ⟨hstep.wf E ih'.1, hstep.ranked E ih'.1
      ((Star.tail hprev hstep).mono .step) hh ih'.2⟩

/-- **Pins cannot form cycles** (section 8.5), in any world built by valid steps
in which every owner signs one history of each line that is not a key log,
which no copy held collides with. -/
theorem no_cycles {w : World D}
    (hs : ValidSteps E (fun _ => (none : Option (Archive D))) w)
    (hh : ∀ l, l ≠ keyLogLine l.owner → OneHistory E w l)
    (s : LineId × Nat) : ¬ Chain (PinsTo w) s s :=
  (hs.ranked E hh).2.no_cycle s

/-- No pin held by a version of a live object names a key log. -/
def PinsNoKeyLog (w : World D) : Prop :=
  ∀ b i c, lookup w b i = some (.live c) → ∀ v ∈ c.versions, ∀ p ∈ v.pins,
    p.line ≠ keyLogLine p.line.owner

theorem ValidStep.pinsNoKeyLog {w w' : World D} (hs : ValidStep E w w')
    (hw : PinsNoKeyLog w) : PinsNoKeyLog w' := by
  intro b i c hl v hv p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
  have hva : c.versionAt (k + 1) = some c.versions[k] := by
    rw [Obj.versionAt_succ, List.getElem?_eq_getElem hk]
  rcases hs.old_or_checked E hl hva with ⟨o, ho, hvo⟩ | h
  · exact hw _ _ _ ho _ (versionAt_mem hvo) p hp
  · exact (h p hp).1

/-- **No pin names a key log**, in every world built by events. -/
theorem Events.pinsNoKeyLog {w : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w) : PinsNoKeyLog w :=
  hs.invariant _ (fun he hw => by
      cases he with
      | step h => exact h.pinsNoKeyLog E hw
      | takedown a oid o _ hl =>
        exact fun b i c h => hw b i c (lookup_takedown E.hash hl h).2)
    (fun _ _ _ h => by simp [lookup] at h)

/-- In a world built by events, no copy of the line of a pin held is a key log. -/
theorem Events.pinned_not_owner {w : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w) {b : ArchiveId} {i : ObjectId}
    {c : Obj D} (hl : lookup w b i = some (.live c)) {v : Version D} (hv : v ∈ c.versions)
    {p : Pin D} (hp : p ∈ v.pins) {b' : ArchiveId} {o : Obj D}
    (ho : lookup w b' (.line p.line) = some (.live o)) : o.kind ≠ .owner :=
  fun hk => Events.pinsNoKeyLog E hs b i c hl v hv p hp (Events.keyLog_line E hs ho hk)

/-- The head of a live object is withdrawn. -/
def HeadWithdrawn (w : World D) (a : ArchiveId) (oid : ObjectId) : Prop :=
  ∃ o, lookup w a oid = some (.live o) ∧ headStatus o.versions = .withdrawn

/-- **A withdrawal stays until a new document version** reinstates the line. -/
theorem ValidStep.withdrawn_stays {w w' : World D} (hs : ValidStep E w w')
    {a : ArchiveId} {oid : ObjectId} (h : HeadWithdrawn w a oid) :
    HeadWithdrawn w' a oid ∨ ∃ o x ss, lookup w a oid = some (.live o) ∧
      lookup w' a oid = some (.live (o.append x ss)) ∧ docCount o.versions < x.documentVersion := by
  obtain ⟨o, hl, hst⟩ := h
  cases hs with
  | newArchive b ar hb hempty =>
    exact Or.inl ⟨o, by rw [lookup_newArchive hb hempty]; exact hl, hst⟩
  | create b ar c o' hb hc =>
    refine Or.inl ⟨o, ?_, hst⟩
    rw [lookup_setEntry hb]
    split
    · rename_i hbc
      obtain ⟨rfl, rfl⟩ := hbc
      simp [lookup, hb, hc] at hl
    · exact hl
  | append b ar c o' y ss hb hc _ hst' =>
    by_cases hbc : a = b ∧ oid = c
    · obtain ⟨rfl, rfl⟩ := hbc
      have hoo : some (Entry.live o') = some (Entry.live o) := by
        rw [← hl]; simp [lookup, hb, hc]
      have := Entry.live.inj (Option.some.inj hoo)
      subst this
      by_cases hy : y.documentVersion ≤ docCount o'.versions
      · refine Or.inl ⟨o'.append y ss, by rw [lookup_setEntry hb]; simp, ?_⟩
        simp [headStatus, Obj.append, hst'.2 hy hst]
      · exact Or.inr ⟨o', y, ss, hl, by rw [lookup_setEntry hb]; simp, by omega⟩
    · exact Or.inl ⟨o, by rw [lookup_setEntry hb, if_no hbc]; exact hl, hst⟩
  | witness b ar c o' ss hb hc =>
    by_cases hbc : a = b ∧ oid = c
    · obtain ⟨rfl, rfl⟩ := hbc
      have hoo : some (Entry.live o') = some (Entry.live o) := by
        rw [← hl]; simp [lookup, hb, hc]
      have := Entry.live.inj (Option.some.inj hoo)
      subst this
      exact Or.inl ⟨{ o' with sigs := o'.sigs ++ ss }, by rw [lookup_setEntry hb]; simp, hst⟩
    · exact Or.inl ⟨o, by rw [lookup_setEntry hb, if_no hbc]; exact hl, hst⟩

/-- Document version `k` of the history `l` is withdrawn: a version at or after
one holding it is a withdrawal (section 13.1). -/
def DocWithdrawn (l : List (Version D)) (k : Nat) : Prop :=
  ∃ j i, ∃ (hji : j ≤ i) (hi : i < l.length),
    (l[j]'(Nat.lt_of_le_of_lt hji hi)).documentVersion = k ∧ l[i].status = .withdrawn

omit [DecidableEq D] in
theorem DocWithdrawn.append {l : List (Version D)} {k : Nat} (h : DocWithdrawn l k)
    (t : List (Version D)) : DocWithdrawn (l ++ t) k := by
  obtain ⟨j, i, hji, hi, hk, hw⟩ := h
  refine ⟨j, i, hji, by simp; omega, ?_, ?_⟩
  · rw [List.getElem_append_left (Nat.lt_of_le_of_lt hji hi)]; exact hk
  · rw [List.getElem_append_left hi]; exact hw

/-- Document version `k` of the object `oid`, as archive `a` holds it, is withdrawn. -/
def DocWithdrawnAt (w : World D) (a : ArchiveId) (oid : ObjectId) (k : Nat) : Prop :=
  ∃ o, lookup w a oid = some (.live o) ∧ DocWithdrawn o.versions k

omit [DecidableEq D] in
/-- **A withdrawn document version stays withdrawn**, also when the line is
reinstated. -/
theorem Steps.docWithdrawn_stays {w w' : World D} (hs : Steps w w') {a : ArchiveId}
    {oid : ObjectId} {k : Nat} (h : DocWithdrawnAt w a oid k) : DocWithdrawnAt w' a oid k := by
  obtain ⟨o, hl, hd⟩ := h
  obtain ⟨o', hl', hg⟩ := hs.live_grows hl
  obtain ⟨t, ht⟩ := hg.versions
  exact ⟨o', hl', by rw [ht]; exact hd.append t⟩

end OpenSheaf
