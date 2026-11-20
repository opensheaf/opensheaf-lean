-- Generated from literate-sheaf/57-acyclic.md by opensheaf-literate: edit the document, not this file.
import Sheaf.Collections

namespace OpenSheaf.Sheaf

variable {D : Type} [DecidableEq D] (E : Env D)

omit [DecidableEq D] in
theorem deposit_antisymm {x y : Name} (h1 : deposit.le y x) (h2 : deposit.le x y) : x = y := by
  obtain ⟨o1, d1, _⟩ := h1
  obtain ⟨_, d2, _⟩ := h2
  cases x; cases y
  simp only at o1 d1 d2
  subst o1
  congr; omega

theorem pinStep_lower {w : World D} (hw : SoundWorld E w) {y x : Name}
    (h : PinStep E w y x) : HeldIn w y := by
  obtain ⟨_, _, _, _, p, b', o, u, _, _, _, _, _, _, ho, hko, hr, rfl⟩ := h
  unfold resolveAt at hr
  rw [ho] at hr
  exact heldIn_of_live E hw ho hko (versionAt_mem (resolveEntry_live_ok E.hash hr).1)

/-- A rank of named document versions in which deposit does not go down and
pins go down. -/
def NameRanked (w : World D) : Prop :=
  ∃ (r : Name → Nat) (N : Nat), (∀ x, HeldIn w x → r x < N) ∧
    (∀ y x, deposit.le y x → HeldIn w x → r y ≤ r x) ∧
    (∀ y x, PinStep E w y x → r y < r x)

theorem NameRanked.chain {w : World D} (hw : SoundWorld E w) {r : Name → Nat}
    (h1 : ∀ y x, deposit.le y x → HeldIn w x → r y ≤ r x)
    (h2 : ∀ y x, PinStep E w y x → r y < r x) {y x : Name}
    (h : (byPins E w).le y x) (hx : HeldIn w x) : deposit.le y x ∨ r y < r x := by
  induction h with
  | refl => exact Or.inl (deposit.refl _)
  | tail _ hb ih =>
    rename_i m x' _
    have hm : HeldIn w m := heldIn_open_byPins E hw (Star.tail (Star.refl _) hb) hx
    rcases hb with hd | hp
    · rcases ih hm with hd' | hlt
      · exact Or.inl (deposit.trans hd' hd)
      · exact Or.inr (Nat.lt_of_lt_of_le hlt (h1 _ _ hd hx))
    · have := h2 _ _ hp
      rcases ih hm with hd' | hlt
      · exact Or.inr (Nat.lt_of_le_of_lt (h1 _ _ hd' hm) this)
      · exact Or.inr (Nat.lt_trans hlt this)

theorem unheld_chain {w : World D} (hw : SoundWorld E w) {x y : Name}
    (h : (byPins E w).le x y) (hx : ¬ HeldIn w x) : deposit.le x y := by
  induction h with
  | refl => exact deposit.refl _
  | tail _ hb ih =>
    rcases hb with hd | hp
    · exact deposit.trans ih hd
    · exact absurd (heldIn_open w ih (pinStep_lower E hw hp)) hx

theorem NameRanked.antisymm {w : World D} (hw : SoundWorld E w) (hr : NameRanked E w)
    {x y : Name} (h1 : (byPins E w).le y x) (h2 : (byPins E w).le x y) : x = y := by
  obtain ⟨r, _, _, hdep, hpin⟩ := hr
  by_cases hx : HeldIn w x
  · have hy : HeldIn w y := heldIn_open_byPins E hw h1 hx
    rcases NameRanked.chain E hw hdep hpin h1 hx with d1 | l1 <;>
      rcases NameRanked.chain E hw hdep hpin h2 hy with d2 | l2
    · exact deposit_antisymm d1 d2
    · exact absurd (hdep _ _ d1 hx) (Nat.not_le_of_lt l2)
    · exact absurd (hdep _ _ d2 hy) (Nat.not_le_of_lt l1)
    · exact absurd (Nat.lt_trans l1 l2) (Nat.lt_irrefl _)
  · have d2 := unheld_chain E hw h2 hx
    have hy : ¬ HeldIn w y := fun hy => hx (heldIn_open w d2 hy)
    exact deposit_antisymm (unheld_chain E hw h1 hy) d2

/-- **Steps keep the edges.** -/
theorem Step.pinStep {w w' : World D} (hs : Step w w') {y x : Name}
    (h : PinStep E w y x) : PinStep E w' y x := by
  obtain ⟨b, l, c, v, p, b', o, u, hl, hk, hv, rfl, hp, hb', ho, hko, hr, rfl⟩ := h
  obtain ⟨c', hl', hg⟩ := hs.live_grows hl
  obtain ⟨o', ho', hg'⟩ := hs.live_grows ho
  obtain ⟨t, ht⟩ := hg.versions
  refine ⟨b, l, c', v, p, b', o', u, hl', by rw [hg.kind]; exact hk,
    by rw [ht]; exact List.mem_append_left _ hv, ?_, hp, hb', ho', by rw [hg'.kind]; exact hko,
    Step.resolveAt_ok E.hash hs hr, ?_⟩
  · simp only [Obj.name, hg.id]
  · simp only [Obj.name, hg'.id]

theorem Step.le {w w' : World D} (hs : Step w w') {y x : Name}
    (h : (byPins E w).le y x) : (byPins E w').le y x :=
  Star.mono (fun hb => hb.elim Or.inl (fun hp => Or.inr (Step.pinStep E hs hp))) h

theorem Steps.le {w w' : World D} (hs : Steps w w') {y x : Name}
    (h : (byPins E w).le y x) : (byPins E w').le y x :=
  hs.invariant (fun w => (byPins E w).le y x) (fun hs h => Step.le E hs h) h

/-- A takedown adds no edge. -/
theorem takedown_pinStep {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl0 : lookup w a oid = some (.live o)) {y x : Name}
    (h : PinStep E (takedown E.hash w a oid o) y x) : PinStep E w y x := by
  obtain ⟨b, l, c, v, p, b', o', u, hl, hk, hv, rfl, hp, hb', ho, hko, hr, rfl⟩ := h
  have hl1 := (lookup_takedown E.hash hl0 hl).2
  obtain ⟨hne, ho1⟩ := lookup_takedown E.hash hl0 ho
  refine ⟨b, l, c, v, p, b', o', u, hl1, hk, hv, rfl, hp, hb', ho1, hko, ?_, rfl⟩
  rw [← takedown_other E.hash hl0 hne]; exact hr

/-- A version whose named document version was not held before a valid step
was made by it, so its pins were checked. -/
theorem ValidStep.new_held {w w' : World D} (hs : ValidStep E w w') (hw : SoundWorld E w)
    {b : ArchiveId} {l : LineId} {c : Obj D} (hl : lookup w' b (.line l) = some (.live c))
    (hk : c.kind ≠ .owner) {v : Version D} (hv : v ∈ c.versions)
    (hnew : ¬ HeldIn w (c.name v)) {p : Pin D} (hp : p ∈ v.pins) : PinOk E w p := by
  obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.mp hv
  have hva : c.versionAt (k + 1) = some c.versions[k] := by
    rw [Obj.versionAt_succ, List.getElem?_eq_getElem hk']
  rcases hs.old_or_checked E hl hva with ⟨o, ho, hvo⟩ | h
  · obtain ⟨c', hl', hg⟩ := (hs.toStep E).live_grows ho
    rw [hl] at hl'; cases hl'
    have hko : o.kind ≠ .owner := by rw [← hg.kind]; exact hk
    have he : o.name c.versions[k] = c.name c.versions[k] := by simp only [Obj.name, hg.id]
    exact absurd (he ▸ heldIn_of_live E hw ho hko (versionAt_mem hvo)) hnew
  · exact h p hp

theorem same_members {w : World D} (hw : SoundWorld E w) (hca : ∀ l, CopiesAgree w l)
    {b b' : ArchiveId} {l l' : LineId} {c c' : Obj D}
    (hl : lookup w b (.line l) = some (.live c)) (hk : c.kind ≠ .owner)
    (hl' : lookup w b' (.line l') = some (.live c')) (hk' : c'.kind ≠ .owner)
    {v v' : Version D} (hv : v ∈ c.versions) (hv' : v' ∈ c'.versions)
    (hn : c.name v = c'.name v') : v.members = v'.members :=
  ((sameContent_iff).mp
    (holds_agree E hw hca ⟨_, _, c, hl, hk, hv, rfl⟩ ⟨_, _, c', hl', hk', hv', hn.symm⟩)).2

/-- A pin found before a step names, after it, the version and the named
document version it named before, when copies agree after the step. -/
theorem Step.found_same {w w' : World D} (hstep : Step w w')
    (hw0 : Events E (fun _ => (none : Option (Archive D))) w) (hw' : SoundWorld E w')
    (hca' : ∀ l, CopiesAgree w' l) {p : Pin D} (hpk : p.line ≠ keyLogLine p.line.owner)
    {b1 : ArchiveId} {u1 : Version D} (hu1 : resolveAt E.hash w b1 p = .ok u1) {b' : ArchiveId}
    {o : Obj D} {u : Version D} (ho : lookup w' b' (.line p.line) = some (.live o))
    (hko : o.kind ≠ .owner) (hres : resolveAt E.hash w' b' p = .ok u) :
    ∃ o1, lookup w b1 (.line p.line) = some (.live o1) ∧ o1.kind ≠ .owner ∧ u1 = u ∧
      o.name u = o1.name u := by
  have hu1' := hu1
  unfold resolveAt at hu1'
  obtain ⟨o1, ho1⟩ := resolveEntry_ok_live E.hash hu1'
  have hko1 : o1.kind ≠ .owner := Events.not_owner E hw0 hpk o1 ho1
  obtain ⟨o1', ho1', hg1⟩ := hstep.live_grows ho1
  have huu : u1 = u := agree_resolveAt E (hca' p.line) rfl
    (fun c c' hc hc' => by
      rw [ho1'] at hc; rw [ho] at hc'; cases hc; cases hc'
      exact ⟨by rw [hg1.kind]; exact hko1, hko⟩)
    (Step.resolveAt_ok E.hash hstep hu1) hres
  have hid : o.id = o1.id := by
    rw [(hw'.1 _ _ _ ho).id, ← hg1.id, (hw'.1 _ _ _ ho1').id]
  exact ⟨o1, ho1, hko1, huu, by simp only [Obj.name, hid]⟩

/-- **Old points keep their old edges.** -/
theorem Step.pinStep_back {w w' : World D} (hstep : Step w w') (hw0 : Events E
      (fun _ => (none : Option (Archive D))) w) (hw : WFWorld E w) (hnk : PinsNoKeyLog w)
    (hw' : SoundWorld E w') (hca' : ∀ l, CopiesAgree w' l) {y x : Name} (hx : HeldIn w x)
    (h : PinStep E w' y x) : PinStep E w y x := by
  obtain ⟨b, l, c, v, p, b', o, u, hl, hk, hv, rfl, hpm, hb', ho, hko, hres, rfl⟩ := h
  obtain ⟨⟨b0, l0, c0, hl0, hk0, n⟩, hx0⟩ := hx
  obtain ⟨v0, hv0, hn0⟩ := (covers_iff ((hw.1 _ _ _ hl0).history hk0) n _).mp hx0
  have hv0' : v0 ∈ c0.versions := List.mem_of_mem_take hv0
  obtain ⟨c0', hl0', hg0⟩ := hstep.live_grows hl0
  obtain ⟨t0, ht0⟩ := hg0.versions
  have hmem : v0 ∈ c0'.versions := by rw [ht0]; exact List.mem_append_left _ hv0'
  have hmembers := same_members E hw' hca' hl hk hl0' (by rw [hg0.kind]; exact hk0) hv hmem
    (by rw [hn0]; simp only [Obj.name, hg0.id])
  have hpm0 : p ∈ v0.memberPins := by
    unfold Version.memberPins at hpm ⊢; rw [← hmembers]; exact hpm
  have hpk := hnk _ _ _ hl0 v0 hv0' p (memberPins_sub hpm0)
  obtain ⟨b1, hb1, u1, hu1⟩ := hw.2.1 _ _ _ hl0 v0 hv0' p (memberPins_sub hpm0)
  obtain ⟨o1, ho1, hko1, huu, hname⟩ := Step.found_same E hstep hw0 hw' hca' hpk hu1 ho hko hres
  subst huu
  rw [hname, show c.name v = c0.name v0 from hn0]
  exact ⟨b0, l0, c0, v0, p, b1, o1, u1, hl0, hk0, hv0', rfl, hpm0, hb1, ho1, hko1, hu1, rfl⟩

/-- **Valid steps keep a rank**, when copies agree after the step. -/
theorem ValidStep.nameRanked {w w' : World D} (hs : ValidStep E w w')
    (hw0 : Events E (fun _ => (none : Option (Archive D))) w) (hw : WFWorld E w)
    (hnk : PinsNoKeyLog w) (hw' : SoundWorld E w') (hca' : ∀ l, CopiesAgree w' l)
    (hr : NameRanked E w) : NameRanked E w' := by
  classical
  obtain ⟨r, N, hN, hdep, hpin⟩ := hr
  have hstep := hs.toStep E
  have hsw : SoundWorld E w := ⟨hw.1, fun a i c h v hv p hp => Or.inl (hw.2.1 a i c h v hv p hp)⟩
  refine ⟨fun x => if HeldIn w x then r x else N, N + 1, fun x _ => ?_, ?_, ?_⟩
  · dsimp only; split
    · exact Nat.lt_succ_of_lt (hN _ ‹_›)
    · exact Nat.lt_succ_self _
  · intro y x hd hx
    dsimp only
    by_cases hxw : HeldIn w x
    · simp only [hxw, heldIn_open w hd hxw, ↓reduceIte]; exact hdep _ _ hd hxw
    · simp only [hxw, ↓reduceIte]; split
      · exact Nat.le_of_lt (hN _ ‹_›)
      · exact Nat.le_refl _
  · intro y x hp
    obtain ⟨b, l, c, v, p, b', o, u, hl, hk, hv, rfl, hpm, hb', ho, hko, hres, rfl⟩ := hp
    by_cases hxw : HeldIn w (c.name v)
    · -- an old named document version: its edges are old edges
      have hedge := Step.pinStep_back E hstep hw0 hw hnk hw' hca' hxw
        ⟨b, l, c, v, p, b', o, u, hl, hk, hv, rfl, hpm, hb', ho, hko, hres, rfl⟩
      have hyw : HeldIn w (o.name u) := pinStep_lower E hsw hedge
      dsimp only
      simp only [hyw, hxw, ↓reduceIte]
      exact hpin _ _ hedge
    · -- a new named document version: its pins were checked by the step
      have hok := ValidStep.new_held E hs hsw hl hk hv hxw (memberPins_sub hpm)
      obtain ⟨b1, _, u1, hu1⟩ := hw.pinOk_found E hok
      obtain ⟨o1, ho1, hko1, huu, hname⟩ :=
        Step.found_same E hstep hw0 hw' hca' hok.1 hu1 ho hko hres
      subst huu
      have hyw : HeldIn w (o1.name u1) := by
        unfold resolveAt at hu1
        rw [ho1] at hu1
        exact heldIn_of_live E hsw ho1 hko1 (versionAt_mem (resolveEntry_live_ok E.hash hu1).1)
      dsimp only
      simp only [hname, hyw, hxw, ↓reduceIte]
      exact hN _ hyw

/-- **Every world built by valid steps, with honest owners, has a rank.** -/
theorem ValidSteps.nameRanked {w : World D}
    (hs : ValidSteps E (fun _ => (none : Option (Archive D))) w) {H : Histories D}
    (hh : Honest E H w) :
    WFWorld E w ∧ PinsNoKeyLog w ∧ NameRanked E w := by
  induction hs with
  | refl =>
    exact ⟨WFWorld.empty E, fun _ _ _ h => by simp [lookup] at h,
      fun _ => 0, 0, fun _ ⟨⟨_, _, _, h, _, _⟩, _⟩ => by simp [lookup] at h,
      fun _ _ _ ⟨⟨_, _, _, h, _, _⟩, _⟩ => by simp [lookup] at h,
      fun _ _ ⟨_, _, _, _, _, _, _, _, h, _⟩ => by simp [lookup] at h⟩
  | tail hprev hstep ih =>
    have ih := ih (hh.back E (.tail (.refl _) (hstep.toStep E)))
    have hev : Events E (fun _ => (none : Option (Archive D))) _ := hprev.mono .step
    have hev' : Events E (fun _ => (none : Option (Archive D))) _ := (hprev.tail hstep).mono .step
    exact ⟨hstep.wf E ih.1, ValidStep.pinsNoKeyLog E hstep ih.2.1,
      ValidStep.nameRanked E hstep hev ih.1 ih.2.1 (Events.sound E hev')
        (fun l => Events.copiesAgree E hev' (hh.one E l)) ih.2.2⟩

/-- **The order with pins is a partial order** in every world built by valid
steps, when every owner signs one history. -/
theorem byPins_antisymm {w : World D}
    (hs : ValidSteps E (fun _ => (none : Option (Archive D))) w) {H : Histories D}
    (hh : Honest E H w) {x y : Name}
    (h1 : (byPins E w).le y x) (h2 : (byPins E w).le x y) : x = y :=
  NameRanked.antisymm E (Events.sound E (hs.mono .step)) (ValidSteps.nameRanked E hs hh).2.2 h1 h2

end OpenSheaf.Sheaf
