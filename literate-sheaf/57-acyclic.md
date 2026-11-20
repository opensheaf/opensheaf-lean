# The order with pins

The previous chapter added the pins of member lists to the order, and left
two questions open. This chapter answers them:

- **later steps keep its edges**: an edge of a world is an edge of every
  world that follows by steps (`Steps.le`), and a takedown adds no edge
  (`takedown_pinStep`); this holds of every world;
- **the order with pins is a partial order**: two named document versions
  each below the other are equal (`byPins_antisymm`), in every world built
  from nothing by valid steps, when every owner signs one history.

The second needs an argument, because the order mixes two kinds of edge on
named document versions. The argument numbers the named document versions
in the order in which they first appear in the world, and shows that
deposit never goes down in that numbering, and a pin always goes down.

Version 0.1 of this program proved the second for every world built by
events, takedowns included. Two things of version 0.2 break that proof, as
they break the model's own proof that pins form no cycles (its chapter
"What cannot happen"):

- a line may be copied, or deposited by its owner, in an archive after a
  pin of it was written: an edge from an old named document version may
  then be found through a new copy, and the numbering must know that the
  new copy holds the version the pin named. It does when the copies of a
  line agree, that is, when the owner signs one history;
- a line whose every copy was taken down may come back (section 13.2, and
  an owner moving its lines, section 6.5): its named document versions,
  held nowhere for a while, are held again. A numbering of what a world
  holds forgets them in between, and the argument would need the history
  of the world, not only its state.

So the chapter proves the partial order for worlds built by valid steps,
with honest owners, and leaves the case with takedowns open.

    -- in Sheaf/Acyclic.lean:
    import Sheaf.Collections

    namespace OpenSheaf.Sheaf

    variable {D : Type} [DecidableEq D] (E : Env D)

The order of deposit alone is antisymmetric: two names each below the
other are the same line at the same number.

    omit [DecidableEq D] in
    theorem deposit_antisymm {x y : Name} (h1 : deposit.le y x) (h2 : deposit.le x y) : x = y := by
      obtain ⟨o1, d1, _⟩ := h1
      obtain ⟨_, d2, _⟩ := h2
      cases x; cases y
      simp only at o1 d1 d2
      subst o1
      congr; omega

## What a world holds

The lower end of a pin edge is held: it is where the pin resolves, in a
live copy that is not a key log.

    theorem pinStep_lower {w : World D} (hw : SoundWorld E w) {y x : Name}
        (h : PinStep E w y x) : HeldIn w y := by
      obtain ⟨_, _, _, _, p, b', o, u, _, _, _, _, _, _, ho, hko, hr, rfl⟩ := h
      unfold resolveAt at hr
      rw [ho] at hr
      exact heldIn_of_live E hw ho hko (versionAt_mem (resolveEntry_live_ok E.hash hr).1)

## A rank

A *rank* numbers the named document versions. Along the order of deposit
it does not go down, below a held point; along a pin edge it goes down
strictly; and the held points have ranks below a bound `N`, so that a new
point can be ranked above all of them.

    /-- A rank of named document versions in which deposit does not go down and
    pins go down. -/
    def NameRanked (w : World D) : Prop :=
      ∃ (r : Name → Nat) (N : Nat), (∀ x, HeldIn w x → r x < N) ∧
        (∀ y x, deposit.le y x → HeldIn w x → r y ≤ r x) ∧
        (∀ y x, PinStep E w y x → r y < r x)

Given a rank, a chain down from a held point either stays in the order of
deposit or goes down in rank. Each step of the chain stays among held
points, since what a world holds is open (chapter
[Collections and what they pin](55-collections.md)).

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

From a point that is not held, only the order of deposit leads up: a pin
edge starts from a held point, and a point above an unheld one in the order
of deposit is not held either.

    theorem unheld_chain {w : World D} (hw : SoundWorld E w) {x y : Name}
        (h : (byPins E w).le x y) (hx : ¬ HeldIn w x) : deposit.le x y := by
      induction h with
      | refl => exact deposit.refl _
      | tail _ hb ih =>
        rcases hb with hd | hp
        · exact deposit.trans ih hd
        · exact absurd (heldIn_open w ih (pinStep_lower E hw hp)) hx

So a ranked world has a partial order. Between held points, two chains
in opposite directions cannot both go down in rank, so both stay in the
order of deposit, which is antisymmetric. A point that is not held reaches
only points of the order of deposit above it, which are not held either.

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

## Steps keep the edges

A step keeps every live copy, with the same identifier and kind and a
longer history, and keeps where every pin that resolves at an archive
resolves (`Step.live_grows` and `Step.resolveAt_ok`, the immutability of
the model). So it keeps every pin edge, and with it the whole order. This
holds for any step of the model, valid or not.

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

A takedown only turns a live entry into a tombstone. The copies and the
resolutions that remain are those of the world before it, so it adds no
edge. Which edges it removes depends on the copies that remain: a copy
kept elsewhere keeps the edges out of its versions.

    /-- A takedown adds no edge. -/
    theorem takedown_pinStep {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl0 : lookup w a oid = some (.live o)) {y x : Name}
        (h : PinStep E (takedown E.hash w a oid o) y x) : PinStep E w y x := by
      obtain ⟨b, l, c, v, p, b', o', u, hl, hk, hv, rfl, hp, hb', ho, hko, hr, rfl⟩ := h
      have hl1 := (lookup_takedown E.hash hl0 hl).2
      obtain ⟨hne, ho1⟩ := lookup_takedown E.hash hl0 ho
      refine ⟨b, l, c, v, p, b', o', u, hl1, hk, hv, rfl, hp, hb', ho1, hko, ?_, rfl⟩
      rw [← takedown_other E.hash hl0 hne]; exact hr

## Worlds built by valid steps

Three facts about a world built by valid steps, which the rank needs.
Every pin held is found (no tombstone, `WFWorld`, in the model). No pin
held names a key log: valid steps check it of every pin they write
(`PinOk`), and the model keeps it as an invariant (`PinsNoKeyLog`,
`ValidStep.pinsNoKeyLog`, in the chapter "What cannot happen" of the
model). And a copy of a line no pin names is not a key log.

A version whose named document version was not held before a valid step
was made by it, so the step checked its pins.

    /-- A version whose named document version was not held before a valid step
    was made by it, so its pins were checked. -/
    theorem ValidStep.new_held {w w' : World D} (hs : ValidStep E w w') (hw : SoundWorld E w)
        {b : ArchiveId} {l : LineId} {c : Obj D} (hl : lookup w' b (.line l) = some (.live c))
        (hk : c.kind ≠ .owner) {v : Version D} (hv : v ∈ c.versions)
        (hnew : ¬ HeldIn w (c.name v)) {p : Pin D} (hp : p ∈ v.pins) : PinOk E w p := by
      obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.mp hv
      have hva : c.versionAt (k + 1) = some c.versions[k] := by
        simp [Obj.versionAt, List.getElem?_eq_getElem hk']
      rcases hs.old_or_checked E hl hva with ⟨o, ho, hvo⟩ | h
      · obtain ⟨c', hl', hg⟩ := (hs.toStep E).live_grows ho
        rw [hl] at hl'; cases hl'
        have hko : o.kind ≠ .owner := by rw [← hg.kind]; exact hk
        have he : o.name c.versions[k] = c.name c.versions[k] := by simp only [Obj.name, hg.id]
        exact absurd (he ▸ heldIn_of_live E hw ho hko (versionAt_mem hvo)) hnew
      · exact h p hp

Two versions that hold the same named document version have the same
member list, since they have the same content (`holds_agree`). So an edge
out of a named document version does not depend on the version it is read
from.

    theorem same_members {w : World D} (hw : SoundWorld E w) (hca : ∀ l, CopiesAgree w l)
        {b b' : ArchiveId} {l l' : LineId} {c c' : Obj D}
        (hl : lookup w b (.line l) = some (.live c)) (hk : c.kind ≠ .owner)
        (hl' : lookup w b' (.line l') = some (.live c')) (hk' : c'.kind ≠ .owner)
        {v v' : Version D} (hv : v ∈ c.versions) (hv' : v' ∈ c'.versions)
        (hn : c.name v = c'.name v') : v.members = v'.members :=
      ((sameContent_iff).mp
        (holds_agree E hw hca ⟨_, _, c, hl, hk, hv, rfl⟩ ⟨_, _, c', hl', hk', hv', hn.symm⟩)).2

An edge into a named document version held before a valid step was an edge
before it: the version holding it has the member list of a version held
before, whose pins were found before the step; and where the pin is found
after the step, through whichever copy, it is the same version, since the
copies of its line agree.

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
      subst huu
      have hid : o.id = o1.id := by
        rw [(hw'.1 _ _ _ ho).id, ← hg1.id, (hw'.1 _ _ _ ho1').id]
      have hname : o.name u1 = o1.name u1 := by simp only [Obj.name, hid]
      rw [hname, show c.name v = c0.name v0 from hn0]
      exact ⟨b0, l0, c0, v0, p, b1, o1, u1, hl0, hk0, hv0', rfl, hpm0, hb1, ho1, hko1, hu1, rfl⟩

The main lemma. The named document versions held before the step keep
their rank; the new ones get the rank `N`, above all of them. An edge out
of an old point is an old edge, and goes down. An edge out of a new point
comes from pins the step checked, found before the step: it goes down to
an old point, ranked below `N`.

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
          have hu1' := hu1
          unfold resolveAt at hu1'
          obtain ⟨o1, ho1⟩ := resolveEntry_ok_live E.hash hu1'
          have hko1 : o1.kind ≠ .owner := Events.not_owner E hw0 hok.1 o1 ho1
          obtain ⟨o1', ho1', hg1⟩ := hstep.live_grows ho1
          have huu : u1 = u := agree_resolveAt E (hca' p.line) rfl
            (fun c c' hc hc' => by
              rw [ho1'] at hc; rw [ho] at hc'; cases hc; cases hc'
              exact ⟨by rw [hg1.kind]; exact hko1, hko⟩)
            (Step.resolveAt_ok E.hash hstep hu1) hres
          subst huu
          have hid : o.id = o1.id := by
            rw [(hw'.1 _ _ _ ho).id, ← hg1.id, (hw'.1 _ _ _ ho1').id]
          have hname : o.name u1 = o1.name u1 := by simp only [Obj.name, hid]
          rw [ho1] at hu1'
          have hyw : HeldIn w (o1.name u1) :=
            heldIn_of_live E hsw ho1 hko1 (versionAt_mem (resolveEntry_live_ok E.hash hu1').1)
          dsimp only
          simp only [hname, hyw, hxw, ↓reduceIte]
          exact hN _ hyw

## The theorem

The empty world has a rank, and every valid step keeps one, together with
the invariants it needs. So every world built by valid steps, with honest
owners, has a rank, and its order with pins is a partial order.

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
