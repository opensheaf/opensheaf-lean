# The order with pins

The previous chapter added the pins of member lists to the order, and left
two questions open. This chapter answers both, for every world built from
nothing by the events of the model:

- **the order with pins is a partial order**: two named document versions
  each below the other are equal (`byPins_antisymm`);
- **later steps keep its edges**: an edge of a world is an edge of every
  world that follows by steps (`Steps.le`), and a takedown adds no edge
  (`takedown_pinStep`).

The second is immutability again. The first needs an argument, because the
order mixes two kinds of edge on named document versions, while the model's
theorem that pins form no cycles (`no_cycles_events`) is about object
versions. The argument numbers the named document versions in the order in
which they first appear in the world, and shows that deposit never goes
down in that numbering, and a pin always goes down.

    -- in Sheaf/Acyclic.lean:
    import Sheaf.Collections

    namespace OpenSheaf.Sheaf

    variable {D : Type} [DecidableEq D] (hash : Hash D)

The order of deposit alone is antisymmetric: two names each below the
other are the same object at the same number.

    theorem deposit_antisymm {x y : Name} (h1 : deposit.le y x) (h2 : deposit.le x y) : x = y := by
      obtain ⟨a1, o1, d1, _⟩ := h1
      obtain ⟨_, _, d2, _⟩ := h2
      cases x; cases y
      simp only at a1 o1 d1 d2
      subst a1; subst o1
      congr; omega

## What a world holds

Two facts about what a world holds: every version of a live copy holds a
named document version of the world, and the lower end of a pin edge is
held (it is where the pin resolves).

    theorem heldIn_of_live {w : World D} (hw : SoundWorld hash w) {b : ArchiveId} {i : ObjectId}
        {c : Obj D} (hl : lookup w b i = some (.live c)) {v : Version D} (hv : v ∈ c.versions) :
        HeldIn w (c.name v) :=
      ⟨⟨b, i, c, hl, c.versions.length⟩,
        (held_iff (hw.1 _ _ _ hl).history _ _).mpr ⟨v, by rw [List.take_length]; exact hv, rfl⟩⟩

    theorem pinStep_lower {w : World D} (hw : SoundWorld hash w) {y x : Name}
        (h : PinStep hash w y x) : HeldIn w y := by
      obtain ⟨_, _, _, _, p, o, u, _, _, _, _, ho, hr, rfl⟩ := h
      have hre : resolveEntry hash (some (.live o)) p = .ok u := by
        unfold resolve at hr; rw [ho] at hr; exact hr
      exact heldIn_of_live hash hw ho (versionAt_mem (resolveEntry_live_ok hash hre).1)

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
        (∀ y x, PinStep hash w y x → r y < r x)

Given a rank, a chain down from a held point either stays in the order of
deposit or goes down in rank. Each step of the chain stays among held
points, since what a world holds is open (chapter
[Collections and what they pin](55-collections.md)).

    theorem NameRanked.chain {w : World D} (hw : SoundWorld hash w) {r : Name → Nat}
        (h1 : ∀ y x, deposit.le y x → HeldIn w x → r y ≤ r x)
        (h2 : ∀ y x, PinStep hash w y x → r y < r x) {y x : Name}
        (h : (byPins hash w).le y x) (hx : HeldIn w x) : deposit.le y x ∨ r y < r x := by
      induction h with
      | refl => exact Or.inl (deposit.refl _)
      | tail _ hb ih =>
        rename_i m x' _
        have hm : HeldIn w m := heldIn_open_byPins hash hw (Star.tail (Star.refl _) hb) hx
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

    theorem unheld_chain {w : World D} (hw : SoundWorld hash w) {x y : Name}
        (h : (byPins hash w).le x y) (hx : ¬ HeldIn w x) : deposit.le x y := by
      induction h with
      | refl => exact deposit.refl _
      | tail _ hb ih =>
        rcases hb with hd | hp
        · exact deposit.trans ih hd
        · exact absurd (heldIn_open w ih (pinStep_lower hash hw hp)) hx

So a ranked world has a partial order. Between held points, two chains
in opposite directions cannot both go down in rank, so both stay in the
order of deposit, which is antisymmetric. A point that is not held reaches
only points of the order of deposit above it, which are not held either.

    theorem NameRanked.antisymm {w : World D} (hw : SoundWorld hash w) (hr : NameRanked hash w)
        {x y : Name} (h1 : (byPins hash w).le y x) (h2 : (byPins hash w).le x y) : x = y := by
      obtain ⟨r, _, _, hdep, hpin⟩ := hr
      by_cases hx : HeldIn w x
      · have hy : HeldIn w y := heldIn_open_byPins hash hw h1 hx
        rcases NameRanked.chain hash hw hdep hpin h1 hx with d1 | l1 <;>
          rcases NameRanked.chain hash hw hdep hpin h2 hy with d2 | l2
        · exact deposit_antisymm d1 d2
        · exact absurd (hdep _ _ d1 hx) (Nat.not_le_of_lt l2)
        · exact absurd (hdep _ _ d2 hy) (Nat.not_le_of_lt l1)
        · exact absurd (Nat.lt_trans l1 l2) (Nat.lt_irrefl _)
      · have d2 := unheld_chain hash hw h2 hx
        have hy : ¬ HeldIn w y := fun hy => hx (heldIn_open w d2 hy)
        exact deposit_antisymm (unheld_chain hash hw h1 hy) d2

## Steps keep the edges

A step keeps every live copy, with the same name and a longer history, and
keeps where every pin that resolves resolves (`Step.resolve_ok`, the
immutability of the model). So it keeps every pin edge, and with it the
whole order. This holds for any step of the model, valid or not.

    omit [DecidableEq D] in
    theorem Step.live_kept {w w' : World D} (hs : Step w w') {b : ArchiveId} {i : ObjectId}
        {c : Obj D} (hl : lookup w b i = some (.live c)) :
        ∃ c', lookup w' b i = some (.live c') ∧ c'.archive = c.archive ∧ c'.id = c.id ∧
          ∃ t, c'.versions = c.versions ++ t := by
      rcases hs.lookup_cases b i with h | h | ⟨o, v, h1, h2⟩
      · exact ⟨c, by rw [h, hl], rfl, rfl, [], by simp⟩
      · rw [hl] at h; cases h
      · rw [hl] at h1; cases h1
        exact ⟨c.append v, h2, rfl, rfl, [v], rfl⟩

    /-- **Steps keep the edges.** -/
    theorem Step.pinStep {w w' : World D} (hs : Step w w') {y x : Name}
        (h : PinStep hash w y x) : PinStep hash w' y x := by
      obtain ⟨b, i, c, v, p, o, u, hl, hv, rfl, hp, ho, hr, rfl⟩ := h
      obtain ⟨c', hl', ha, hi, t, ht⟩ := Step.live_kept hs hl
      obtain ⟨o', ho', ha', hi', _, _⟩ := Step.live_kept hs ho
      refine ⟨b, i, c', v, p, o', u, hl', by rw [ht]; exact List.mem_append_left _ hv, ?_, hp, ho',
        Step.resolve_ok hash hs hr, ?_⟩
      · simp only [Obj.name, ha, hi]
      · simp only [Obj.name, ha', hi']

    theorem Step.le {w w' : World D} (hs : Step w w') {y x : Name}
        (h : (byPins hash w).le y x) : (byPins hash w').le y x :=
      Star.mono (fun hb => hb.elim Or.inl (fun hp => Or.inr (Step.pinStep hash hs hp))) h

    theorem Steps.le {w w' : World D} (hs : Steps w w') {y x : Name}
        (h : (byPins hash w).le y x) : (byPins hash w').le y x :=
      hs.invariant (fun w => (byPins hash w).le y x) (fun hs h => Step.le hash hs h) h

A takedown only turns a live entry into a tombstone. The copies and the
resolutions that remain are those of the world before it, so it adds no
edge; it removes the edges into the object taken down, and those from its
versions.

    /-- A takedown adds no edge. -/
    theorem takedown_pinStep {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl0 : lookup w a oid = some (.live o)) {y x : Name}
        (h : PinStep hash (takedown hash w a oid o) y x) : PinStep hash w y x := by
      obtain ⟨b, i, c, v, p, o', u, hl, hv, rfl, hp, ho, hr, rfl⟩ := h
      have hl1 := (lookup_takedown hash hl0 hl).2
      have ho1 := (lookup_takedown hash hl0 ho).2
      refine ⟨b, i, c, v, p, o', u, hl1, hv, rfl, hp, ho1, ?_, rfl⟩
      unfold resolve at hr ⊢
      rw [ho] at hr; rw [ho1]; exact hr

## Events keep a rank

A takedown keeps the rank as it is: it holds less, and adds no edge.

    omit [DecidableEq D] in
    theorem heldIn_takedown {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl0 : lookup w a oid = some (.live o)) {x : Name}
        (h : HeldIn (takedown hash w a oid o) x) : HeldIn w x := by
      obtain ⟨⟨b, i, c, hl, n⟩, hx⟩ := h
      exact ⟨⟨b, i, c, (lookup_takedown hash hl0 hl).2, n⟩, hx⟩

    theorem takedown_ranked {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        (hl0 : lookup w a oid = some (.live o)) (hr : NameRanked hash w) :
        NameRanked hash (takedown hash w a oid o) := by
      obtain ⟨r, N, hN, hdep, hpin⟩ := hr
      exact ⟨r, N, fun x hx => hN x (heldIn_takedown hash hl0 hx),
        fun y x hd hx => hdep y x hd (heldIn_takedown hash hl0 hx),
        fun y x hp => hpin y x (takedown_pinStep hash hl0 hp)⟩

A valid step needs three facts. A pin held before the step that resolves
after it resolved before it, to the same version (a pin that reported
`removed` still does).

    /-- A pin that holds before a step and resolves after it resolved before it,
    to the same version. -/
    theorem resolve_back {w w' : World D} (hs : Step w w') {p : Pin D} (hh : OpenSheaf.Held hash w p)
        {u : Version D} (hu : resolve hash w' p = .ok u) : resolve hash w p = .ok u := by
      rcases hh with ⟨u', hu'⟩ | hrem
      · rw [Step.resolve_ok hash hs hu'] at hu; cases hu; exact hu'
      · rw [Step.resolve_removed hash hs hrem] at hu; cases hu

A named document version that was not held before the step was made by
it, so the step checked its pins: they resolved, or reported `removed`,
before the step (the premise `hpins` of the model's valid steps).

    /-- A version whose named document version was not held before a valid step
    was made by it, so its pins were checked. -/
    theorem ValidStep.new_held {w w' : World D} (hs : ValidStep hash w w') (hw : SoundWorld hash w)
        {b : ArchiveId} {i : ObjectId} {c : Obj D} (hl : lookup w' b i = some (.live c))
        {v : Version D} (hv : v ∈ c.versions) (hnew : ¬ HeldIn w (c.name v))
        {p : Pin D} (hp : p ∈ v.pins) : OpenSheaf.Held hash w p := by
      cases hs with
      | newArchive a ar ha hempty =>
        rw [lookup_newArchive ha hempty] at hl
        exact absurd (heldIn_of_live hash hw hl hv) hnew
      | create a ar oid o ha ho _ hpins _ =>
        rw [lookup_setEntry ha] at hl
        split at hl
        · cases hl; exact (hpins v hv p hp).held
        · exact absurd (heldIn_of_live hash hw hl hv) hnew
      | append a ar oid o y ha ho _ _ _ _ hpins _ =>
        rw [lookup_setEntry ha] at hl
        split at hl
        · cases hl
          have hlo : lookup w a oid = some (.live o) := by simp [lookup, ha, ho]
          simp only [Obj.append, List.mem_append, List.mem_singleton] at hv
          rcases hv with hv | rfl
          · exact absurd (heldIn_of_live hash hw hlo hv) hnew
          · exact (hpins p hp).held
        · exact absurd (heldIn_of_live hash hw hl hv) hnew

Two versions that hold the same named document version have the same
member list, since copies agree and a number has one content (the model's
`CopiesAgree` and `one_number_one_content`). So an edge out of a named
document version does not depend on the version it is read from.

    /-- Two versions holding the same named document version, in a world whose
    copies agree, have the same member list. -/
    theorem same_members {w : World D} (hw : SoundWorld hash w) (hca : CopiesAgree w)
        {b b' : ArchiveId} {i i' : ObjectId} {c c' : Obj D}
        (hl : lookup w b i = some (.live c)) (hl' : lookup w b' i' = some (.live c'))
        {v v' : Version D} (hv : v ∈ c.versions) (hv' : v' ∈ c'.versions)
        (hn : c.name v = c'.name v') : v.members = v'.members := by
      simp only [Obj.name, Name.mk.injEq] at hn
      obtain ⟨ha, hi, hd⟩ := hn
      rcases hca _ _ _ _ _ _ hl hl' ha hi with ⟨t, ht⟩ | ⟨t, ht⟩
      · have hwf := (hw.1 _ _ _ hl').history
        have := one_number_one_content hwf (by rw [ht]; exact List.mem_append_left _ hv) hv' hd
        exact ((sameContent_iff).mp this).2
      · have hwf := (hw.1 _ _ _ hl).history
        have := one_number_one_content hwf hv (by rw [ht]; exact List.mem_append_left _ hv') hd
        exact ((sameContent_iff).mp this).2

The main lemma. The named document versions held before the step keep
their rank; the new ones get the rank `N`, above all of them. An edge out
of an old point comes from pins the old point already had, which resolved
before the step to the same versions: it is an old edge, and goes down. An
edge out of a new point comes from pins the step checked, which resolved
before the step: it goes down to an old point, ranked below `N`.

    /-- **Valid steps keep a rank.** Named document versions held before the step
    keep their rank; the new ones get a rank above all others. -/
    theorem ValidStep.nameRanked {w w' : World D} (hs : ValidStep hash w w') (hw : SoundWorld hash w)
        (hw' : SoundWorld hash w') (hca' : CopiesAgree w') (hr : NameRanked hash w) :
        NameRanked hash w' := by
      classical
      obtain ⟨r, N, hN, hdep, hpin⟩ := hr
      have hstep := hs.toStep hash
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
        obtain ⟨b, i, c, v, p, o, u, hl, hv, rfl, hpm, ho, hres, rfl⟩ := hp
        by_cases hxw : HeldIn w (c.name v)
        · -- an old named document version: its pins resolved before the step
          obtain ⟨⟨b0, i0, c0, hl0, n⟩, hx0⟩ := hxw
          obtain ⟨v0, hv0, hn0⟩ := (held_iff (hw.1 _ _ _ hl0).history n _).mp hx0
          have hv0' : v0 ∈ c0.versions := List.mem_of_mem_take hv0
          obtain ⟨c0', hl0', ha0, hi0, t0, ht0⟩ := Step.live_kept hstep hl0
          have hmem : v0 ∈ c0'.versions := by rw [ht0]; exact List.mem_append_left _ hv0'
          have hmembers := same_members hash hw' hca' hl hl0' hv hmem
            (by rw [hn0]; simp only [Obj.name, ha0, hi0])
          have hpm0 : p ∈ v0.memberPins := by
            unfold Version.memberPins at hpm ⊢; rw [← hmembers]; exact hpm
          have hres0 := resolve_back hash hstep
            (hw.2 _ _ _ hl0 v0 hv0' p (memberPins_sub hpm0)) hres
          have hres0' := hres0
          unfold resolve at hres0'
          obtain ⟨o0, ho0⟩ := resolveEntry_ok_live hash hres0'
          obtain ⟨o0', ho0', hoa, hoi, _, _⟩ := Step.live_kept hstep ho0
          rw [ho] at ho0'; cases ho0'
          have hname : o.name u = o0.name u := by simp only [Obj.name, hoa, hoi]
          have hedge : PinStep hash w (o0.name u) (c0.name v0) :=
            ⟨b0, i0, c0, v0, p, o0, u, hl0, hv0', rfl, hpm0, ho0, hres0, rfl⟩
          have hyw : HeldIn w (o0.name u) := pinStep_lower hash hw hedge
          have hxw' : HeldIn w (c.name v) := ⟨⟨b0, i0, c0, hl0, n⟩, hx0⟩
          dsimp only
          simp only [hname, hyw, hxw', ↓reduceIte]
          have : c.name v = c0.name v0 := hn0
          rw [this]
          exact hpin _ _ hedge
        · -- a new named document version: its pins were checked by the step
          have hres0 := resolve_back hash hstep
            (ValidStep.new_held hash hs hw hl hv hxw (memberPins_sub hpm)) hres
          have hres0' := hres0
          unfold resolve at hres0'
          obtain ⟨o0, ho0⟩ := resolveEntry_ok_live hash hres0'
          obtain ⟨o0', ho0', hoa, hoi, _, _⟩ := Step.live_kept hstep ho0
          rw [ho] at ho0'; cases ho0'
          have hname : o.name u = o0.name u := by simp only [Obj.name, hoa, hoi]
          have hre : resolveEntry hash (some (.live o0)) p = .ok u := by
            unfold resolve at hres0; rw [ho0] at hres0; exact hres0
          have hyw : HeldIn w (o0.name u) :=
            heldIn_of_live hash hw ho0 (versionAt_mem (resolveEntry_live_ok hash hre).1)
          dsimp only
          simp only [hname, hyw, hxw, ↓reduceIte]
          exact hN _ hyw

## The theorem

The empty world has a rank, and every event keeps one, together with the
invariants of the model it needs (sound worlds, mirrors and agreeing
copies). So every world built by events has a rank, and its order with pins
is a partial order.

    /-- **Every world built by events has a rank.** -/
    theorem Events.nameRanked {w : World D}
        (hs : Events hash (fun _ => (none : Option (Archive D))) w) : NameRanked hash w := by
      have := hs.invariant
        (fun w => (SoundWorld hash w ∧ MirrorsOk w ∧ CopiesAgree w) ∧ NameRanked hash w)
        (fun he ⟨hk, hr⟩ => by
          have hk' := Event.copiesAgree hash he hk
          refine ⟨hk', ?_⟩
          cases he with
          | step hs => exact ValidStep.nameRanked hash hs hk.1 hk'.1 hk'.2.2 hr
          | takedown a oid o hl => exact takedown_ranked hash hl hr)
        ⟨⟨SoundWorld.empty hash, fun _ _ _ h => by simp [lookup] at h,
          fun _ _ _ _ _ _ h => by simp [lookup] at h⟩,
         fun _ => 0, 0, fun _ ⟨⟨_, _, _, h, _⟩, _⟩ => by simp [lookup] at h,
         fun _ _ _ ⟨⟨_, _, _, h, _⟩, _⟩ => by simp [lookup] at h,
         fun _ _ ⟨_, _, _, _, _, _, _, h, _⟩ => by simp [lookup] at h⟩
      exact this.2

    /-- **The order with pins is a partial order** in every world built by events. -/
    theorem byPins_antisymm {w : World D}
        (hs : Events hash (fun _ => (none : Option (Archive D))) w) {x y : Name}
        (h1 : (byPins hash w).le y x) (h2 : (byPins hash w).le x y) : x = y :=
      NameRanked.antisymm hash (Events.sound hash hs) (Events.nameRanked hash hs) h1 h2

    end OpenSheaf.Sheaf
