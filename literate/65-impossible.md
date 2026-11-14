# What cannot happen

The previous chapters prove what the protocol does. This one proves what it
prevents: for each way of breaking it, an attempt is modelled and shown to
be impossible, or, where it can be made outside the protocol, to be
detected. These are the negative tests of the model.

| The break | Why it cannot happen |
|---|---|
| A pin changes its meaning | immutability: no step changes what a pin resolves to |
| An archive rewrites the history of an object | no sequence of steps can; outside the protocol, every pin of a rewritten version stops resolving (with a collision-free digest) |
| An identifier taken down names another object | tombstones stay |
| One document version number for two contents, or a gap in the numbering | the counting rule of section 7.3 |
| Pins form a cycle (a version pins itself, or two collections pin each other) | valid steps pin only versions that exist already |

The last one is stated in section 10.2 ("Pins cannot form cycles"), where
it is justified by the hashes. The model proves it from the protocol alone,
with no assumption on the digest function.

    -- in OpenSheaf/Impossible.lean:
    import OpenSheaf.Copies

    namespace OpenSheaf

    variable {D : Type} [DecidableEq D] (hash : Hash D)

## A pin cannot change its meaning

Immutability, stated as an impossibility: once a pin resolves to a version,
no sequence of steps makes it resolve to another.

    /-- **A pin cannot change its meaning.** -/
    theorem pin_meaning_fixed {w w' : World D} (hs : Steps w w') {p : Pin D} {v u : Version D}
        (hp : resolve hash w p = .ok v) (hne : u ≠ v) : resolve hash w' p ≠ .ok u := by
      rw [Steps.resolve_ok hash hs hp]
      intro h
      cases h
      exact hne rfl

## History cannot be rewritten

Within the protocol, an object only grows ([chapter 5](45-worlds.md)): its
history in a later world extends its history in an earlier one. A world in
which an archive has replaced, removed or reordered versions of an object
is therefore not reachable by any sequence of steps.

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

An archive can still rewrite its files outside the protocol: nothing stops
the owner of a disk. Then every pin of a rewritten version, made before,
stops resolving: the digest in the pin is that of the original inventory,
and, with a collision-free digest, no other inventory has it. Tampering is
not prevented, it is detected, by anyone holding a pin.

    /-- **Tampering is detected.** If an archive replaces an object by one whose
    history differs up to version `p.version`, a pin of that version made
    before resolves to no version at all. -/
    theorem tamper_detected (hinj : ∀ l l', hash l = hash l' → l = l') {w : World D}
        {a : ArchiveId} {oid : ObjectId} {o o' : Obj D} (hl : lookup w a oid = some (.live o))
        {p : Pin D} {v : Version D} (hpa : p.archive = a ∧ p.object = oid)
        (hp : resolve hash w p = .ok v) (hdiff : o'.inventory p.version ≠ o.inventory p.version)
        (u : Version D) : resolve hash (setEntry w a oid (.live o')) p ≠ .ok u := by
      obtain ⟨ar, ha⟩ := lookup_some_archive hl
      intro h
      unfold resolve at h hp
      rw [lookup_setEntry ha] at h
      simp only [hpa, and_self, ite_true] at h
      rw [hpa.1, hpa.2, hl] at hp
      obtain ⟨_, hd⟩ := resolveEntry_live_ok hash hp
      obtain ⟨_, hd'⟩ := resolveEntry_live_ok hash h
      exact hdiff (hinj _ _ (hd'.trans hd.symm))

## A tombstoned identifier cannot be reused

Section 11.3: "Identifiers of tombstoned objects MUST NOT be reused". In the
model it is not a rule that archives must remember: no step can do it.

    omit [DecidableEq D] in
    /-- **A tombstoned identifier is never reused.** -/
    theorem no_reuse {w w' : World D} (hs : Steps w w') {a : ArchiveId} {oid : ObjectId}
        {n : Nat} {d : D} (h : lookup w a oid = some (.tomb n d)) (o : Obj D) :
        lookup w' a oid ≠ some (.live o) := by
      rw [Steps.tomb_stays hs h]
      intro h'
      cases h'

## Document versions are unambiguous

Citations name document versions, so a number must mean one content, and
section 7.3 asks for numbers "from 1, without gaps". The counting rule of
[chapter 2](20-object.md) guarantees both. The proofs go along the history
from the end, so they need to take a well-formed history apart again.

    section Numbers

Lean's core library has no induction from the end of a list; it follows
from induction on the reversed list.

    omit [DecidableEq D] in
    theorem snoc_induction {α : Type} {motive : List α → Prop} (nil : motive [])
        (snoc : ∀ l x, motive l → motive (l ++ [x])) (l : List α) : motive l := by
      rw [← List.reverse_reverse l]
      induction l.reverse with
      | nil => exact nil
      | cons x r ih => rw [List.reverse_cons]; exact snoc _ _ ih

    theorem WellFormed.init {l : List (Version D)} {x : Version D}
        (h : WellFormed (l ++ [x])) : WellFormed l ∧ Follows l x := by
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

    theorem sameContent_iff {v u : Version D} :
        sameContent v u = true ↔ v.files = u.files ∧ v.members = u.members := by
      simp [sameContent]

One number, one content: two versions of a well-formed history with the
same document version have the same content. The last version either holds
earlier content, and takes its number, or new content, and a number above
all the others.

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
            exact ⟨hyz.1.trans hzx.1, hyz.2.trans hzx.2⟩
          · have := le_docCount hy; omega
        simp only [List.mem_append, List.mem_singleton] at hv hu
        rcases hv with hv | rfl <;> rcases hu with hu | rfl
        · exact ih hwf hv hu heq
        · exact key v hv heq
        · have := key u hu heq.symm
          rw [sameContent_iff] at this ⊢
          exact ⟨this.1.symm, this.2.symm⟩
        · exact sameContent_self _

No gaps: every number from 1 to the highest is held by some version.

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

## Pins cannot form cycles

A version is named by a **site**: an archive, an object, and an object
version number. A site *pins* another when the version there holds a pin
that resolves, and names the other.

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

A pin that resolves names a site where a version exists.

    theorem live_of_resolve {w : World D} {p : Pin D} {u : Version D}
        (h : resolve hash w p = .ok u) : Live w (p.archive, p.object, p.version) := by
      unfold resolve at h
      obtain ⟨c, hc⟩ := resolveEntry_ok_live hash h
      rw [hc] at h
      exact ⟨c, u, hc, (resolveEntry_live_ok hash h).1⟩

The idea of the proof: number the versions in the order in which they were
made. Every valid step pins only versions that exist before it, so a pin
always goes from a later version to an earlier one, and a chain of pins
cannot come back to where it started. `Ranked` says that such a numbering
exists: every existing version has a rank below `N`, and pins go down.

    /-- A numbering of the versions in which pins go down. -/
    def Ranked (w : World D) : Prop :=
      ∃ (rank : Site → Nat) (N : Nat), (∀ s, Live w s → rank s < N) ∧
        ∀ s t, PinsTo hash w s t → rank t < rank s

In a ranked world there is no cycle: along a chain of pins the rank goes
down, so it cannot come back.

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

Two facts about versions after an append: a version of the object is an
old one or the one appended, at the next number.

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

Two small helpers for `if`, whose library names this version of Lean
deprecates:

    omit [DecidableEq D] in
    theorem if_yes {α : Type} {c : Prop} [Decidable c] {x y : α} (h : c) :
        (if c then x else y) = x := by simp [h]

    omit [DecidableEq D] in
    theorem if_no {α : Type} {c : Prop} [Decidable c] {x y : α} (h : ¬ c) :
        (if c then x else y) = y := by simp [h]

A version found at a number is a version of the object, and an object has
no version after its last.

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

In a well-formed world, a version that exists holds only pins that
resolve; so a pin seen after a step, held by a version that existed before
it, already resolved before it.

    theorem pinsTo_old {w : World D} (hw : WFWorld hash w) {s t : Site} {o : Obj D}
        {v : Version D} {p : Pin D} (hl : lookup w s.1 s.2.1 = some (.live o))
        (hv : o.versionAt s.2.2 = some v) (hp : p ∈ v.pins)
        (ht : t = (p.archive, p.object, p.version)) : PinsTo hash w s t := by
      obtain ⟨u, hu⟩ := hw.2 _ _ _ hl v (versionAt_mem hv) p hp
      exact ⟨o, v, p, hl, hv, hp, ⟨u, hu⟩, ht⟩

The main lemma: a valid step keeps a numbering in which pins go down. The
new versions get the number `N`, above all the others; their pins resolved
before the step, so they name versions numbered below `N`. The pins of the
old versions are unchanged, by immutability.

    theorem ValidStep.ranked {w w' : World D} (hs : ValidStep hash w w') (hw : WFWorld hash w)
        (hr : Ranked hash w) : Ranked hash w' := by
      obtain ⟨rank, N, hlive, hdown⟩ := hr
      cases hs with
      | newArchive a ar ha hempty =>
        have back : ∀ b x e, lookup (fun c => if c = a then some ar else w c) b x = some e →
            lookup w b x = some e := by
          intro b x e h
          by_cases hb : b = a
          · subst hb; simp [lookup, hempty] at h
          · simpa [lookup, hb] using h
        refine ⟨rank, N, fun s ⟨o, v, hl, hv⟩ => hlive s ⟨o, v, back _ _ _ hl, hv⟩, ?_⟩
        rintro s t ⟨o, v, p, hl, hv, hp, _, ht⟩
        exact hdown s t (pinsTo_old hash hw (back _ _ _ hl) hv hp ht)
      | create a ar oid o ha ho hwf hpins =>
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
            have hpt := pinsTo_old hash hw hl hv hp ht
            rw [if_no hc, if_no (htold hpt)]
            exact hdown _ _ hpt
      | append a ar oid o x ha ho hf hk hpins =>
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
            · have hpt := pinsTo_old hash hw hlo hv hp ht
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
            have hpt := pinsTo_old hash hw hl hv hp ht
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

The empty world is ranked, trivially, and so, by induction, is every world
built from it by valid steps.

    theorem ValidSteps.ranked {w : World D}
        (hs : ValidSteps hash (fun _ => (none : Option (Archive D))) w) :
        WFWorld hash w ∧ Ranked hash w := by
      induction hs with
      | refl =>
        refine ⟨WFWorld.empty hash, fun _ => 0, 0, ?_, ?_⟩
        · rintro s ⟨o, v, hl, _⟩; simp [lookup] at hl
        · rintro s t ⟨o, v, p, hl, _⟩; simp [lookup] at hl
      | tail _ hstep ih => exact ⟨hstep.wf hash ih.1, hstep.ranked hash ih.1 ih.2⟩

    /-- **Pins cannot form cycles** (section 10.2), in any world built by valid
    steps, whatever the digest function. -/
    theorem no_cycles {w : World D}
        (hs : ValidSteps hash (fun _ => (none : Option (Archive D))) w) (s : Site) :
        ¬ Chain (PinsTo hash w) s s :=
      (hs.ranked hash).2.no_cycle hash s

In particular a version cannot pin itself, and two collections cannot pin
each other: both would be cycles. Section 10.2 attributes this to the
hashes (a pin names a digest, which cannot be known before the version
exists). The model shows that the protocol is enough: a valid step pins
only what already exists. The hashes make it hold also for copies that come
from outside the protocol.

    end OpenSheaf
