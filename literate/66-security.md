# What keys can do

Section 15.1 of the specification says, owner by owner and key by key,
what whoever holds a key can do, and what it cannot. "Whoever holds
`threshold` current keys of an owner signs versions of its lines as that
owner until the owner exposes them, after which what those keys alone sign
is contested, and archives aware of it never add it (sections 7.3 and
7.5), though readers still find its signatures good; it cannot change the
key log, which only rotation keys sign." The earlier chapters prove the
last clause (`current_keys_cannot_extend`, [chapter 4](35-owners.md)) and
that an archive aware of an exposure adds nothing signed with the exposed
keys alone (`exposed_keys_add_nothing`, [chapter 8](47-acts.md)). This
chapter proves the rest of what section 15.1 promises about keys, and
section 6.3 about exposures and forks:

- **an exposure cannot be blocked**: whether a new version of a key log is
  valid depends only on the signatures made with rotation keys of the
  version before; signature files made with any other key, current keys
  among them, neither help nor hinder it
  (`KeyLogOk.append_iff_rotation`, `current_keys_cannot_block`);
- **a fork freezes the owner for ever**: once an archive holds a fork
  record of an owner's key log, it holds one in every later world built by
  events, and no event ever adds a version, or a new copy, of the owner's
  other lines there (`Events.fork_freezes_forever`);
- **the keys of the other side never count**: an owner's key, in a world
  built by events, is a current key of a version that a copy of its key
  log holds, not of one a fork record carries (`OwnerKey.held`,
  `Events.unheld_keys_add_nothing`); and a reader who holds the fork record
  never finds a version signed and not contested by keys of a carried
  version (`KeyLogOk.clean_held`);
- **good signatures stay good, and contested stays contested**: against a
  longer copy of the key log, a version signed stays signed, and a version
  contested stays contested (`SignedWith.longer`, `Contested.longer`);
- **a takeover, and the owner's only answer**: rotation keys of the latest
  version, not revealed, extend the key log with keys of the thief's own,
  which then count as the owner's (`KeyLogOk.append_keyed`,
  `takeover_ownerKey`); the owner's old rotation keys can then never extend
  it (`takeover_locks_out`), and its only answer is a fork, which freezes
  it;
- **a retired key still signs**: a key retired but never exposed makes good,
  uncontested signatures naming the versions that list it
  (`retired_key_signs`).

[Chapter 15](72-risks.md) shows each residual risk of section 15.1 in the
story's worlds; [chapter 18](85-reader.md) proves what a reader's check of
one copy guarantees, whatever host served it.

    -- in OpenSheaf/Security.lean:
    import OpenSheaf.Impossible

    namespace OpenSheaf

    variable {D : Type} [DecidableEq D] (E : Env D)

## Only rotation keys count

"Only rotation keys sign that version, so whoever holds the current keys
can neither prevent nor contest it" (section 6.3, of the version that
exposes a key). Pre-rotation gives this: "current keys never sign a
version of the key log, and rotation keys sign nothing else" (section 6.1),
and a version of a key log is never contested ("Only versions of lines are
contested, never versions of key logs", section 7.3). What the model has to
show is that the count of rotation keys of the version before, the only
thing a later version needs of its signatures, does not move when
signature files of other keys are added or left out.

The count is by the digests that `next` commits to, and a signature file
whose key has no such digest is filtered out before it is counted: so two
lists of signature files that hold the same files made with keys whose
digests `next` commits to give the same count. The lemma says one
direction.

    /-- Only the signature files whose keys `next` of `pk` commits to count. -/
    theorem rotationSigners_length_rel {l : LineId} {n : Nat} {d : D} {kl : Pin D}
        {pk : Keys D} {sigs sigs' : List (Sig D)}
        (hsub : ∀ s ∈ sigs, E.keyDigest s.key ∈ pk.next → s ∈ sigs') :
        (rotationSigners E l n d kl pk sigs).length ≤
          (rotationSigners E l n d kl pk sigs').length := by
      unfold rotationSigners
      apply length_le_of_sub (distinct_nodup _)
      intro x hx
      rw [mem_distinct] at hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      obtain ⟨s, hs, rfl, h1, h2, h3⟩ := mem_signers E hk
      have h3' : E.keyDigest s.key ∈ pk.next := by simpa using h3
      refine List.mem_map.mpr ⟨s.key, ?_, rfl⟩
      unfold signers
      rw [mem_distinct]
      refine List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hsub s hs h3', ?_⟩, rfl⟩
      simp [h1, h2, h3']

A step of a key log reads the version before only through its keys:

    theorem KeyStep.prev_congr {X : OwnerName} {o : Obj D} {j : Nat} {prev prev' x : Version D}
        (hp : prev'.keys = prev.keys) (h : KeyStep E X o j prev x) : KeyStep E X o j prev' x := by
      unfold KeyStep at h ⊢; rw [hp]; exact h

A step stays valid in a copy with the same versions whose witness folder
holds the signature files of rotation keys of the version before that the
first holds; others may be missing. This sharpens `KeyStep.more_sigs`
([chapter 4](35-owners.md)), which asks for every signature file; a fork
record reads no witness folder at all, its carried versions holding their
own signature files.

    theorem KeyStep.of_rotation {X : OwnerName} {o o' : Obj D} (hid : o'.id = o.id)
        (hg : o'.genesis = o.genesis) (hv : o'.versions = o.versions) {j : Nat}
        {prev x : Version D}
        (hs : ∀ pk, prev.keys = some pk → ∀ s ∈ o.sigs, E.keyDigest s.key ∈ pk.next → s ∈ o'.sigs)
        (h : KeyStep E X o j prev x) : KeyStep E X o' j prev x := by
      have hinv : ∀ n, o'.inventory n = o.inventory n := fun n => by
        simp [Obj.inventory, hid, hg, hv]
      have hva : ∀ n, o'.versionAt n = o.versionAt n := fun n => by simp [Obj.versionAt, hv]
      cases hx : x.keys with
      | some k =>
        obtain ⟨pk, hp, h1, h2, ⟨h3, h4⟩, h5⟩ := h.keyed E hx
        refine KeyStep.of_keyed E hp hx ⟨h1, by rw [hv]; exact h2, ⟨h3, ?_⟩, h5⟩
        unfold keyPin; rw [hinv, hinv]
        exact Nat.le_trans h4 (rotationSigners_length_rel E (hs pk hp))
      | none =>
        obtain ⟨pk, hp, h1, h2⟩ := h.fork E hx
        refine KeyStep.of_fork E hp hx ⟨by rw [hv]; exact h1, ?_⟩
        unfold ForkRecordOk at h2 ⊢
        obtain ⟨h2a, h2b, h2c, h2d⟩ := h2
        refine ⟨h2a, h2b, h2c, ?_⟩
        cases hcs : x.carried with
        | nil => rw [hcs] at h2d; exact h2d.elim
        | cons c cs =>
          rw [hcs] at h2d
          unfold ForkCarried ForkBase keysAt at h2d ⊢
          simpa only [hinv, hva, hv, hg] using h2d

A version with keys reads only the versions up to it: it stays a valid
step in a longer copy, with at least the same signature files.

    omit [DecidableEq D] in
    theorem take_le_of_take {α : Type} {l l' : List α} {m n : Nat} (hn : n ≤ m)
        (h : l'.take m = l.take m) : l'.take n = l.take n := by
      rw [← Nat.min_eq_left hn, ← List.take_take, h, List.take_take]

    theorem KeyStep.prefix {X : OwnerName} {o o' : Obj D} (hid : o'.id = o.id)
        (hg : o'.genesis = o.genesis) {j : Nat}
        (ht : o'.versions.take (j + 1) = o.versions.take (j + 1))
        (hs : ∀ s ∈ o.sigs, s ∈ o'.sigs) {prev x : Version D} {k : Keys D}
        (hx : x.keys = some k) (h : KeyStep E X o j prev x) : KeyStep E X o' j prev x := by
      have hinv : ∀ n, n ≤ j + 1 → o'.inventory n = o.inventory n := fun n hn => by
        simp only [Obj.inventory, hid, hg, take_le_of_take hn ht]
      obtain ⟨pk, hp, h1, h2, ⟨h3, h4⟩, h5⟩ := h.keyed E hx
      refine KeyStep.of_keyed E hp hx ⟨h1, by rw [take_le_of_take (Nat.le_succ j) ht]; exact h2,
        ⟨h3, ?_⟩, h5⟩
      unfold keyPin; rw [hinv (j + 1) (Nat.le_refl _), hinv j (Nat.le_succ j)]
      exact Nat.le_trans h4 (rotationSigners_length_mono E hs)

Two facts about a valid key log: it has a version, and the keys of its
latest version, when it has keys, are those of its last element.

    theorem KeyLogOk.length_pos {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) :
        0 < o.versions.length := by
      obtain ⟨_, _, hp⟩ := h.parts
      have := hp.head
      cases hv : o.versions with
      | nil => rw [hv] at this; cases this
      | cons _ _ => simp

    omit [DecidableEq D] in
    theorem keysAt_last {o : Obj D} {pk : Keys D} (hpk : keysAt o o.versions.length = some pk)
        (hlen : 0 < o.versions.length) :
        (o.versions[o.versions.length - 1]'(by omega)).keys = some pk := by
      obtain ⟨m, hm⟩ : ∃ m, o.versions.length = m + 1 := ⟨o.versions.length - 1, by omega⟩
      simp only [keysAt, hm, Obj.versionAt_succ] at hpk
      rw [List.getElem?_eq_getElem (by omega)] at hpk
      simp only [hm, Nat.add_sub_cancel]
      simpa using hpk

A valid key log whose latest version has keys is extended validly by any
version that follows that latest version as a step: the steps before stay
valid, since they read only the versions up to them and the signature
files kept, which an append keeps. A latest version with keys is not a fork
record, so no fork record is left anywhere but last.

    /-- **A valid key log grows by one valid step.** -/
    theorem KeyLogOk.append_step {X : OwnerName} {o : Obj D} (ho : KeyLogOk E X o) {pk : Keys D}
        (hpk : keysAt o o.versions.length = some pk) {prev x : Version D} {ss : List (Sig D)}
        (hprev : prev.keys = some pk)
        (hlast : KeyStep E X (o.append x ss) o.versions.length prev x) :
        KeyLogOk E X (o.append x ss) := by
      obtain ⟨g, k1, hp⟩ := ho.parts
      have hlen := ho.length_pos E
      have hlastk := keysAt_last hpk hlen
      unfold KeyLogOk
      rw [show (o.append x ss).genesis = some g from hp.genesis]
      have hhead : (o.append x ss).versions.head? = some (firstKeyVersion g) := by
        have := hp.head
        simp only [Obj.append, List.head?_append, this, Option.some_or]
      refine ⟨hp.id, hp.kind, hp.gkind, hp.name, ?_, hhead, fun i hi => ?_⟩
      · rw [hp.keys]; exact ⟨hp.keysOk, hp.notEnded⟩
      · have hi' : i < o.versions.length := by simp [Obj.append] at hi; omega
        by_cases hlt : i + 1 < o.versions.length
        · have hs := hp.steps i (by omega)
          obtain ⟨k, hk⟩ : ∃ k, (o.versions[i + 1]'hlt).keys = some k := by
            cases hx : (o.versions[i + 1]'hlt).keys with
            | some k => exact ⟨k, rfl⟩
            | none =>
              have := ho.fork_last E hlt hx
              have him : i + 1 = o.versions.length - 1 := by omega
              simp only [him] at hx
              rw [hlastk] at hx; cases hx
          have ht : (o.append x ss).versions.take (i + 1 + 1) = o.versions.take (i + 1 + 1) := by
            simp [Obj.append, List.take_append_of_le_length (show i + 1 + 1 ≤ o.versions.length by omega)]
          have := KeyStep.prefix E (o := o) (o' := o.append x ss) rfl rfl ht
            (fun s hs => List.mem_append_left _ hs) hk hs
          rw [append_getElem_old (by omega), append_getElem_old hlt]
          exact this
        · have him : i + 1 = o.versions.length := by omega
          have hxi : ((o.append x ss).versions[i + 1]'(by simp [Obj.append]; omega)) = x := by
            simp [Obj.append, him]
          rw [hxi, append_getElem_old hi']
          have hk : (o.versions[i]'hi').keys = some pk := by
            have : i = o.versions.length - 1 := by omega
            subst this; exact hlastk
          rw [him]
          exact KeyStep.prev_congr E (hk.trans hprev.symm) hlast

And so the theorem. Two lists of new signature files, `ss` and `ss'`,
that hold the same files made with rotation keys of the latest version
`pk` make the new version valid alike, whatever else they hold.

    theorem KeyLogOk.append_of_rotation {X : OwnerName} {o : Obj D} (ho : KeyLogOk E X o)
        {pk : Keys D} (hpk : keysAt o o.versions.length = some pk) {x : Version D}
        {ss ss' : List (Sig D)} (hss : ∀ s ∈ ss, E.keyDigest s.key ∈ pk.next → s ∈ ss')
        (h : KeyLogOk E X (o.append x ss)) : KeyLogOk E X (o.append x ss') := by
      obtain ⟨_, _, hp⟩ := h.parts
      have hlen := ho.length_pos E
      have hlastk := keysAt_last hpk hlen
      have hs := hp.steps (o.versions.length - 1) (by simp [Obj.append]; omega)
      rw [append_getElem_old (by omega)] at hs
      simp only [Nat.sub_add_cancel hlen] at hs
      rw [append_getElem_last] at hs
      refine ho.append_step E hpk hlastk
        (KeyStep.of_rotation E (o := o.append x ss) (o' := o.append x ss') rfl rfl rfl ?_ hs)
      intro pk' hpk' s hs' hd
      rw [hlastk] at hpk'; cases hpk'
      rcases List.mem_append.mp hs' with h1 | h1
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (hss s h1 hd)

    /-- **Only rotation keys of the version before decide a new version of a key
    log.** -/
    theorem KeyLogOk.append_iff_rotation {X : OwnerName} {o : Obj D} (ho : KeyLogOk E X o)
        {pk : Keys D} (hpk : keysAt o o.versions.length = some pk) {x : Version D}
        {ss ss' : List (Sig D)} (hss : ∀ s, E.keyDigest s.key ∈ pk.next → (s ∈ ss ↔ s ∈ ss')) :
        KeyLogOk E X (o.append x ss) ↔ KeyLogOk E X (o.append x ss') :=
      ⟨ho.append_of_rotation E hpk fun s hs hd => (hss s hd).mp hs,
       ho.append_of_rotation E hpk fun s hs hd => (hss s hd).mpr hs⟩

The corollary for current keys. Signature files `cs` made with keys that
some version of the key log lists as current, whoever made them, are never
made with a rotation key of the latest version (`KeyLogOk.disjoint`), so
adding them to the new version changes nothing: whoever holds the current
keys cannot block the version that exposes them. Nor can it contest it,
since versions of a key log are never contested; and since key logs are
never taken down in the model, nor can it remove it, once held. This is
the formal content of "whoever holds the current keys can neither prevent
nor contest it" (section 6.3).

    /-- **An exposure cannot be blocked** by whoever holds current keys. -/
    theorem current_keys_cannot_block {X : OwnerName} {o : Obj D} (ho : KeyLogOk E X o)
        {pk : Keys D} (hpk : keysAt o o.versions.length = some pk) {x : Version D}
        {ss cs : List (Sig D)}
        (hcur : ∀ s ∈ cs, ∃ i, ∃ hi : i < o.versions.length, ∃ ki,
          (o.versions[i]'hi).keys = some ki ∧ s.key ∈ ki.keys) :
        KeyLogOk E X (o.append x (ss ++ cs)) ↔ KeyLogOk E X (o.append x ss) := by
      have hlen := ho.length_pos E
      have hlastk := keysAt_last hpk hlen
      refine ho.append_iff_rotation E hpk fun s hd =>
        ⟨fun hs => ?_, fun hs => List.mem_append_left _ hs⟩
      rcases List.mem_append.mp hs with h1 | h1
      · exact h1
      · obtain ⟨i, hi, ki, hki, hkey⟩ := hcur s h1
        exact absurd hd (ho.disjoint E hi (by omega) hki hlastk hkey)

## A fork freezes the owner for ever

"A fork ends the owner, at the fork point, and freezes it (section 7.5)"
(section 6.3), and "Once an archive knows of a fork of an owner's key log
(section 6.3), it adds no version of that owner's other lines, from a copy
or as a deposit, unless other evidence it trusts ... dates signature files
enough to make the version signed before any version of the key log at
the fork point was signed" (section 7.5). The model has no such evidence,
and `frozen_adds_nothing` ([chapter 8](47-acts.md)) refuses one step. Here
the refusal lasts: an archive "never replaces or removes" a version of a
key log it holds "but by a takedown" (section 6.3), which the model leaves
out for key logs, so the fork record stays, and with it the freeze.

A copy of a key log that has a fork record still has it when it grows:

    omit [DecidableEq D] in
    theorem Frozen.prefix {kl kl' : Obj D} (ht : ∃ t, kl'.versions = kl.versions ++ t)
        (h : Frozen kl) : Frozen kl' := by
      obtain ⟨t, ht⟩ := ht
      obtain ⟨v, hv, hk⟩ := h
      exact ⟨v, by rw [ht]; exact List.mem_append_left _ hv, hk⟩

and, when the longer copy is valid, it is the same copy: "No version of the
key log follows a valid fork record" (section 6.3), so a valid key log that
extends a copy with a fork record adds nothing to it (`KeyLogOk.fork_last`).

    theorem KeyLogOk.frozen_final {X : OwnerName} {kl kl' : Obj D} (h' : KeyLogOk E X kl')
        (ht : ∃ t, kl'.versions = kl.versions ++ t) (hf : Frozen kl) :
        kl'.versions = kl.versions := by
      obtain ⟨t, ht⟩ := ht
      obtain ⟨v, hv, hk⟩ := hf
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
      have hi' : i < kl'.versions.length := by rw [ht]; simp; omega
      have he : kl'.versions[i]'hi' = kl.versions[i] := by
        simp only [ht, List.getElem_append_left hi]
      have := h'.fork_last E hi' (by rw [he]; exact hk)
      rw [ht] at this ⊢
      simp at this
      have : t = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [this]

Events never take a key log down: a takedown is of a line that is not a
key log, and leaves every key log in place.

    omit [DecidableEq D] in
    theorem lookup_keyLog_takedown {w : World D} {a : ArchiveId} {l : LineId} {o : Obj D}
        (hk : l ≠ keyLogLine l.owner) (hl : lookup w a (.line l) = some (.live o)) (b : ArchiveId)
        (X : OwnerName) :
        lookup (takedown E.hash w a (.line l) o) b (.line (keyLogLine X)) =
          lookup w b (.line (keyLogLine X)) := by
      rw [lookup_takedown_eq E.hash hl, if_no]
      rintro ⟨_, he⟩
      apply hk
      rw [← ObjectId.line.inj he]; rfl

So a copy of a key log only grows, by events:

    theorem Event.keyLog_grows {w w' : World D} (he : Event E w w') {a : ArchiveId}
        {X : OwnerName} {kl : Obj D} (h : lookup w a (.line (keyLogLine X)) = some (.live kl)) :
        ∃ kl', lookup w' a (.line (keyLogLine X)) = some (.live kl') ∧ Grows kl kl' := by
      cases he with
      | step hs => exact (hs.toStep E).live_grows h
      | takedown b l o hk hl =>
        exact ⟨kl, by rw [lookup_keyLog_takedown E hk hl]; exact h, Grows.refl kl⟩

    theorem Events.keyLog_grows {w w' : World D} (hs : Events E w w') {a : ArchiveId}
        {X : OwnerName} {kl : Obj D} (h : lookup w a (.line (keyLogLine X)) = some (.live kl)) :
        ∃ kl', lookup w' a (.line (keyLogLine X)) = some (.live kl') ∧ Grows kl kl' := by
      refine hs.invariant (fun w => ∃ kl', lookup w a (.line (keyLogLine X)) = some (.live kl') ∧
        Grows kl kl') ?_ ⟨kl, h, Grows.refl kl⟩
      rintro _ _ he ⟨kl1, h1, hg1⟩
      obtain ⟨kl2, h2, hg2⟩ := he.keyLog_grows E h1
      exact ⟨kl2, h2, hg1.trans hg2⟩

An object of kind `owner` is the key log of its line's owner, by its
identity:

    theorem IdentityOk.owner_line {l : LineId} {o : Obj D} (h : IdentityOk E l o)
        (hk : o.kind = .owner) : l = keyLogLine l.owner := by
      unfold IdentityOk at h
      split at h
      · exact h.elim
      · rw [if_yes hk] at h; exact h.2.1

One event, at an archive whose copy of the key log of the owner of `l` has
a fork record: a valid step there adds no version and no copy of `l`
(which is not the key log), since it would need the owner's signature
against a copy that is not frozen; a witness adds signature files only;
and a takedown removes. Whatever copy of `l` the archive holds after has
the versions of the one it held before.

    theorem Event.frozen_line {w w' : World D} (he : Event E w w') {a : ArchiveId} {kl : Obj D}
        {l : LineId} (hkl : lookup w a (.line (keyLogLine l.owner)) = some (.live kl))
        (hf : Frozen kl) (hk : l ≠ keyLogLine l.owner) {o' : Obj D}
        (h' : lookup w' a (.line l) = some (.live o')) :
        ∃ o, lookup w a (.line l) = some (.live o) ∧ o'.versions = o.versions := by
      cases he with
      | step hs =>
        rcases hs.live_cases E h' with h0 | ⟨ar, _, ⟨hid, hline⟩, _⟩ | ⟨o, ss, ho, rfl, _⟩
        · exact ⟨o', h0, rfl⟩
        · by_cases hko : o'.kind = .owner
          · exact absurd (hid.owner_line E hko) hk
          · exact absurd (hline hko) (frozen_adds_nothing E hkl hf)
        · exact ⟨o, ho, rfl⟩
      | takedown b l2 o hk2 hl =>
        exact ⟨o', (lookup_takedown E.hash hl h').2, rfl⟩

The theorem, for any events after a world `w` in which archive `a` holds a
copy of the key log of `X` with a fork record: in every later world, `a`
holds a copy of that key log, grown from it and still with a fork record;
and every copy of a line of `X`, other than its key log, that `a` holds
then has exactly the versions of the copy `a` held in `w` (it may have
more signature files, or have been taken down, and then it is no copy).
No new copy appears, and none grows. The theorem needs nothing of how `w`
was built.

    /-- **A fork freezes the owner for ever**, at the archive that knows of it. -/
    theorem Events.fork_freezes_forever {w w' : World D} (hs : Events E w w') {a : ArchiveId}
        {X : OwnerName} {kl : Obj D} (hkl : lookup w a (.line (keyLogLine X)) = some (.live kl))
        (hf : Frozen kl) :
        (∃ kl', lookup w' a (.line (keyLogLine X)) = some (.live kl') ∧ Grows kl kl' ∧
          Frozen kl') ∧
        ∀ l, l.owner = X → l ≠ keyLogLine X → ∀ o', lookup w' a (.line l) = some (.live o') →
          ∃ o, lookup w a (.line l) = some (.live o) ∧ o'.versions = o.versions := by
      refine hs.invariant (fun w' =>
        (∃ kl', lookup w' a (.line (keyLogLine X)) = some (.live kl') ∧ Grows kl kl' ∧
          Frozen kl') ∧
        ∀ l, l.owner = X → l ≠ keyLogLine X → ∀ o', lookup w' a (.line l) = some (.live o') →
          ∃ o, lookup w a (.line l) = some (.live o) ∧ o'.versions = o.versions) ?_
        ⟨⟨kl, hkl, Grows.refl kl, hf⟩, fun l _ _ o' h' => ⟨o', h', rfl⟩⟩
      rintro w1 w2 he ⟨⟨kl1, h1, hg1, hf1⟩, hlines⟩
      obtain ⟨kl2, h2, hg2⟩ := he.keyLog_grows E h1
      refine ⟨⟨kl2, h2, hg1.trans hg2, hf1.prefix hg2.versions⟩, fun l hl hk o2 ho2 => ?_⟩
      subst hl
      obtain ⟨o1, ho1, hv1⟩ := he.frozen_line E h1 hf1 hk ho2
      obtain ⟨o, ho, hv⟩ := hlines l rfl hk o1 ho1
      exact ⟨o, ho, hv1.trans hv⟩

In a world built by events from nothing, every copy of a key log is valid
(`Events.keyLogsOk`), so the copy with the fork record does not even grow:
it is the same, version for version, for ever.

    /-- **A fork record stays, and nothing follows it.** -/
    theorem Events.fork_record_stays {w w' : World D}
        (h0 : Events E (fun _ => (none : Option (Archive D))) w) (hs : Events E w w')
        {a : ArchiveId} {X : OwnerName} {kl : Obj D}
        (hkl : lookup w a (.line (keyLogLine X)) = some (.live kl)) (hko : kl.kind = .owner)
        (hf : Frozen kl) :
        ∃ kl', lookup w' a (.line (keyLogLine X)) = some (.live kl') ∧
          kl'.versions = kl.versions := by
      obtain ⟨⟨kl', h', hg, _⟩, _⟩ := Events.fork_freezes_forever E hs hkl hf
      have hok : KeyLogOk E X kl' :=
        Events.keyLogsOk E (h0.trans hs) (l := keyLogLine X) h' (by rw [hg.kind]; exact hko)
      exact ⟨kl', h', hok.frozen_final E hg.versions hf⟩

## The keys of the other side never count

A fork record carries the versions of the other side, "each with its
`keys.json`" (section 6.3), and their keys are current keys of that side.
They never make a version of the owner's lines: "a thief that forks the
key log may thus expose the owner's earlier keys, which makes contested
what they signed (section 7.3), but never makes a version signed" (section
6.3).

In a world, the owner's keys (`OwnerKey`, [chapter 8](47-acts.md)) are
read in the versions a copy of the key log holds, never in those a fork
record carries: a key that some copy of the key log lists only in a
carried version, or nowhere, is no key of the owner.

    omit [DecidableEq D] in
    /-- **An owner's key is a current key of a version held.** -/
    theorem OwnerKey.held {w : World D} {X : OwnerName} {s : Sig D} (h : OwnerKey E w X s) :
        ∃ b kl, lookup w b (.line (keyLogLine X)) = some (.live kl) ∧
          ∃ v ∈ kl.versions, ∃ kv, v.keys = some kv ∧ kv.ended = false ∧ s.key ∈ kv.keys := by
      obtain ⟨_, b, kl, hkl, v, hv, _, kv, hkv, hend, hkey⟩ := h
      exact ⟨b, kl, hkl, v, versionAt_mem hv, kv, hkv, hend, hkey⟩

So, in a world built by events, keys `K` that no held version of any copy
of the owner's key log lists, keys of a carried version among them, add
nothing: if every signature of a line that verifies is made with one of
them, no archive holds a copy of the line.

    /-- **Keys that no version held lists add nothing**, those of the other side of
    a fork included. -/
    theorem Events.unheld_keys_add_nothing {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {l : LineId} {K : List Key}
        (hK : ∀ b kl, lookup w b (.line (keyLogLine l.owner)) = some (.live kl) →
          ∀ v ∈ kl.versions, ∀ kv, v.keys = some kv → ∀ key ∈ K, key ∉ kv.keys)
        (hsig : ∀ s, E.verifies s = true → s.line = l → s.key ∈ K) {b : ArchiveId} {o : Obj D}
        (hl : lookup w b (.line l) = some (.live o)) (hk : o.kind ≠ .owner) : False := by
      refine forgery_needs_owner_key E hs (fun s hv hsl hown => ?_) hl hk
      obtain ⟨b', kl, hkl, v, hv', kv, hkv, _, hkey⟩ := hown.held E
      exact hK b' kl hkl v hv' kv hkv s.key (hsig s hv hsl) hkey

A reader is not bound by the steps: it judges a signature against the
key-log version it names, "also as carried by a fork record" (section
7.3), so against a copy with a fork record a version signed with keys of
the other side may be signed. It is then contested, never signed and not
contested: every version a fork record carries is at or after the fork
point, and a signature naming one is tainted. The proof needs three facts
of a valid key log: a version with keys carries nothing; the versions a
fork record carries are numbered upwards from the fork point; and only the
last version, the fork record, carries any, so the fork point is the number
of its first.

    theorem KeyLogOk.carried_keyed {X : OwnerName} {kl : Obj D} (h : KeyLogOk E X kl) {i : Nat}
        (hi : i < kl.versions.length) {k : Keys D} (hk : (kl.versions[i]'hi).keys = some k) :
        (kl.versions[i]'hi).carried = [] := by
      obtain ⟨g, _, hp⟩ := h.parts
      cases i with
      | zero => rw [hp.getElem_zero E hi]; rfl
      | succ i =>
        obtain ⟨_, _, hc, _⟩ := (hp.steps i (by omega)).keyed E hk
        exact hc

    theorem carriedChain_gt {X : OwnerName} {gen : Option (Genesis D)} (cs : List (Carried D)) :
        ∀ {prevs : List (Keys D)} {base : List (Version D)} {n : Nat} {d : D} {pk : Keys D},
          carriedChain E X gen prevs base n d pk cs = true → ∀ c ∈ cs, n < c.version := by
      induction cs with
      | nil => intro _ _ _ _ _ _ c hc; cases hc
      | cons c cs ih =>
        intro prevs base n d pk h c' hc'
        obtain ⟨hv, _, _, _, _, _, _, hrest⟩ := (carriedChain_cons E).mp h
        rcases List.mem_cons.mp hc' with rfl | hc'
        · omega
        · have := ih hrest c' hc'; omega

    /-- Every version a valid key log carries is at or after its fork point. -/
    theorem KeyLogOk.forkPoint_le {X : OwnerName} {kl : Obj D} (h : KeyLogOk E X kl)
        {c : Carried D} (hc : c ∈ carriedOf kl) : ∃ f, forkPoint kl = some f ∧ f ≤ c.version := by
      obtain ⟨g, k1, hp⟩ := h.parts
      obtain ⟨v, hv, hcv⟩ := List.mem_flatMap.mp hc
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
      have hnone : (kl.versions[i]'hi).keys = none := by
        cases hk : (kl.versions[i]'hi).keys with
        | none => rfl
        | some k => rw [h.carried_keyed E hi hk] at hcv; cases hcv
      have hlast := h.fork_last E hi hnone
      have hpre : (kl.versions.take i).flatMap (·.carried) = [] := by
        rw [List.flatMap_eq_nil_iff]
        intro u hu
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hu
        have hj' : j < i := by simp at hj; omega
        rw [List.getElem_take]
        cases hk : (kl.versions[j]'(by omega)).keys with
        | none => have := h.fork_last E (by omega) hk; omega
        | some k => exact h.carried_keyed E _ hk
      have hsplit : kl.versions = kl.versions.take i ++ [kl.versions[i]'hi] := by
        conv => lhs; rw [← List.take_append_drop i kl.versions]
        congr 1
        rw [List.drop_eq_getElem_cons hi]
        simp [show i + 1 = kl.versions.length from hlast]
      have hco : carriedOf kl = (kl.versions[i]'hi).carried := by
        unfold carriedOf
        generalize kl.versions[i]'hi = vi at hsplit ⊢
        rw [hsplit, List.flatMap_append, hpre]
        simp
      cases i with
      | zero => rw [hp.getElem_zero E hi] at hnone; simp [firstKeyVersion, hp.keys] at hnone
      | succ m =>
        obtain ⟨_, _, _, hfr⟩ := (hp.steps m (by omega)).fork E hnone
        obtain ⟨_, _, _, hfc⟩ := hfr
        cases hcs : (kl.versions[m + 1]'hi).carried with
        | nil => rw [hcs] at hcv; cases hcv
        | cons c0 cs =>
          rw [hcs] at hfc hcv
          obtain ⟨h2, _, _, hbase⟩ := hfc
          unfold ForkBase at hbase
          split at hbase
          · exact hbase.elim
          · have hgt := carriedChain_gt E _ hbase c hcv
            refine ⟨c0.version, ?_, ?_⟩
            · simp [forkPoint, hco, hcs]
            · rcases List.mem_cons.mp hcv with rfl | _
              · exact Nat.le_refl _
              · omega

The theorem: against any valid copy of the key log, with a fork record or
without, a version signed directly without tainted signatures has a good
signature by a current key of a version the copy holds, with its digest,
never of one it only carries.

    /-- **The keys of the other side of a fork never sign uncontested.** -/
    theorem KeyLogOk.clean_held {X : OwnerName} {kl : Obj D} (h : KeyLogOk E X kl) {l : LineId}
        {n : Nat} {d : D} {sigs : List (Sig D)}
        (hs : SignedWith E kl l n d sigs fun s => !tainted kl s) :
        ∃ s ∈ sigs, E.verifies s = true ∧ s.Signs l n d s.keyLog ∧
          s.keyLog.line = keyLogLine l.owner ∧
          ∃ v, kl.versionAt s.keyLog.version = some v ∧
            E.hash (kl.inventory s.keyLog.version) = s.keyLog.digest ∧
            ∃ kv, v.keys = some kv ∧ kv.ended = false ∧ s.key ∈ kv.keys := by
      obtain ⟨s, hs, hver, hsg, hok, hl, kv, hkv, hend, hkey⟩ := hs.signer
      refine ⟨s, hs, hver, hsg, hl, ?_⟩
      have hcarried : ∀ c ∈ carriedOf kl, c.version = s.keyLog.version → False := by
        intro c hc hcv
        obtain ⟨f, hf, hle⟩ := h.forkPoint_le E hc
        simp [tainted, hf, hcv ▸ hle] at hok
      unfold keyVersion at hkv
      split at hkv
      · rename_i v hv
        split at hkv
        · rename_i hd; exact ⟨v, hv, hd, kv, hkv, hend, hkey⟩
        · obtain ⟨c, hc, -⟩ := Option.map_eq_some_iff.mp hkv
          have hm := List.mem_of_find?_eq_some hc
          have hp := List.find?_some hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hp
          exact (hcarried c hm hp.1).elim
      · obtain ⟨c, hc, -⟩ := Option.map_eq_some_iff.mp hkv
        have hm := List.mem_of_find?_eq_some hc
        have hp := List.find?_some hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        exact (hcarried c hm hp.1).elim

## Good signatures stay good, contested stays contested

A signature file that is not invalid, and whose key-log version the reader
reaches, is "good, for ever: later versions of the key log, an end or a
fork never change it" (section 7.3). "Changing the current keys or
`threshold` affects only signatures naming the new version or a later one:
signatures naming earlier versions stay good" (section 6.1), and "The
signatures of an ended owner, and those made with exposed keys, stay good"
(section 6.4). Readers use a longer copy of a key log when they find one:
"Of two copies of a key log, compared up to their fork records (section
6.3), either one extends the other, and readers use the longer" (section
6.5). What a longer copy changes is the subject of this section.

A **longer copy** of a key log: the same object, the same genesis record,
and the versions of the shorter first. It may have other signature files.

    /-- `kl'` is a longer copy of the key log `kl`. -/
    structure LongerCopy (kl kl' : Obj D) : Prop where
      id : kl'.id = kl.id
      genesis : kl'.genesis = kl.genesis
      versions : ∃ t, kl'.versions = kl.versions ++ t

What a reader reads in a copy of a key log, the key-log version a pin
reaches, the keys exposed and the fork point, depends only on its
versions, not on its witness folder:

    theorem keyVersion_same {kl kl' : Obj D} (hid : kl'.id = kl.id)
        (hg : kl'.genesis = kl.genesis) (hv : kl'.versions = kl.versions) (p : Pin D) :
        keyVersion E kl' p = keyVersion E kl p := by
      simp only [keyVersion, carriedOf, Obj.versionAt, Obj.inventory, hid, hg, hv]; rfl

    omit [DecidableEq D] in
    theorem exposed_same {kl kl' : Obj D} (hv : kl'.versions = kl.versions) :
        exposedIn kl' = exposedIn kl ∧ forkPoint kl' = forkPoint kl := by
      simp only [exposedIn, forkPoint, carriedOf, hv]; exact ⟨trivial, trivial⟩

The key-log version that a signature reaches in a valid copy is the one it
reaches in a longer valid copy: without a fork record, the versions held
are held there too, with the same inventories; with one, the longer copy
is the same (`KeyLogOk.frozen_final`). It holds with a fork record or
without.

    /-- **The key-log version a signature reaches stays.** -/
    theorem keyVersion_longer {X : OwnerName} {kl kl' : Obj D} (h : KeyLogOk E X kl)
        (h' : KeyLogOk E X kl') (hlc : LongerCopy kl kl') {p : Pin D} {kv : Keys D}
        (hk : keyVersion E kl p = some kv) : keyVersion E kl' p = some kv := by
      by_cases hf : Frozen kl
      · rw [keyVersion_same E hlc.id hlc.genesis (h'.frozen_final E hlc.versions hf), hk]
      · obtain ⟨v, hv, hd, hvk⟩ := keyVersion_held E (h.carried_nil E hf) hk
        obtain ⟨t, ht⟩ := hlc.versions
        have hn := (Obj.versionAt_bounds hv).2
        have hv' := versionAt_prefix (t := []) (by simp) ht hn hv
        have hd' : E.hash (kl'.inventory p.version) = p.digest := by
          rw [inventory_prefix (t := []) ⟨hlc.id, hlc.genesis⟩ (by simp) ht hn]; exact hd
        unfold keyVersion
        rw [hv']
        simp only [hd', ite_true]
        exact hvk

And so a version signed directly against a copy, by signature files that
pass any test, is signed directly against a longer one: signatures stay
good.

    /-- **Signatures stay good** against a longer copy of the key log. -/
    theorem SignedWith.longer {X : OwnerName} {kl kl' : Obj D} (h : KeyLogOk E X kl)
        (h' : KeyLogOk E X kl') (hlc : LongerCopy kl kl') {l : LineId} {n : Nat} {d : D}
        {sigs : List (Sig D)} {ok : Sig D → Bool} (hs : SignedWith E kl l n d sigs ok) :
        SignedWith E kl' l n d sigs ok := by
      obtain ⟨s, hs, hl, kv, hkv, hend, hpos, hc⟩ := hs
      refine ⟨s, hs, hl, kv, ?_, hend, hpos, hc⟩
      rw [keyVersion_longer E h h' hlc (Option.mem_toList.mp hkv)]
      simp

Exposures and fork points only accumulate: a signature tainted against a
copy is tainted against a longer one. Without a fork record, the copy has
no fork point, and the keys it exposes are exposed in the versions the
longer copy holds; with one, the copies are the same.

    /-- **Taint accumulates** in a longer copy of the key log. -/
    theorem tainted_longer {X : OwnerName} {kl kl' : Obj D} (h : KeyLogOk E X kl)
        (h' : KeyLogOk E X kl') (hlc : LongerCopy kl kl') {s : Sig D}
        (ht : tainted kl s = true) : tainted kl' s = true := by
      by_cases hf : Frozen kl
      · obtain ⟨he, hfp⟩ := exposed_same (h'.frozen_final E hlc.versions hf)
        unfold tainted; rw [he, hfp]; exact ht
      · have hc := h.carried_nil E hf
        have hfp : forkPoint kl = none := by simp [forkPoint, hc]
        simp only [tainted, hfp, Option.any_none, Bool.or_false, decide_eq_true_eq] at ht
        obtain ⟨t, hv⟩ := hlc.versions
        have : s.key ∈ exposedIn kl' := by
          unfold exposedIn at ht ⊢
          rw [hc, List.flatMap_nil, List.append_nil] at ht
          rw [hv, List.flatMap_append]
          exact List.mem_append_left _ (List.mem_append_left _ ht)
        simp [tainted, this]

The converse direction, for signatures without taint. A version signed
directly without tainted signatures against the longer copy is so against
the shorter, provided the shorter reaches the key-log versions its
signature files name: a signature that names a version only the longer
copy holds is unchecked against the shorter (section 7.3), not good. So a
longer copy can make a version contested, never uncontested, as far as the
shorter reaches.

    theorem SignedWith.shorter_clean {X : OwnerName} {kl kl' : Obj D} (h : KeyLogOk E X kl)
        (h' : KeyLogOk E X kl') (hlc : LongerCopy kl kl') {l : LineId} {n : Nat} {d : D}
        {sigs : List (Sig D)} (hreach : ∀ s ∈ sigs, (keyVersion E kl s.keyLog).isSome = true)
        (hs : SignedWith E kl' l n d sigs fun s => !tainted kl' s) :
        SignedWith E kl l n d sigs fun s => !tainted kl s := by
      obtain ⟨s, hs, hl, kv, hkv, hend, hpos, hc⟩ := hs
      obtain ⟨kv0, hkv0⟩ := Option.isSome_iff_exists.mp (hreach s hs)
      have heq : kv0 = kv := by
        have := keyVersion_longer E h h' hlc hkv0
        rw [Option.mem_toList.mp hkv] at this
        exact (Option.some.inj this).symm
      subst heq
      refine ⟨s, hs, hl, kv0, by rw [hkv0]; simp, hend, hpos, Nat.le_trans hc ?_⟩
      apply signers_length_mono E _ (fun _ h => h)
      intro t ht
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht ⊢
      refine ⟨ht.1, ?_⟩
      cases htk : tainted kl t with
      | false => rfl
      | true => rw [tainted_longer E h h' hlc htk] at ht; exact absurd ht.2 (by simp)

The statuses of a version, read against a longer copy: a signed version
stays signed; a version signed and not contested against the longer copy
is so against the shorter, when the shorter reaches the key-log versions
of its signature files; and so a contested version stays contested.

    theorem Signed.longer {X : OwnerName} {kl kl' : Obj D} (h : KeyLogOk E X kl)
        (h' : KeyLogOk E X kl') (hlc : LongerCopy kl kl') {l : LineId} {o : Obj D} {n : Nat}
        (hs : Signed E kl l o n) : Signed E kl' l o n := by
      obtain ⟨h1, m, h2, h3, h4⟩ := hs
      exact ⟨h1, m, h2, h3, h4.longer E h h' hlc⟩

    theorem SignedNotContested.shorter {X : OwnerName} {kl kl' : Obj D} (h : KeyLogOk E X kl)
        (h' : KeyLogOk E X kl') (hlc : LongerCopy kl kl') {l : LineId} {o : Obj D} {n : Nat}
        (hreach : ∀ s ∈ o.sigs, (keyVersion E kl s.keyLog).isSome = true)
        (hs : SignedNotContested E kl' l o n) : SignedNotContested E kl l o n := by
      obtain ⟨h1, m, h2, h3, h4⟩ := hs
      exact ⟨h1, m, h2, h3, SignedWith.shorter_clean E h h' hlc hreach h4⟩

    /-- **Contested stays contested** against a longer copy of the key log. -/
    theorem Contested.longer {X : OwnerName} {kl kl' : Obj D} (h : KeyLogOk E X kl)
        (h' : KeyLogOk E X kl') (hlc : LongerCopy kl kl') {l : LineId} {o : Obj D} {n : Nat}
        (hreach : ∀ s ∈ o.sigs, (keyVersion E kl s.keyLog).isSome = true)
        (hc : Contested E kl l o n) : Contested E kl' l o n :=
      ⟨hc.1.longer E h h' hlc, fun hn => hc.2 (hn.shorter E h h' hlc hreach)⟩

What does make a contested version uncontested is more signature files:
"While it is not ended, the owner MAY sign again, with current keys not
exposed, versions it knows it made that are contested by an exposed key
(section 7.1)" (section 6.4). New signature files, with keys not exposed,
naming a version before any fork point, can bring a version signed without
tainted signatures to its threshold, and `SignedWith.mono`
([chapter 5](38-lines.md)) keeps it so whatever is added after. A longer
copy of the key log never does it alone.

## A takeover, and the owner's only answer

"Whoever holds `nextThreshold` rotation keys of the latest version of a
key log, not revealed, takes the owner over (with a `nextThreshold` of 1,
a single key, section 6.2), without a fork, by signing the next version
with keys of its own; the owner can then only end it, and only if it still
holds copies of those keys itself, by signing another version of that
number, a fork (section 6.3)" (section 15.1).

The first half is constructive: a version with keys, which obeys the rules
of section 6.1 and is signed by `nextThreshold` rotation keys of the latest
version, extends a valid key log validly, whoever signed it. The model has
no notion of who holds a key, and needs none: the signatures are all it
reads.

    /-- **Rotation keys of the latest version extend the key log**, whoever holds
    them. -/
    theorem KeyLogOk.append_keyed {X : OwnerName} {o : Obj D} (ho : KeyLogOk E X o)
        {pk : Keys D} (hpk : keysAt o o.versions.length = some pk) {x : Version D} {k : Keys D}
        {ss : List (Sig D)} (hx : x.keys = some k)
        (h : x.carried = [] ∧ KeysOk E (keysOf o.versions) k ∧
          RotationSigned E X (o.append x ss) o.versions.length pk ∧ k.successor ≠ some X ∧
          x.Plain) :
        KeyLogOk E X (o.append x ss) := by
      have hlen := ho.length_pos E
      refine ho.append_step E hpk (keysAt_last hpk hlen)
        (KeyStep.of_keyed E (keysAt_last hpk hlen) hx ?_)
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      refine ⟨h1, ?_, h3, h4, h5⟩
      simpa [Obj.append] using h2

Then the keys of the new version are the owner's, in any world that holds
the extended copy: a signature naming the new version, made with one of
its keys, is made with an owner's key (`OwnerKey`), and so can sign the
owner's lines wherever an archive holds that copy.

    omit [DecidableEq D] in
    /-- **The new keys count as the owner's.** -/
    theorem takeover_ownerKey {w : World D} {X : OwnerName} {b : ArchiveId} {o : Obj D}
        {x : Version D} {ss : List (Sig D)}
        (hl : lookup w b (.line (keyLogLine X)) = some (.live (o.append x ss))) {k : Keys D}
        (hx : x.keys = some k) (hend : k.ended = false) {s : Sig D}
        (hpin : s.keyLog.line = keyLogLine X ∧ s.keyLog.version = o.versions.length + 1 ∧
          s.keyLog.digest = E.hash ((o.append x ss).inventory (o.versions.length + 1)))
        (hkey : s.key ∈ k.keys) : OwnerKey E w X s := by
      obtain ⟨h1, h2, h3⟩ := hpin
      refine ⟨h1, b, _, hl, x, ?_, by rw [h2, h3], k, hx, hend, hkey⟩
      rw [h2, Obj.versionAt_succ]
      simp [Obj.append]

The second half. Once the new version `x` is held, a later version needs
rotation keys of `x` (`extend_needs_rotation`, [chapter 4](35-owners.md)),
which the thief committed; the owner's old rotation keys, those of the
version before `x`, are never among them, since `next` of `x` "MUST NOT
hold ... a digest that `next` of an earlier version holds" (section 6.1,
rule 3). If every signature of the version after `x` that verifies is made
with an old rotation key, that version is not valid.

    /-- **After a takeover, the owner's old rotation keys extend nothing.** -/
    theorem takeover_locks_out {X : OwnerName} {o : Obj D} {x y : Version D}
        {ss ss' : List (Sig D)} (h : KeyLogOk E X ((o.append x ss).append y ss'))
        (hne : o.versions ≠ []) {pk k ky : Keys D} (hpk : keysAt o o.versions.length = some pk)
        (hx : x.keys = some k) (hy : y.keys = some ky)
        (hold : ∀ s ∈ (o.append x ss).sigs ++ ss', E.verifies s = true → s.line = keyLogLine X →
          s.version = o.versions.length + 2 → E.keyDigest s.key ∈ pk.next) : False := by
      have hlen : 0 < o.versions.length := List.length_pos_iff.mpr hne
      obtain ⟨pk', hpk', s, hs, hver, hl, hv, hd⟩ :=
        extend_needs_rotation E h (by simp [Obj.append]) hy
      have hxk : keysAt (o.append x ss) (o.append x ss).versions.length = some k := by
        simp [keysAt, Obj.append, Obj.versionAt_succ, hx]
      rw [hxk] at hpk'; cases hpk'
      have hold' := hold s hs hver hl (by rw [hv]; simp [Obj.append])
      have hi : o.versions.length < ((o.append x ss).append y ss').versions.length := by
        simp [Obj.append]
      have hxi : (((o.append x ss).append y ss').versions[o.versions.length]'hi).keys = some k := by
        simp [Obj.append, hx]
      have hok := h.keysOk_at E hi hxi
      have hlast := keysAt_last hpk hlen
      have hmem : pk ∈ keysOf (((o.append x ss).append y ss').versions.take o.versions.length) := by
        have hj : o.versions.length - 1 < ((o.append x ss).append y ss').versions.length := by
          simp [Obj.append]; omega
        refine keys_mem_keysOf (i := o.versions.length - 1) (by omega) hj ?_
        simp only [Obj.append, List.append_assoc]
        rw [List.getElem_append_left (by omega)]
        exact hlast
      exact (hok.2.2.2.2.1 _ hd).2 pk hmem hold'

What the owner can still do with its old rotation keys is sign another
version of the number of `x`. An archive that holds the thief's side and
meets it appends a fork record (section 6.3), valid by `ForkRecordOk`,
since the version it carries is signed by rotation keys of the version
before the fork point and differs from `x`; from then on that archive is
frozen for ever (`Events.fork_freezes_forever`), and the owner ended:
"an owner whose rotation keys are stolen can add nothing more under that
identity, and continues under a successor" (section 15.1). Whether a fork
record of a given version is valid is a computation, which the story does
in [chapter 15](72-risks.md); the model does not build fork records in
general.

## A retired key still signs

"A retired key in someone else's hands still makes good signatures naming
the versions that list it" (section 6.2), and, among the residual risks,
"a retired key never exposed still makes good, uncontested signatures
naming the versions that list it (section 6.2)" (section 15.1). In the
model: against a valid copy of the key log without a fork record, a
signature that verifies, signs a version, and names a version of the key
log that the copy holds, with keys listing its key and a `threshold` of 1,
makes that version signed directly without tainted signatures, as long as
the copy does not expose the key; whether later versions still list the
key does not enter.

    /-- **A retired key never exposed still signs**, uncontested. -/
    theorem retired_key_signs {X : OwnerName} {kl : Obj D} (h : KeyLogOk E X kl)
        (hf : ¬ Frozen kl) {l : LineId} {n : Nat} {d : D} {sigs : List (Sig D)} {s : Sig D}
        (hs : s ∈ sigs) (hver : E.verifies s = true) (hsg : s.Signs l n d s.keyLog)
        (hline : s.keyLog.line = keyLogLine l.owner) {v : Version D}
        (hv : kl.versionAt s.keyLog.version = some v)
        (hd : E.hash (kl.inventory s.keyLog.version) = s.keyLog.digest) {kv : Keys D}
        (hkv : v.keys = some kv) (hend : kv.ended = false) (ht : kv.threshold = 1)
        (hkey : s.key ∈ kv.keys) (hexp : s.key ∉ exposedIn kl) :
        SignedWith E kl l n d sigs fun t => !tainted kl t := by
      have hfp : forkPoint kl = none := by simp [forkPoint, h.carried_nil E hf]
      have htaint : tainted kl s = false := by simp [tainted, hfp, hexp]
      have hk : keyVersion E kl s.keyLog = some kv := by
        unfold keyVersion; rw [hv]; simp only [hd, ite_true]; exact hkv
      refine ⟨s, hs, hline, kv, by rw [hk]; simp, hend, by omega, ?_⟩
      rw [ht]
      apply List.length_pos_of_mem (a := s.key)
      unfold signers
      rw [mem_distinct]
      refine List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, ?_⟩, rfl⟩
      simp [hsg, hver, hkey, htaint]

The remedy the specification gives is the exposure: "an owner unsure that
a retired key is destroyed exposes it" (section 15.1), after which
`exposed_keys_add_nothing` applies, and, by the first section of this
chapter, nobody holding current keys can stop it.

    end OpenSheaf
