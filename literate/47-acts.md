# Owners sign, places host

Owners sign, places host: in version 0.2 of the specification, "an
archive only hosts what owners write there, and copies what others wrote
elsewhere; it decides nothing about what is authentic" (section 1), and "a
host or a network therefore cannot ... add [a version] to another owner's
line" (section 15.1).
Version 0.1 of the specification had no owners: an archive held its own
objects, and an earlier version of this model filled the gap with
**writers**, the agents through whom an archive acted. Version 0.2 replaces
them by keys, which the model now has: an archive "decides only which
owners it hosts" (section 3), and a version is added only when its owner's
keys sign it (section 7.5).

This chapter proves what follows, in every world built by events:

- every copy of every line, mirrors included, holds as its head a version
  signed by a signature that verifies, made with a current key of a version
  of the owner's key log that an archive of the world holds, and that
  version vouches for every version before it (`Events.headsSigned`); so a
  version of an owner's line appears in an archive only if someone signed it
  with such a key (`forgery_needs_owner_key`), and a selection changes only
  by its curator's keys (the same theorem, for the selection's line). Such
  keys are the owner's, or those that whoever holds its rotation keys
  commits in a new version of its key log, which the key log then shows,
  unless names collide (`Events.ownerKey_origin`):
  "whoever holds `nextThreshold` rotation keys of the latest version of a
  key log, not revealed, takes the owner over" (section 15.1);
- every copy of every key log is valid (`Events.keyLogsOk`);
- an archive that does not host an owner only copies its lines
  (`mirror_copies`); an archive that knows of a fork of an owner's key log
  adds nothing to its lines (`frozen_adds_nothing`); one that knows of an
  ending version adds only copies (`ended_copies`); and nobody can add a
  version with keys that the archive's copy of the key log exposes
  (`exposed_keys_add_nothing`).

    -- in OpenSheaf/Acts.lean:
    import OpenSheaf.Worlds

    namespace OpenSheaf

    variable {D : Type} [DecidableEq D] (E : Env D)

## Signed by the owner

A signature file is **the owner's**, in a world, when it names a version
of the owner's key log that some archive of the world holds, with the
digest of the pin, that version is not an ending version, and the key is
one of its current keys. Section 7.5 judges a version "against the key log
the archive holds"; the model asks for a key log the world holds, so that
nothing is assumed of key logs that could be written but are held
nowhere. In a world built by events, every key log held is valid (below),
and once held stays held: key logs are not taken down in the model
([chapter 7](45-worlds.md)).

    /-- The signature `s` is made with a current key of a version, not an ending
    version, of a copy of the key log of the owner `X` that the world `w` holds. -/
    def OwnerKey (w : World D) (X : OwnerName) (s : Sig D) : Prop :=
      s.keyLog.line = keyLogLine X ∧ ∃ b kl, lookup w b (.line (keyLogLine X)) = some (.live kl) ∧
        ∃ v, kl.versionAt s.keyLog.version = some v ∧
          E.hash (kl.inventory s.keyLog.version) = s.keyLog.digest ∧
          ∃ kv, v.keys = some kv ∧ kv.ended = false ∧ s.key ∈ kv.keys

    /-- The head of the copy `o` of line `l` is signed by its owner, in `w`: a
    signature in its witness folder verifies, signs it, and is the owner's. -/
    def HeadSigned (w : World D) (l : LineId) (o : Obj D) : Prop :=
      ∃ s ∈ o.sigs, E.verifies s = true ∧
        s.Signs l o.versions.length (E.hash (o.inventory o.versions.length)) s.keyLog ∧
        OwnerKey E w l.owner s

    /-- Every copy of a line that is not a key log has a head signed by its owner,
    and every copy of a key log is valid. -/
    def OwnersSign (w : World D) : Prop :=
      ∀ b l o, lookup w b (.line l) = some (.live o) →
        (o.kind ≠ .owner → HeadSigned E w l o) ∧ (o.kind = .owner → KeyLogOk E l.owner o)

What makes a key the owner's stays so through steps, which only make key
logs grow, and through takedowns, which in the model never take down a key
log.

    omit [DecidableEq D] in
    theorem OwnerKey.step {w w' : World D} (hs : Step w w') {X : OwnerName} {s : Sig D}
        (h : OwnerKey E w X s) : OwnerKey E w' X s := by
      obtain ⟨hl, b, kl, hkl, v, hv, hd, kv, hkv⟩ := h
      obtain ⟨kl', hkl', hg⟩ := hs.live_grows hkl
      obtain ⟨t, ht⟩ := hg.versions
      have hn := (Obj.versionAt_bounds hv).2
      refine ⟨hl, b, kl', hkl', v, versionAt_prefix (t := []) (by simp) ht hn hv, ?_, kv, hkv⟩
      rw [inventory_prefix (t := []) ⟨hg.id, hg.genesis⟩ (by simp) ht hn]; exact hd

    omit [DecidableEq D] in
    theorem OwnerKey.steps {w w' : World D} (hs : Steps w w') {X : OwnerName} {s : Sig D}
        (h : OwnerKey E w X s) : OwnerKey E w' X s :=
      hs.invariant (fun w => OwnerKey E w X s) (fun hs h => h.step E hs) h

    omit [DecidableEq D] in
    theorem OwnerKey.takedown {w : World D} {a : ArchiveId} {l : LineId} {o : Obj D}
        (hk : l ≠ keyLogLine l.owner) (hlo : lookup w a (.line l) = some (.live o))
        {X : OwnerName} {s : Sig D} (h : OwnerKey E w X s) :
        OwnerKey E (takedown E.hash w a (.line l) o) X s := by
      obtain ⟨hl, b, kl, hkl, rest⟩ := h
      refine ⟨hl, b, kl, ?_, rest⟩
      rw [lookup_takedown_eq E.hash hlo, if_no]
      · exact hkl
      · rintro ⟨rfl, he⟩
        apply hk
        have := ObjectId.line.inj he
        rw [← this]; rfl

A valid step that writes a line checks exactly this: the head of the new
state is signed directly against the archive's copy of the owner's key
log, which is valid and not frozen, so that it carries no version of
another side (`LineOk`, [chapter 7](45-worlds.md); `KeyLogOk.carried_nil`,
[chapter 5](38-lines.md)); and a key log is valid (`IdentityOk`).
`SignedWith.signer` gives the signature.

    theorem authorised_ownersSign {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
        {o : Obj D} (h : Authorised E w a ar (.line l) o) :
        (o.kind ≠ .owner → HeadSigned E w l o) ∧ (o.kind = .owner → KeyLogOk E l.owner o) := by
      obtain ⟨hid, hline⟩ := h
      refine ⟨fun hk => ?_, fun hk => ?_⟩
      · obtain ⟨kl, hkla, hkl, hnf, hsig, _⟩ := hline hk
        obtain ⟨s, hs, hver, hsg, _, hll, kv, hkv, hend, hkey⟩ := hsig.signer
        obtain ⟨v, hv, hd, hvk⟩ := keyVersion_held E (hkl.carried_nil E hnf) hkv
        exact ⟨s, hs, hver, hsg, hll, a, kl, hkla, v, hv, hd, kv, hvk, hend, hkey⟩
      · unfold IdentityOk at hid
        split at hid
        · exact hid.elim
        · rw [if_yes hk] at hid
          exact hid.2.2

Witnesses keep the head signed, since they only add signature files; a
step that does not touch an entry keeps it, and keeps its signatures the
owner's. The proof goes by what the step did to the entry
(`ValidStep.live_cases`, [chapter 7](45-worlds.md)).

    theorem ValidStep.ownersSign {w w' : World D} (hs : ValidStep E w w') (hw : OwnersSign E w) :
        OwnersSign E w' := by
      have hst := hs.toStep E
      intro b l o' hl
      have up : (o'.kind ≠ .owner → HeadSigned E w l o') ∧ (o'.kind = .owner → KeyLogOk E l.owner o') →
          (o'.kind ≠ .owner → HeadSigned E w' l o') ∧ (o'.kind = .owner → KeyLogOk E l.owner o') :=
        fun ⟨h1, h2⟩ => ⟨fun hk => by
          obtain ⟨s, hs', hver, hsg, hown⟩ := h1 hk
          exact ⟨s, hs', hver, hsg, hown.step E hst⟩, h2⟩
      rcases hs.live_cases E hl with hl0 | ⟨_, _, hauth, _⟩ | ⟨o, ss, hlo, rfl, _⟩
      · exact up (hw b l o' hl0)
      · exact up (authorised_ownersSign E hauth)
      · obtain ⟨h1, h2⟩ := hw b l o hlo
        refine up ⟨fun hk => ?_, fun hk => ?_⟩
        · obtain ⟨s, hs, hrest⟩ := h1 hk
          exact ⟨s, List.mem_append_left _ hs, hrest⟩
        · exact (h2 hk).witness E ss

A takedown only removes a copy, never a key log.

    theorem takedown_ownersSign {w : World D} {a : ArchiveId} {l : LineId} {o : Obj D}
        (hk : l ≠ keyLogLine l.owner) (hl : lookup w a (.line l) = some (.live o))
        (hw : OwnersSign E w) : OwnersSign E (takedown E.hash w a (.line l) o) := by
      intro b l' o' h
      obtain ⟨h1, h2⟩ := hw b l' o' (lookup_takedown E.hash hl h).2
      refine ⟨fun hk' => ?_, h2⟩
      obtain ⟨s, hs', hver, hsg, hown⟩ := h1 hk'
      exact ⟨s, hs', hver, hsg, hown.takedown E hk hl⟩

    theorem Event.ownersSign {w w' : World D} (he : Event E w w') (hw : OwnersSign E w) :
        OwnersSign E w' := by
      cases he with
      | step hs => exact hs.ownersSign E hw
      | takedown a l o hk hl => exact takedown_ownersSign E hk hl hw

    /-- **Owners sign, places host.** In every world built by events, the head of
    every copy of every line is signed by its owner, with a key of a key log the
    world holds, and every copy of a key log is valid. -/
    theorem Events.ownersSign {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) : OwnersSign E w :=
      hs.invariant _ (·.ownersSign E) fun _ _ _ h => by simp [lookup] at h

    theorem Events.headsSigned {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {b : ArchiveId} {l : LineId}
        {o : Obj D} (hl : lookup w b (.line l) = some (.live o)) (hk : o.kind ≠ .owner) :
        HeadSigned E w l o :=
      (Events.ownersSign E hs b l o hl).1 hk

    theorem Events.keyLogsOk {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {b : ArchiveId} {l : LineId}
        {o : Obj D} (hl : lookup w b (.line l) = some (.live o)) (hk : o.kind = .owner) :
        KeyLogOk E l.owner o :=
      (Events.ownersSign E hs b l o hl).2 hk

## Every copy keeps its identity

A valid step checks the identity of every line it writes (`IdentityOk`,
[chapter 7](45-worlds.md)): its genesis record, its name among the names of
that record, and its branch points. The check holds of every copy of every
line in every world built by events, not only when the copy is written:
witnesses change neither the genesis record nor the versions, and keep a
key log valid (`KeyLogOk.witness`), and a takedown only removes a copy.

    /-- Every copy of every line has the identity of its line. -/
    def IdentitiesOk (w : World D) : Prop :=
      ∀ b l o, lookup w b (.line l) = some (.live o) → IdentityOk E l o

    theorem IdentityOk.witness {l : LineId} {o : Obj D} (h : IdentityOk E l o)
        (ss : List (Sig D)) : IdentityOk E l { o with sigs := o.sigs ++ ss } := by
      unfold IdentityOk at h ⊢
      split at h
      · exact h.elim
      · rename_i g hg
        rw [show ({ o with sigs := o.sigs ++ ss } : Obj D).genesis = some g from hg]
        obtain ⟨h1, h2⟩ := h
        refine ⟨h1, ?_⟩
        split
        · rename_i hk
          rw [if_yes hk] at h2
          exact ⟨h2.1, KeyLogOk.more_sigs E (o := o) rfl rfl hg.symm rfl
            (fun _ hs => List.mem_append_left ss hs) h2.2⟩
        · rename_i hk
          rw [if_no hk] at h2
          exact h2

    theorem ValidStep.identitiesOk {w w' : World D} (hs : ValidStep E w w')
        (hw : IdentitiesOk E w) : IdentitiesOk E w' := by
      intro b l o' hl
      rcases hs.live_cases E hl with hl0 | ⟨_, _, hauth, _⟩ | ⟨o, ss, hlo, rfl, _⟩
      · exact hw b l o' hl0
      · exact hauth.1
      · exact (hw b l o hlo).witness E ss

    theorem Event.identitiesOk {w w' : World D} (he : Event E w w') (hw : IdentitiesOk E w) :
        IdentitiesOk E w' := by
      cases he with
      | step hs => exact hs.identitiesOk E hw
      | takedown a oid o _ hl => exact fun b l o' h => hw b l o' (lookup_takedown E.hash hl h).2

    /-- **Every copy keeps its identity**, in every world built by events. -/
    theorem Events.identitiesOk {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) : IdentitiesOk E w :=
      hs.invariant _ (·.identitiesOk E) fun _ _ _ h => by simp [lookup] at h

A line's name is one of the 16 names of the genesis record its copies hold:
algorithm 0 for an originator's line and for a key log, one of the 16 for
a branch.

    theorem IdentityOk.name {l : LineId} {o : Obj D} (h : IdentityOk E l o) :
        ∃ g, o.genesis = some g ∧ ∃ k, k < 16 ∧ l.name = E.nameOf g k := by
      unfold IdentityOk at h
      split at h
      · exact h.elim
      · rename_i g hg
        refine ⟨g, hg, ?_⟩
        obtain ⟨_, h2⟩ := h
        split at h2
        · obtain ⟨hl, hkl⟩ := h2
          obtain ⟨g', _, hp⟩ := hkl.parts
          have hg' := hp.genesis
          rw [hg] at hg'; cases hg'
          refine ⟨0, by omega, ?_⟩
          rw [hp.name]; rw [hl]; rfl
        · rcases h2 with ⟨_, hn, _⟩ | ⟨_, ⟨k, hk, hn⟩, _⟩
          · exact ⟨0, by omega, hn⟩
          · exact ⟨k, hk, hn⟩

So all copies of a line hold the same genesis record, unless two genesis
records have a name in common: "names made by different algorithms never
coincide" (section 5.2), and a reader holding a name holds nothing else
that ties it to a record. The hypothesis, as elsewhere, is that the names
of the two records being compared, those the copies hold, do not collide.

    /-- **Copies of a line hold one genesis record**, in every world built by
    events, unless the names of the two records they hold collide. -/
    theorem Events.genesis_agree_of_names {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w)
        {b b' : ArchiveId} {l : LineId} {o o' : Obj D} (hl : lookup w b (.line l) = some (.live o))
        (hl' : lookup w b' (.line l) = some (.live o'))
        (hcol : ∀ g g' k k', o.genesis = some g → o'.genesis = some g' → k < 16 → k' < 16 →
          E.nameOf g k = E.nameOf g' k' → g = g') : o.genesis = o'.genesis := by
      obtain ⟨g, hg, k, hk, hnk⟩ := (Events.identitiesOk E hs b l o hl).name E
      obtain ⟨g', hg', k', hk', hnk'⟩ := (Events.identitiesOk E hs b' l o' hl').name E
      rw [hg, hg', hcol g g' k k' hg hg' hk hk' (hnk.symm.trans hnk')]

## Where an owner's key comes from

A key counts as the owner's when a version of the owner's key log that the
world holds lists it as current (`OwnerKey`). In a world built by events,
that version is the first, computed from the owner's genesis record, or a
version signed by rotation keys of the version before it: the owner's
keys, or keys that whoever held its rotation keys committed. Or else the
copy held at the key log's line is not a key log at all, which needs a
genesis record of another kind with the owner's name, a collision of
names.

    /-- **An owner's key comes from its key log**: the first version, or a version
    signed by rotation keys of the one before; unless names collide. -/
    theorem Events.ownerKey_origin {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {X : OwnerName} {s : Sig D}
        (h : OwnerKey E w X s) :
        ∃ b kl, lookup w b (.line (keyLogLine X)) = some (.live kl) ∧
          ((KeyLogOk E X kl ∧ (s.keyLog.version = 1 ∨
            ∃ pk, keysAt kl (s.keyLog.version - 1) = some pk ∧ ∃ s' ∈ kl.sigs,
              E.verifies s' = true ∧ s'.line = keyLogLine X ∧ s'.version = s.keyLog.version ∧
              s'.digest = E.hash (kl.inventory s.keyLog.version) ∧ E.keyDigest s'.key ∈ pk.next)) ∨
           (kl.kind ≠ .owner ∧ ∃ g k, kl.genesis = some g ∧ k < 16 ∧ X = E.nameOf g k)) := by
      obtain ⟨_, b, kl, hkl, v, hv, _, kv, hkv, _⟩ := h
      refine ⟨b, kl, hkl, ?_⟩
      by_cases hk : kl.kind = .owner
      · have hlog : KeyLogOk E X kl := Events.keyLogsOk E hs (l := keyLogLine X) hkl hk
        left
        refine ⟨hlog, ?_⟩
        obtain ⟨h1, h2⟩ := Obj.versionAt_bounds hv
        by_cases hn : s.keyLog.version = 1
        · exact Or.inl hn
        · right
          obtain ⟨m, hm⟩ : ∃ m, s.keyLog.version = m + 2 := ⟨s.keyLog.version - 2, by omega⟩
          have hi : m + 1 < kl.versions.length := by omega
          have hvi : (kl.versions[m + 1]'hi) = v := by
            rw [hm, Obj.versionAt_succ, List.getElem?_eq_getElem hi] at hv
            exact Option.some.inj hv
          obtain ⟨pk, hpk, s', hs', hver, hl, hvs, hds, hkd⟩ :=
            hlog.held_rotation E hi (k := kv) (by rw [hvi]; exact hkv)
          refine ⟨pk, ?_, s', hs', hver, hl, by rw [hvs, hm], by rw [hds, hm], hkd⟩
          rw [hm, show m + 2 - 1 = m + 1 by omega, keysAt, Obj.versionAt_succ,
            List.getElem?_eq_getElem (by omega)]
          exact hpk
      · right
        obtain ⟨g, hg, k, hk16, hname⟩ := (Events.identitiesOk E hs b _ kl hkl).name E
        exact ⟨hk, g, k, hg, hk16, hname⟩

## Nobody else can add to a line

The head of a copy vouches for every version before it (section 7.3), and
is signed with a current key of a version of the owner's key log that the
world holds. So no archive, and no thief, can make a version of an owner's
line appear anywhere unless someone holding such a key signed exactly that
version: its line, its number and the digest of its inventory. Such keys
are the owner's own, unless someone holding its rotation keys extended its
key log with keys of its own, which the key log then shows, unless names
collide (`Events.ownerKey_origin`, above). The model
states it as a contrapositive: if no signature made with such a key
verifies for any version of the line, the line has no copy.

    /-- **Forgery needs an owner's key.** If no signature of the line `l` that
    verifies is made with a current key of a version of its owner's key log held
    in `w`, no archive of `w` holds a copy of `l`, in any world built by events. -/
    theorem forgery_needs_owner_key {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {l : LineId}
        (hno : ∀ s, E.verifies s = true → s.line = l → ¬ OwnerKey E w l.owner s)
        {b : ArchiveId} {o : Obj D} (hl : lookup w b (.line l) = some (.live o))
        (hk : o.kind ≠ .owner) : False := by
      obtain ⟨s, _, hver, hsg, hown⟩ := Events.headsSigned E hs hl hk
      exact hno s hver hsg.1 hown

**A selection changes only by its curator.** A selection is a line, and
its curator is its owner (section 8). Every version of every copy of it is
vouched for by a signature of the curator's keys: the authors of a paper
cannot change a journal's selection of it, nor a host the selections it
keeps, unless they hold the curator's keys. The same holds of every line:
a paper's versions were signed by its owner, a catalogue's by its curator.

## What an archive adds

Four rules of section 7.5, each a consequence of what a valid step checks
when it writes a line (`LineOk`, [chapter 7](45-worlds.md)). An archive that
does not host the owner of a line holds a **mirror** (section 11): it only
copies.

    /-- **A mirror only copies.** -/
    theorem mirror_copies {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
        {o' : Obj D} (hok : LineOk E w a ar l o') (hout : l.owner ∉ ar.owners) :
        CopyOf w a o' := by
      obtain ⟨_, _, _, _, _, h⟩ := hok
      rcases h with ⟨hin, _⟩ | hc
      · exact absurd hin hout
      · exact hc

"A fork freezes the owner" (section 7.5): an archive whose copy of the
owner's key log has a fork record adds no version of the owner's lines.

    /-- **A fork freezes the owner.** -/
    theorem frozen_adds_nothing {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
        {o' kl : Obj D} (hkl : lookup w a (.line (keyLogLine l.owner)) = some (.live kl))
        (hfr : Frozen kl) : ¬ LineOk E w a ar l o' := by
      rintro ⟨kl', hkl', _, hnf, _⟩
      rw [hkl] at hkl'; cases hkl'
      exact hnf hfr

"Ended owners": once the archive's copy of the key log has an ending
version, it takes the owner's versions "only from copies found elsewhere,
never as new deposits" (section 7.5).

    /-- **An ended owner deposits nothing.** -/
    theorem ended_copies {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
        {o' kl : Obj D} (hkl : lookup w a (.line (keyLogLine l.owner)) = some (.live kl))
        (hend : HasEnding kl) (hok : LineOk E w a ar l o') : CopyOf w a o' := by
      obtain ⟨kl', hkl', _, _, _, h⟩ := hok
      rw [hkl] at hkl'; cases hkl'
      rcases h with ⟨_, hne⟩ | hc
      · exact absurd hend hne
      · exact hc

And exposed keys: "whoever holds `threshold` current keys of an owner signs
versions of its lines as that owner until the owner exposes them, after
which what those keys alone sign is contested, and archives aware of it
never add it" (section 15.1). If every signature of the new head that
verifies is made with a key the archive's copy of the key log exposes, the
archive does not add it.

    /-- **Exposed keys add nothing.** -/
    theorem exposed_keys_add_nothing {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
        {o' kl : Obj D} (hkl : lookup w a (.line (keyLogLine l.owner)) = some (.live kl))
        (hexp : ∀ s ∈ o'.sigs, E.verifies s = true → s.key ∈ exposedIn kl) :
        ¬ LineOk E w a ar l o' := by
      rintro ⟨kl', hkl', _, _, hsig, _⟩
      rw [hkl] at hkl'; cases hkl'
      obtain ⟨s, hs, hver, _, hok, _⟩ := hsig.signer
      exact not_tainted_not_exposed hok (hexp s hs hver)

    end OpenSheaf
