-- Generated from literate/47-acts.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Worlds

namespace OpenSheaf

variable {D : Type} [DecidableEq D] (E : Env D)

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

theorem ValidStep.ownersSign {w w' : World D} (hs : ValidStep E w w') (hw : OwnersSign E w) :
    OwnersSign E w' := by
  have hst := hs.toStep E
  intro b l o' hl
  have up : (o'.kind ≠ .owner → HeadSigned E w l o') ∧ (o'.kind = .owner → KeyLogOk E l.owner o') →
      (o'.kind ≠ .owner → HeadSigned E w' l o') ∧ (o'.kind = .owner → KeyLogOk E l.owner o') :=
    fun ⟨h1, h2⟩ => ⟨fun hk => by
      obtain ⟨s, hs', hver, hsg, hown⟩ := h1 hk
      exact ⟨s, hs', hver, hsg, hown.step E hst⟩, h2⟩
  cases hs with
  | newArchive a ar ha hempty =>
    rw [lookup_newArchive ha hempty] at hl; exact up (hw b l o' hl)
  | create a ar oid o ha ho _ _ _ _ hauth =>
    rw [lookup_setEntry ha] at hl
    split at hl
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases hl
      exact up (authorised_ownersSign E hauth)
    · exact up (hw b l o' hl)
  | append a ar oid o x ss ha ho _ _ _ _ _ _ _ hauth =>
    rw [lookup_setEntry ha] at hl
    split at hl
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases hl
      exact up (authorised_ownersSign E hauth)
    · exact up (hw b l o' hl)
  | witness a ar oid o ss ha ho =>
    rw [lookup_setEntry ha] at hl
    split at hl
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases hl
      have hlo : lookup w b (.line l) = some (.live o) := by simp [lookup, ha, ho]
      obtain ⟨h1, h2⟩ := hw b l o hlo
      refine up ⟨fun hk => ?_, fun hk => ?_⟩
      · obtain ⟨s, hs, hrest⟩ := h1 hk
        exact ⟨s, List.mem_append_left _ hs, hrest⟩
      · exact (h2 hk).witness E ss
    · exact up (hw b l o' hl)

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
  cases hs with
  | newArchive a ar ha hempty =>
    rw [lookup_newArchive ha hempty] at hl; exact hw b l o' hl
  | create a ar oid o ha ho _ _ _ _ hauth =>
    rw [lookup_setEntry ha] at hl
    split at hl
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases hl
      exact hauth.1
    · exact hw b l o' hl
  | append a ar oid o x ss ha ho _ _ _ _ _ _ _ hauth =>
    rw [lookup_setEntry ha] at hl
    split at hl
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases hl
      exact hauth.1
    · exact hw b l o' hl
  | witness a ar oid o ss ha ho =>
    rw [lookup_setEntry ha] at hl
    split at hl
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases hl
      exact (hw b l o (by simp [lookup, ha, ho])).witness E ss
    · exact hw b l o' hl

theorem Event.identitiesOk {w w' : World D} (he : Event E w w') (hw : IdentitiesOk E w) :
    IdentitiesOk E w' := by
  cases he with
  | step hs => exact hs.identitiesOk E hw
  | takedown a oid o _ hl => exact fun b l o' h => hw b l o' (lookup_takedown E.hash hl h).2

/-- **Every copy keeps its identity**, in every world built by events. -/
theorem Events.identitiesOk {w : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w) : IdentitiesOk E w :=
  hs.invariant _ (·.identitiesOk E) fun _ _ _ h => by simp [lookup] at h

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
      obtain ⟨g', _, hg', _, _, _, hname, _⟩ := hkl.parts
      rw [hg] at hg'; cases hg'
      refine ⟨0, by omega, ?_⟩
      rw [hname]; rw [hl]; rfl
    · rcases h2 with ⟨_, hn, _⟩ | ⟨_, ⟨k, hk, hn⟩, _⟩
      · exact ⟨0, by omega, hn⟩
      · exact ⟨k, hk, hn⟩

/-- **Copies of a line hold one genesis record**, in every world built by
events, unless the names of the two records they hold collide. -/
theorem Events.genesis_agree {w : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w)
    {b b' : ArchiveId} {l : LineId} {o o' : Obj D} (hl : lookup w b (.line l) = some (.live o))
    (hl' : lookup w b' (.line l) = some (.live o'))
    (hcol : ∀ g g' k k', o.genesis = some g → o'.genesis = some g' → k < 16 → k' < 16 →
      E.nameOf g k = E.nameOf g' k' → g = g') : o.genesis = o'.genesis := by
  obtain ⟨g, hg, k, hk, hnk⟩ := (Events.identitiesOk E hs b l o hl).name E
  obtain ⟨g', hg', k', hk', hnk'⟩ := (Events.identitiesOk E hs b' l o' hl').name E
  rw [hg, hg', hcol g g' k k' hg hg' hk hk' (hnk.symm.trans hnk')]

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
      have hi : s.keyLog.version - 2 + 1 < kl.versions.length := by omega
      have hvi : (kl.versions[s.keyLog.version - 2 + 1]'hi) = v := by
        simp only [Obj.versionAt, show s.keyLog.version ≠ 0 by omega, ite_false] at hv
        rw [List.getElem?_eq_getElem (by omega)] at hv
        have := Option.some.inj hv
        rw [← this]; congr 1; omega
      obtain ⟨pk, hpk, s', hs', hver, hl, hvs, hds, hkd⟩ :=
        hlog.held_rotation E hi (k := kv) (by rw [hvi]; exact hkv)
      refine ⟨pk, ?_, s', hs', hver, hl, by rw [hvs]; omega, ?_, hkd⟩
      · simp only [keysAt, Obj.versionAt, show s.keyLog.version - 1 ≠ 0 by omega, ite_false]
        rw [List.getElem?_eq_getElem (by omega)]
        have : s.keyLog.version - 1 - 1 = s.keyLog.version - 2 := by omega
        simp only [this]; exact hpk
      · rw [hds]; congr 2; omega
  · right
    obtain ⟨g, hg, k, hk16, hname⟩ := (Events.identitiesOk E hs b _ kl hkl).name E
    exact ⟨hk, g, k, hg, hk16, hname⟩

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

/-- **A mirror only copies.** -/
theorem mirror_copies {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
    {o' : Obj D} (hok : LineOk E w a ar l o') (hout : l.owner ∉ ar.owners) :
    CopyOf w a o' := by
  obtain ⟨_, _, _, _, _, h⟩ := hok
  rcases h with ⟨hin, _⟩ | hc
  · exact absurd hin hout
  · exact hc

/-- **A fork freezes the owner.** -/
theorem frozen_adds_nothing {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
    {o' kl : Obj D} (hkl : lookup w a (.line (keyLogLine l.owner)) = some (.live kl))
    (hfr : Frozen kl) : ¬ LineOk E w a ar l o' := by
  rintro ⟨kl', hkl', _, hnf, _⟩
  rw [hkl] at hkl'; cases hkl'
  exact hnf hfr

/-- **An ended owner deposits nothing.** -/
theorem ended_copies {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
    {o' kl : Obj D} (hkl : lookup w a (.line (keyLogLine l.owner)) = some (.live kl))
    (hend : HasEnding kl) (hok : LineOk E w a ar l o') : CopyOf w a o' := by
  obtain ⟨kl', hkl', _, _, _, h⟩ := hok
  rw [hkl] at hkl'; cases hkl'
  rcases h with ⟨_, hne⟩ | hc
  · exact absurd hend hne
  · exact hc

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
