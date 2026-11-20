-- Generated from literate/85-reader.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.References
import OpenSheaf.Story

namespace OpenSheaf

variable {D : Type} [DecidableEq D] (E : Env D)

instance (l : LineId) (o : Obj D) : Decidable (IdentityOk E l o) := by
  unfold IdentityOk; split <;> infer_instance

/-- A reader accepts the copy `o` of the line `l` against the copy `kl` of its
owner's key log (sections 6, 7.3 and 7.5). -/
def ReaderAccepts (kl : Obj D) (l : LineId) (o : Obj D) : Prop :=
  o.id = .line l ∧ o.kind ≠ .owner ∧ o.versions ≠ [] ∧ IdentityOk E l o ∧
    KeyLogOk E l.owner kl ∧ ¬ Frozen kl ∧ SignedClean E kl l o o.versions.length

instance (kl : Obj D) (l : LineId) (o : Obj D) : Decidable (ReaderAccepts E kl l o) := by
  unfold ReaderAccepts; infer_instance

/-- **What a reader accepts is signed with a current key of the key log.** -/
theorem ReaderAccepts.signer {kl : Obj D} {l : LineId} {o : Obj D}
    (h : ReaderAccepts E kl l o) :
    ∃ s ∈ o.sigs, E.verifies s = true ∧
      s.Signs l o.versions.length (E.hash (o.inventory o.versions.length)) s.keyLog ∧
      s.keyLog.line = keyLogLine l.owner ∧
      ∃ v, kl.versionAt s.keyLog.version = some v ∧
        E.hash (kl.inventory s.keyLog.version) = s.keyLog.digest ∧
        ∃ kv, v.keys = some kv ∧ kv.ended = false ∧ s.key ∈ kv.keys ∧
          s.key ∉ exposedIn kl := by
  obtain ⟨_, _, _, _, hkl, hf, hs⟩ := h
  obtain ⟨s, hs, hver, hsg, hok, hl, kv, hkv, hend, hkey⟩ := hs.signer
  obtain ⟨v, hv, hd, hvk⟩ := keyVersion_held E (hkl.carried_nil E hf) hkv
  exact ⟨s, hs, hver, hsg, hl, v, hv, hd, kv, hvk, hend, hkey, not_tainted_not_exposed hok⟩

/-- **Every version of a key log with keys comes from the genesis record or
from rotation keys.** -/
theorem KeyLogOk.origin {X : OwnerName} {kl : Obj D} (h : KeyLogOk E X kl) {m : Nat}
    {v : Version D} (hv : kl.versionAt m = some v) {kv : Keys D} (hkv : v.keys = some kv) :
    (m = 1 ∧ ∃ g, kl.genesis = some g ∧ g.kind = .owner ∧ E.nameOf g 0 = X ∧
      v = firstKeyVersion g ∧ g.keys = some kv) ∨
    (∃ pk, keysAt kl (m - 1) = some pk ∧ ∃ s ∈ kl.sigs, E.verifies s = true ∧
      s.line = keyLogLine X ∧ s.version = m ∧ s.digest = E.hash (kl.inventory m) ∧
      E.keyDigest s.key ∈ pk.next) := by
  obtain ⟨h1, h2⟩ := Obj.versionAt_bounds hv
  obtain ⟨g, k1, hp⟩ := h.parts
  by_cases hm : m = 1
  · subst hm
    rw [Obj.versionAt_succ, List.getElem?_eq_getElem (by omega)] at hv
    have hv0 := Option.some.inj hv
    rw [hp.getElem_zero E (by omega)] at hv0
    subst hv0
    exact Or.inl ⟨rfl, g, hp.genesis, hp.gkind, hp.name, rfl, hkv⟩
  · right
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 2 := ⟨m - 2, by omega⟩
    have hi : i + 1 < kl.versions.length := by omega
    have hvi : (kl.versions[i + 1]'hi) = v := by
      rw [Obj.versionAt_succ, List.getElem?_eq_getElem hi] at hv
      exact Option.some.inj hv
    obtain ⟨pk, hpk, s, hs, hver, hl, hvs, hds, hkd⟩ :=
      h.held_rotation E hi (k := kv) (by rw [hvi]; exact hkv)
    refine ⟨pk, ?_, s, hs, hver, hl, hvs, hds, hkd⟩
    rw [show i + 2 - 1 = i + 1 by omega, keysAt, Obj.versionAt_succ,
      List.getElem?_eq_getElem (by omega)]
    exact hpk

/-- **The key that signs what a reader accepts comes from the genesis record of
the owner, or from rotation keys.** -/
theorem ReaderAccepts.origin {kl : Obj D} {l : LineId} {o : Obj D}
    (h : ReaderAccepts E kl l o) :
    ∃ s ∈ o.sigs, E.verifies s = true ∧
      s.Signs l o.versions.length (E.hash (o.inventory o.versions.length)) s.keyLog ∧
      ∃ v kv, kl.versionAt s.keyLog.version = some v ∧ v.keys = some kv ∧ s.key ∈ kv.keys ∧
        ((s.keyLog.version = 1 ∧ ∃ g, kl.genesis = some g ∧ g.kind = .owner ∧
            E.nameOf g 0 = l.owner ∧ v = firstKeyVersion g ∧ g.keys = some kv) ∨
         (∃ pk, keysAt kl (s.keyLog.version - 1) = some pk ∧ ∃ s' ∈ kl.sigs,
            E.verifies s' = true ∧ s'.line = keyLogLine l.owner ∧
            s'.version = s.keyLog.version ∧
            s'.digest = E.hash (kl.inventory s.keyLog.version) ∧
            E.keyDigest s'.key ∈ pk.next)) := by
  obtain ⟨s, hs, hver, hsg, _, v, hv, _, kv, hkv, _, hkey, _⟩ := h.signer
  exact ⟨s, hs, hver, hsg, v, kv, hv, hkv, hkey, h.2.2.2.2.1.origin E hv hkv⟩

omit [DecidableEq D] in
/-- **The head fixes the history**, unless the two inventories collide. -/
theorem head_fixes_history {o o' : Obj D} (hn : o'.versions.length = o.versions.length)
    (hd : E.hash (o'.inventory o.versions.length) = E.hash (o.inventory o.versions.length))
    (hcol : NoCollision E (o'.inventory o.versions.length) (o.inventory o.versions.length)) :
    o'.versions = o.versions ∧ o'.genesis = o.genesis := by
  have heq := hcol hd
  have hv := congrArg Inventory.versions heq
  simp only [Obj.inventory, List.take_length] at hv
  rw [← hn, List.take_length] at hv
  exact ⟨hv, congrArg Inventory.genesis heq⟩

/-- The keys of the versions held in `kl` sign only prefixes of the history `H`
of `l`, whose genesis record is `g`. -/
def KeysSignHistory (kl : Obj D) (l : LineId) (g : Option (Genesis D))
    (H : List (Version D)) : Prop :=
  ∀ s, E.verifies s = true → s.line = l → s.keyLog.line = keyLogLine l.owner →
    (∃ v, kl.versionAt s.keyLog.version = some v ∧
      E.hash (kl.inventory s.keyLog.version) = s.keyLog.digest ∧
      ∃ kv, v.keys = some kv ∧ s.key ∈ kv.keys) →
    s.version ≤ H.length ∧ s.digest = E.hash (histInv l g H s.version)

/-- **No host forges a version.** -/
theorem ReaderAccepts.no_forgery {kl : Obj D} {l : LineId} {o : Obj D}
    (h : ReaderAccepts E kl l o) {g : Option (Genesis D)} {H : List (Version D)}
    (hsign : KeysSignHistory E kl l g H)
    (hcol : NoCollision E (o.inventory o.versions.length) (histInv l g H o.versions.length)) :
    o.versions.length ≤ H.length ∧ o.versions = H.take o.versions.length ∧ o.genesis = g := by
  obtain ⟨s, _, hver, hsg, hl, v, hv, hd, kv, hkv, _, hkey, _⟩ := h.signer
  obtain ⟨hle, hdig⟩ := hsign s hver hsg.1 hl ⟨v, hv, hd, kv, hkv, hkey⟩
  rw [hsg.2.1] at hle hdig
  have heq := hcol (hsg.2.2.1.symm.trans hdig)
  have hv' := congrArg Inventory.versions heq
  simp only [Obj.inventory, histInv, List.take_length] at hv'
  exact ⟨hle, hv', congrArg Inventory.genesis heq⟩

/-- **Readers agree**, when the owner's keys sign one history. -/
theorem readers_agree {kl kl' : Obj D} {l : LineId} {o o' : Obj D}
    (h : ReaderAccepts E kl l o) (h' : ReaderAccepts E kl' l o')
    {g : Option (Genesis D)} {H : List (Version D)}
    (hsign : KeysSignHistory E kl l g H) (hsign' : KeysSignHistory E kl' l g H)
    (hcol : NoCollision E (o.inventory o.versions.length) (histInv l g H o.versions.length))
    (hcol' : NoCollision E (o'.inventory o'.versions.length)
      (histInv l g H o'.versions.length)) :
    Comparable o.versions o'.versions := by
  obtain ⟨_, e1, _⟩ := h.no_forgery E hsign hcol
  obtain ⟨_, e2, _⟩ := h'.no_forgery E hsign' hcol'
  have t1 := List.take_append_drop o.versions.length H
  have t2 := List.take_append_drop o'.versions.length H
  rw [← e1] at t1; rw [← e2] at t2
  exact comparable_of_prefixes t1.symm t2.symm

end OpenSheaf

namespace OpenSheaf.Story

example : lookup w19 "coauthor" (.line paperLine) = some (.live paper3) ∧
    lookup w19 "coauthor" (.line (keyLogLine "author")) = some (.live logA2) := ⟨rfl, rfl⟩

example : ¬ ReaderAccepts E logA2 paperLine { paper3 with versions := [v1', v2, v3] } := by
  decide

example : ReaderAccepts E logA2 paperLine paper4 ∧ ¬ ReaderAccepts E logA3 paperLine paper4 := by
  decide

theorem mirror_accepted : ReaderAccepts E logA2 paperLine paper3 := by decide

example := ReaderAccepts.signer E mirror_accepted

example := ReaderAccepts.origin E mirror_accepted

end OpenSheaf.Story
