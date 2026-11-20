# A reader's check

The theorems of [chapter 8](47-acts.md) hold in worlds built by events:
they say what archives that follow the protocol hold. A reader cannot
know how a copy came to it. It fetches a copy of a line and a copy of the
owner's key log, from any host, and checks them: "Pins and signatures make
every copy checkable wherever it is fetched (sections 4 and 7) ... A host
or a network therefore cannot forge a version, nor add one to another
owner's line (section 7.5)" (section 15.1); "A key log checks itself from
its owner name ... A copy from any source is therefore as good as the
original, and a line can be checked without trusting any host, also after
the archives that served it have gone" (section 6.5).

This chapter defines the check a reader makes of one copy, and proves what
it guarantees for any objects at all, with no assumption on the world or
on the host that served them. Two assumptions remain, and only two: that a
signature verifies only when it was made with its key, which is what the
environment's `verifies` means, and, for the last theorems, that the
inventories compared do not collide. What the reader accepts:

- has a head signed by a signature that verifies, signs exactly that head
  (its line, its number and the digest of its inventory), and is made with
  a current key, not exposed, of a version that the reader's copy of the
  key log holds and that is not an ending version
  (`ReaderAccepts.signer`);
- that version of the key log is the first, computed from the genesis
  record whose name by algorithm 0 is the owner name, or was signed by
  rotation keys of the version before, and so on back to the first
  (`KeyLogOk.origin`, `ReaderAccepts.origin`);
- is, version by version, the history the owner's keys signed, unless
  inventories collide: the head's digest fixes every version before it
  (`head_fixes_history`), and if the owner's keys sign only one history,
  every copy accepted is a prefix of it (`ReaderAccepts.no_forgery`), and
  any two copies accepted agree (`readers_agree`).

    -- in OpenSheaf/Reader.lean:
    import OpenSheaf.References
    import OpenSheaf.Story

    namespace OpenSheaf

    variable {D : Type} [DecidableEq D] (E : Env D)

## The check

The identity of a line, `IdentityOk` ([chapter 7](45-worlds.md)), needs no
world: the genesis record, the name and, for a branch, the parent's line,
are in the copy. A reader decides it by computation.

    instance (l : LineId) (o : Obj D) : Decidable (IdentityOk E l o) := by
      unfold IdentityOk; split <;> infer_instance

A reader **accepts** a copy `o` of the line `l`, against a copy `kl` of
its owner's key log, when `o` is a line that is not a key log, stored
under `l`, with at least one version and the identity of `l`; `kl` is a
valid key log of the owner of `l` (section 6, `KeyLogOk`), without a fork
record; and the head of `o` is signed directly, without tainted
signatures, against `kl` (section 7.3, `SignedClean`). It is the check an
archive makes before adding a version (section 7.5, `LineOk`), without
the archive: what the archive hosts, and where the copy came from, are no
concern of the reader. An ending version in `kl` does not stop the reader:
"signatures made before it name earlier versions, and stay good" (section
6.3).

    /-- A reader accepts the copy `o` of the line `l` against the copy `kl` of its
    owner's key log (sections 6, 7.3 and 7.5). -/
    def ReaderAccepts (kl : Obj D) (l : LineId) (o : Obj D) : Prop :=
      o.id = .line l ∧ o.kind ≠ .owner ∧ o.versions ≠ [] ∧ IdentityOk E l o ∧
        KeyLogOk E l.owner kl ∧ ¬ Frozen kl ∧ SignedClean E kl l o o.versions.length

    instance (kl : Obj D) (l : LineId) (o : Obj D) : Decidable (ReaderAccepts E kl l o) := by
      unfold ReaderAccepts; infer_instance

## A signature by a current key

What a reader accepts has a head signed by the owner: a signature in its
witness folder verifies, signs the head, names a version of the owner's
key log that the reader's copy holds, with that digest, and is made with
one of the current keys of that version, which is not an ending version,
and which the copy does not expose. Nothing here depends on who served
`o` or `kl`.

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

## Back to the genesis record

Where the key comes from. Every version of a valid key log that has keys
is its first version, which is the one computed from a genesis record of
kind `owner` whose name by algorithm 0 is the owner name (section 6.2),
with the keys of that record; or a version signed by a rotation key of the
version before it (section 6.1). `Events.ownerKey_origin` (chapter 8) says
the same of the owner's keys in a world built by events; here it holds of
any valid copy, wherever it was found. Applied again to the version
before, it walks the chain back to the genesis record: whoever made a
version with keys held either the genesis record's name, which a reader
checks against the owner name, or rotation keys that the version before
committed to.

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

For what a reader accepts, the key that signs its head:

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

## A signed head vouches for its past

"A version signed directly vouches for every version it extends, byte for
byte, inventories included, whatever their own signatures" (section 7.3).
In the model, the digest of the inventory of the head describes the
object, its genesis record and all its versions: two copies whose heads
have the same number and digest, and whose head inventories do not
collide, hold the same versions and the same genesis record. Signatures
play no part in this: it is what the digest of the head that the
signature signs fixes.

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

## No host forges a version

The owner's keys, as a copy `kl` of its key log lists them, **sign one
history** `H` of the line `l`, with the genesis record `g`, when every
signature of `l` that verifies and is made with a current key of a
version that `kl` holds signs the digest of a prefix of `H`. This is the
reader's form of `SignsHistory` ([chapter 9](48-copies.md)), against a copy
of the key log instead of a world; it says that whoever holds the owner's
keys, the owner or a thief, signs nothing else.

    /-- The keys of the versions held in `kl` sign only prefixes of the history `H`
    of `l`, whose genesis record is `g`. -/
    def KeysSignHistory (kl : Obj D) (l : LineId) (g : Option (Genesis D))
        (H : List (Version D)) : Prop :=
      ∀ s, E.verifies s = true → s.line = l → s.keyLog.line = keyLogLine l.owner →
        (∃ v, kl.versionAt s.keyLog.version = some v ∧
          E.hash (kl.inventory s.keyLog.version) = s.keyLog.digest ∧
          ∃ kv, v.keys = some kv ∧ s.key ∈ kv.keys) →
        s.version ≤ H.length ∧ s.digest = E.hash (histInv l g H s.version)

Then whatever a reader accepts against `kl`, from any host, is a prefix of
`H`, with its genesis record, unless the inventory of its head collides
with that of the prefix of `H` of the same length. A host that adds a
version, changes one, or serves another genesis record makes a copy that
no reader accepts, unless the owner's keys signed it, or the digest of the
head collides. This is the formal content of "a host or a network
therefore cannot forge a version, nor add one to another owner's line"
(section 15.1).

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

And so two readers, each with its own copy of the line and of the key log,
from different hosts, agree: what one accepts is a prefix of what the
other accepts, or the converse. The copies of the key log may differ in
length; each must list keys that sign only `H`.

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

## In the story

The reader's check, computed on the story ([chapter 14](70-story.md)). A
reader who fetches the author's paper from the co-author's mirror, and the
author's key log from the co-author's archive too, accepts it. The copy
rewritten in place (that of `wTamper`, whose first version has another
source file) is refused: the digest of its head inventory is no longer the
one the author's signature signs. The thief's fourth version, signed with
the retired key `a1`, is accepted against `logA2` and refused against
`logA3`, which exposes `a1`: the reader's view of the first residual risk
of [chapter 15](72-risks.md).

    namespace OpenSheaf.Story

    example : lookup w19 "coauthor" (.line paperLine) = some (.live paper3) ∧
        lookup w19 "coauthor" (.line (keyLogLine "author")) = some (.live logA2) := ⟨rfl, rfl⟩

    example : ¬ ReaderAccepts E logA2 paperLine { paper3 with versions := [v1', v2, v3] } := by
      decide

    example : ReaderAccepts E logA2 paperLine paper4 ∧ ¬ ReaderAccepts E logA3 paperLine paper4 := by
      decide

From the acceptance, decided once, the general theorems give the rest
without computing it: a signature of the head by a current key of the
author's key log (`ReaderAccepts.signer`), and where that key comes from
(`ReaderAccepts.origin`): here, version 2 of the key log, signed by the
rotation key `a222` of the first, which is computed from the author's
genesis record.

    theorem mirror_accepted : ReaderAccepts E logA2 paperLine paper3 := by decide

    example := ReaderAccepts.signer E mirror_accepted

    example := ReaderAccepts.origin E mirror_accepted

    end OpenSheaf.Story
