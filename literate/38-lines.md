# Lines and signatures

"A line is its signed versions, wherever they are stored" (section 7).
Every sealed version of a line is signed by its owner, with at least
`threshold` distinct current keys of one version of the owner's key log
(section 7.1); a version signed directly vouches for every version it
extends (section 7.3); and a signed version is **contested** when it needs
a key that the owner's key log exposes, or names a version of the key log
from a fork point on (section 7.3). This chapter defines these statuses,
against a copy of the owner's key log, and proves what they rest on:

- a signed version has a signature that verifies, by a current key of a
  version of the key log that is not an ending version
  (`SignedWith.signer`): "it has no keys, so nothing is signed against it"
  (section 6.3);
- a rotation key never signs a line, since no rotation key of a valid key
  log is among its current keys (`KeyLogOk.disjoint`, in the previous
  chapter);
- more signature files, or a weaker test on them, keep a version signed
  (`SignedWith.mono`). What a longer copy of the key log, with more
  exposures, does to a status is not proved here.

    -- in OpenSheaf/Lines.lean:
    import OpenSheaf.Owners

    namespace OpenSheaf

    variable {D : Type} [DecidableEq D] (E : Env D)

## The key-log version a signature names

A signature names a version of its owner's key log by a pin, and "is
judged against the key-log version it names alone" (section 7.1). The
reader reaches that version in its copy of the key log, with that digest,
"also as carried by a fork record" (section 7.3). The model looks among the
versions the copy holds, then among those its fork records carry.

    /-- The versions carried by the fork records of a key log. -/
    def carriedOf (kl : Obj D) : List (Carried D) := kl.versions.flatMap (·.carried)

    /-- The keys of the key-log version that `p` names, in the copy `kl` of the key
    log: held, with that digest, or carried by a fork record (section 7.3). -/
    def keyVersion (kl : Obj D) (p : Pin D) : Option (Keys D) :=
      match kl.versionAt p.version with
      | some v =>
        if E.hash (kl.inventory p.version) = p.digest then v.keys
        else ((carriedOf kl).find? fun c => c.version == p.version && c.digest == p.digest).map (·.keys)
      | none =>
        ((carriedOf kl).find? fun c => c.version == p.version && c.digest == p.digest).map (·.keys)

The key-log version reached depends only on the number and the digest of
the pin, not on its hints.

    theorem keyVersion_congr {kl : Obj D} {p q : Pin D} (hv : p.version = q.version)
        (hd : p.digest = q.digest) : keyVersion E kl p = keyVersion E kl q := by
      unfold keyVersion; rw [hv, hd]

## Exposed keys and fork points

"An exposure counts in any version of the key log, on either side of a
fork ..., in a version a fork record carries included" (section 6.3). The fork
point of a copy of a key log is the number of the first version its fork
record carries (section 6.3).

    /-- The keys a copy of a key log exposes, on either side of a fork. -/
    def exposedIn (kl : Obj D) : List Key :=
      kl.versions.flatMap (fun v => (v.keys.map (·.exposed)).getD []) ++
        (carriedOf kl).flatMap (·.keys.exposed)

    /-- The fork point of a copy of a key log, if it has a fork record. -/
    def forkPoint (kl : Obj D) : Option Nat := (carriedOf kl).head?.map (·.version)

A signature file is **tainted** when it counts against a version: it was
made with an exposed key, or names a version of the key log from the fork
point on (section 7.3). Other evidence that the reader trusts (a timestamp)
may date such a signature before the exposure or the fork; the model has
no time, and leaves that evidence out.

    /-- The signature `s` is made with a key that `kl` exposes, or names a version
    of `kl` from its fork point on (section 7.3). -/
    def tainted (kl : Obj D) (s : Sig D) : Bool :=
      decide (s.key ∈ exposedIn kl) || (forkPoint kl).any (· ≤ s.keyLog.version)

## Signed versions

A version is **signed directly** "by at least `threshold` distinct current
keys of one key-log version, `threshold` being that version's, with good
signature files naming that version" (section 7.3). A signature file is
good when it verifies, signs the version, with the digest of its
inventory, and its key is one of the `keys` of the key-log version it
names, which the reader reaches. The model asks, besides, that the
key-log version named be the owner's, and that it not be an ending
version, which has no keys.

`SignedWith` counts only the signature files that pass a test `ok`: all of
them, for a signed version; those that are not tainted, for a version that
is signed and not contested.

    /-- Version `n` of line `l`, whose inventory has digest `d`, is signed directly
    by the signature files `sigs` that pass `ok`, against the copy `kl` of its
    owner's key log (sections 7.1 and 7.3). -/
    def SignedWith (kl : Obj D) (l : LineId) (n : Nat) (d : D) (sigs : List (Sig D))
        (ok : Sig D → Bool) : Prop :=
      ∃ s ∈ sigs, s.keyLog.line = keyLogLine l.owner ∧ ∃ kv ∈ (keyVersion E kl s.keyLog).toList,
        kv.ended = false ∧ 1 ≤ kv.threshold ∧
        kv.threshold ≤ (signers E l n d s.keyLog (fun t => decide (t.key ∈ kv.keys) && ok t) sigs).length

    instance (kl : Obj D) (l : LineId) (n : Nat) (d : D) (sigs : List (Sig D))
        (ok : Sig D → Bool) : Decidable (SignedWith E kl l n d sigs ok) := by
      unfold SignedWith; infer_instance

Two readings of it, for version `n` of a copy `o` of a line, against the
copy `kl` of the owner's key log:

    /-- Version `n` of the copy `o` of `l` is signed directly (section 7.3). -/
    def SignedDirect (kl : Obj D) (l : LineId) (o : Obj D) (n : Nat) : Prop :=
      SignedWith E kl l n (E.hash (o.inventory n)) o.sigs fun _ => true

    /-- Version `n` of the copy `o` of `l` is signed directly without tainted
    signatures: signed and, unless vouched for otherwise, not contested
    (section 7.3). -/
    def SignedClean (kl : Obj D) (l : LineId) (o : Obj D) (n : Nat) : Prop :=
      SignedWith E kl l n (E.hash (o.inventory n)) o.sigs fun s => !tainted kl s

    instance (kl : Obj D) (l : LineId) (o : Obj D) (n : Nat) :
        Decidable (SignedDirect E kl l o n) := by unfold SignedDirect; infer_instance

    instance (kl : Obj D) (l : LineId) (o : Obj D) (n : Nat) :
        Decidable (SignedClean E kl l o n) := by unfold SignedClean; infer_instance

A version is **signed** when it is signed directly or "vouched for, when a
later version of the same line signed directly extends it"; it is
**contested** when it "would not be signed if these good signature files
of its owner, its own or those of the versions that vouch for it, were left
out": those that are tainted (section 7.3). So a version is signed and not
contested exactly when some version at or after it is signed directly
without tainted signatures.

    /-- Version `n` of the copy `o` of `l` is signed: it or a later version is
    signed directly (section 7.3). -/
    def Signed (kl : Obj D) (l : LineId) (o : Obj D) (n : Nat) : Prop :=
      1 ≤ n ∧ ∃ m, n ≤ m ∧ m ≤ o.versions.length ∧ SignedDirect E kl l o m

    /-- Version `n` of the copy `o` of `l` is signed and not contested. -/
    def SignedNotContested (kl : Obj D) (l : LineId) (o : Obj D) (n : Nat) : Prop :=
      1 ≤ n ∧ ∃ m, n ≤ m ∧ m ≤ o.versions.length ∧ SignedClean E kl l o m

    /-- Version `n` of the copy `o` of `l` is contested (section 7.3). -/
    def Contested (kl : Obj D) (l : LineId) (o : Obj D) (n : Nat) : Prop :=
      Signed E kl l o n ∧ ¬ SignedNotContested E kl l o n

A reader decides these statuses by computation: the versions at or after
`n` are finitely many.

    theorem signed_iff (kl : Obj D) (l : LineId) (o : Obj D) (n : Nat) :
        Signed E kl l o n ↔ 1 ≤ n ∧ ∃ m ∈ List.range (o.versions.length + 1),
          n ≤ m ∧ SignedDirect E kl l o m := by
      unfold Signed
      constructor
      · rintro ⟨h1, m, h2, h3, h4⟩
        exact ⟨h1, m, List.mem_range.mpr (Nat.lt_succ_of_le h3), h2, h4⟩
      · rintro ⟨h1, m, hm, h2, h4⟩
        exact ⟨h1, m, h2, Nat.le_of_lt_succ (List.mem_range.mp hm), h4⟩

    theorem signedNotContested_iff (kl : Obj D) (l : LineId) (o : Obj D) (n : Nat) :
        SignedNotContested E kl l o n ↔ 1 ≤ n ∧ ∃ m ∈ List.range (o.versions.length + 1),
          n ≤ m ∧ SignedClean E kl l o m := by
      unfold SignedNotContested
      constructor
      · rintro ⟨h1, m, h2, h3, h4⟩
        exact ⟨h1, m, List.mem_range.mpr (Nat.lt_succ_of_le h3), h2, h4⟩
      · rintro ⟨h1, m, hm, h2, h4⟩
        exact ⟨h1, m, h2, Nat.le_of_lt_succ (List.mem_range.mp hm), h4⟩

    instance (kl : Obj D) (l : LineId) (o : Obj D) (n : Nat) : Decidable (Signed E kl l o n) :=
      decidable_of_iff _ (signed_iff E kl l o n).symm

    instance (kl : Obj D) (l : LineId) (o : Obj D) (n : Nat) :
        Decidable (SignedNotContested E kl l o n) :=
      decidable_of_iff _ (signedNotContested_iff E kl l o n).symm

    instance (kl : Obj D) (l : LineId) (o : Obj D) (n : Nat) : Decidable (Contested E kl l o n) := by
      unfold Contested; infer_instance

The valid steps of [chapter 7](45-worlds.md) ask only for `SignedClean` of
the head, against a copy of the key log without a fork record: an archive
that knows of a fork adds nothing to the owner's lines (section 7.5), so
the half of `tainted` that looks at the fork point never matters to them.
It matters to readers: in the story ([chapter 13](70-story.md)), the
archive that holds the fork record of the author's key log reads the
versions of the paper signed against a key-log version from the fork point
on as contested, and the version signed before it as signed and not
contested.

## What a signature rests on

Counting fewer signatures, or with a stronger test, never makes a version
signed: a signed version stays signed when signatures are added, and a
version signed without tainted signatures is signed.

    /-- **More signatures, or a weaker test, keep a version signed.** -/
    theorem SignedWith.mono {kl : Obj D} {l : LineId} {n : Nat} {d : D}
        {sigs sigs' : List (Sig D)} {ok ok' : Sig D → Bool}
        (h : SignedWith E kl l n d sigs ok) (hok : ∀ s, ok s = true → ok' s = true)
        (hsub : ∀ s ∈ sigs, s ∈ sigs') : SignedWith E kl l n d sigs' ok' := by
      obtain ⟨s, hs, hl, kv, hkv, hend, hpos, hc⟩ := h
      refine ⟨s, hsub s hs, hl, kv, hkv, hend, hpos, Nat.le_trans hc ?_⟩
      apply signers_length_mono E _ hsub
      intro t ht
      simp only [Bool.and_eq_true] at ht ⊢
      exact ⟨ht.1, hok t ht.2⟩

    theorem SignedClean.signedDirect {kl : Obj D} {l : LineId} {o : Obj D} {n : Nat}
        (h : SignedClean E kl l o n) : SignedDirect E kl l o n :=
      SignedWith.mono E h (fun _ _ => rfl) (fun _ hs => hs)

    theorem SignedNotContested.signed {kl : Obj D} {l : LineId} {o : Obj D} {n : Nat}
        (h : SignedNotContested E kl l o n) : Signed E kl l o n := by
      obtain ⟨h1, m, hnm, hm, hc⟩ := h
      exact ⟨h1, m, hnm, hm, hc.signedDirect E⟩

A version signed directly has a signature that verifies, signs it, names a
version of the owner's key log that is not an ending version, and is made
with one of that version's current keys. Nothing can be signed against an
ending version, nor with a key that is not current.

    /-- **A signed version has a good signature by a current key.** -/
    theorem SignedWith.signer {kl : Obj D} {l : LineId} {n : Nat} {d : D}
        {sigs : List (Sig D)} {ok : Sig D → Bool} (h : SignedWith E kl l n d sigs ok) :
        ∃ s ∈ sigs, E.verifies s = true ∧ s.Signs l n d s.keyLog ∧ ok s = true ∧
          s.keyLog.line = keyLogLine l.owner ∧
          ∃ kv, keyVersion E kl s.keyLog = some kv ∧ kv.ended = false ∧ s.key ∈ kv.keys := by
      obtain ⟨s0, _, hl, kv, hkv, hend, hpos, hc⟩ := h
      obtain ⟨s, hs, hsg, hver, hok⟩ := signer_of_threshold E hpos hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hsg
      refine ⟨s, hs, hver, ⟨h0, h1, h2, rfl, rfl, rfl⟩, hok.2, h3.trans hl, kv, ?_, hend, hok.1⟩
      rw [keyVersion_congr E h4 h5]; exact Option.mem_toList.mp hkv

A signature not tainted is made with a key that is not exposed: so a
version signed and not contested does not need an exposed key.

    omit [DecidableEq D] in
    theorem not_tainted_not_exposed {kl : Obj D} {s : Sig D} (h : (!tainted kl s) = true) :
        s.key ∉ exposedIn kl := by
      simp only [tainted, Bool.not_or, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not] at h
      exact h.1

## Frozen and ended owners

An owner is **ended** "when its key log has an ending version or a fork
record" (section 6.3); a fork **freezes** it: an archive that knows of the
fork "adds no version of that owner's other lines, from a copy or as a
deposit" (section 7.5).

    /-- The copy `kl` of a key log has an ending version. -/
    def HasEnding (kl : Obj D) : Prop := ∃ v ∈ kl.versions, ∃ k, v.keys = some k ∧ k.ended = true

    instance (kl : Obj D) : Decidable (HasEnding kl) := by
      unfold HasEnding; infer_instance

    /-- The copy `kl` of a key log has a fork record, and freezes its owner. -/
    def Frozen (kl : Obj D) : Prop := ∃ v ∈ kl.versions, v.keys = none

    instance (kl : Obj D) : Decidable (Frozen kl) := by
      unfold Frozen; infer_instance

A copy of a valid key log without a fork record carries nothing: every
version with keys carries nothing. So a key-log version that a signature
reaches in it is a version the copy holds, with the digest of the pin.

    theorem KeyLogOk.carried_nil {X : OwnerName} {kl : Obj D} (h : KeyLogOk E X kl)
        (hf : ¬ Frozen kl) : carriedOf kl = [] := by
      obtain ⟨g, _, hp⟩ := h.parts
      unfold carriedOf
      rw [List.flatMap_eq_nil_iff]
      intro v hv
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
      cases i with
      | zero => rw [hp.getElem_zero E hi]; rfl
      | succ i =>
        cases hx : (kl.versions[i + 1]'hi).keys with
        | none => exact absurd ⟨_, List.getElem_mem hi, hx⟩ hf
        | some k =>
          obtain ⟨_, _, hc, _⟩ := (hp.steps i (by omega)).keyed E hx
          exact hc

    theorem keyVersion_held {kl : Obj D} (hc : carriedOf kl = []) {p : Pin D} {kv : Keys D}
        (h : keyVersion E kl p = some kv) :
        ∃ v, kl.versionAt p.version = some v ∧ E.hash (kl.inventory p.version) = p.digest ∧
          v.keys = some kv := by
      unfold keyVersion at h
      rw [hc] at h
      split at h
      · rename_i v hv
        split at h
        · rename_i hd; exact ⟨v, hv, hd, h⟩
        · simp at h
      · simp at h

    end OpenSheaf
