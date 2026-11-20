-- Generated from literate/38-lines.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Owners

namespace OpenSheaf

variable {D : Type} [DecidableEq D] (E : Env D)

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

theorem keyVersion_congr {kl : Obj D} {p q : Pin D} (hv : p.version = q.version)
    (hd : p.digest = q.digest) : keyVersion E kl p = keyVersion E kl q := by
  unfold keyVersion; rw [hv, hd]

/-- The keys a copy of a key log exposes, on either side of a fork. -/
def exposedIn (kl : Obj D) : List Key :=
  kl.versions.flatMap (fun v => (v.keys.map (·.exposed)).getD []) ++
    (carriedOf kl).flatMap (·.keys.exposed)

/-- The fork point of a copy of a key log, if it has a fork record. -/
def forkPoint (kl : Obj D) : Option Nat := (carriedOf kl).head?.map (·.version)

/-- The signature `s` is made with a key that `kl` exposes, or names a version
of `kl` from its fork point on (section 7.3). -/
def tainted (kl : Obj D) (s : Sig D) : Bool :=
  decide (s.key ∈ exposedIn kl) || (forkPoint kl).any (· ≤ s.keyLog.version)

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

omit [DecidableEq D] in
theorem not_tainted_not_exposed {kl : Obj D} {s : Sig D} (h : (!tainted kl s) = true) :
    s.key ∉ exposedIn kl := by
  simp only [tainted, Bool.not_or, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  exact h.1

/-- **A rotation key never signs a line**, against a version of a valid key
log. -/
theorem rotation_key_signs_no_line {X : OwnerName} {kl : Obj D} (hkl : KeyLogOk E X kl)
    {i j : Nat} (hi : i < kl.versions.length) (hj : j < kl.versions.length)
    {ki kj : Keys D} (hki : (kl.versions[i]'hi).keys = some ki)
    (hkj : (kl.versions[j]'hj).keys = some kj) {key : Key} (hd : E.keyDigest key ∈ kj.next) :
    key ∉ ki.keys :=
  fun hk => hkl.disjoint E hi hj hki hkj hk hd

/-- The copy `kl` of a key log has an ending version. -/
def HasEnding (kl : Obj D) : Prop := ∃ v ∈ kl.versions, ∃ k, v.keys = some k ∧ k.ended = true

instance (kl : Obj D) : Decidable (HasEnding kl) := by
  unfold HasEnding; infer_instance

/-- The copy `kl` of a key log has a fork record, and freezes its owner. -/
def Frozen (kl : Obj D) : Prop := ∃ v ∈ kl.versions, v.keys = none

instance (kl : Obj D) : Decidable (Frozen kl) := by
  unfold Frozen; infer_instance

theorem KeyLogOk.carried_nil {X : OwnerName} {kl : Obj D} (h : KeyLogOk E X kl)
    (hf : ¬ Frozen kl) : carriedOf kl = [] := by
  obtain ⟨g, _, _, _, _, _, _, _, _, _, hhead, hsteps⟩ := h.parts
  unfold carriedOf
  rw [List.flatMap_eq_nil_iff]
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
  cases i with
  | zero =>
    have h0 : kl.versions[0]'hi = firstKeyVersion g := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hi] at hhead
      exact Option.some.inj hhead
    rw [h0]; rfl
  | succ i =>
    have hs := hsteps i (by omega)
    unfold KeyStep at hs
    split at hs
    · exact hs.1
    · rename_i hx
      exact absurd ⟨_, List.getElem_mem hi, hx⟩ hf
    · exact hs.elim

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
