-- Generated from literate/35-owners.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Archive

namespace OpenSheaf

variable {D : Type} [DecidableEq D] (E : Env D)

/-- The distinct elements of a list. -/
def distinct {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | k :: ks => if k ∈ distinct ks then distinct ks else k :: distinct ks

omit [DecidableEq D] in
theorem mem_distinct {α : Type} [DecidableEq α] {k : α} {ks : List α} :
    k ∈ distinct ks ↔ k ∈ ks := by
  induction ks with
  | nil => simp [distinct]
  | cons j ks ih =>
    simp only [distinct]
    split
    · rename_i h
      rw [ih]
      constructor
      · exact List.mem_cons_of_mem _
      · intro hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact ih.mp h
        · exact hk
    · simp [ih]

/-- The signature file `s` signs version `n` of line `l`, whose inventory has
digest `d`, against the key-log version `kl`. -/
def Sig.Signs (s : Sig D) (l : LineId) (n : Nat) (d : D) (kl : Pin D) : Prop :=
  s.line = l ∧ s.version = n ∧ s.digest = d ∧
    s.keyLog.line = kl.line ∧ s.keyLog.version = kl.version ∧ s.keyLog.digest = kl.digest

instance (s : Sig D) (l : LineId) (n : Nat) (d : D) (kl : Pin D) :
    Decidable (s.Signs l n d kl) := by
  unfold Sig.Signs; infer_instance

/-- The distinct keys of the signature files of `sigs` that sign version `n` of
`l` with digest `d` against `kl`, verify, and pass `ok`. -/
def signers (l : LineId) (n : Nat) (d : D) (kl : Pin D) (ok : Sig D → Bool)
    (sigs : List (Sig D)) : List Key :=
  distinct ((sigs.filter fun s => decide (s.Signs l n d kl) && E.verifies s && ok s).map
    (·.key))

theorem mem_signers {l : LineId} {n : Nat} {d : D} {kl : Pin D} {ok : Sig D → Bool}
    {sigs : List (Sig D)} {k : Key} (h : k ∈ signers E l n d kl ok sigs) :
    ∃ s ∈ sigs, s.key = k ∧ s.Signs l n d kl ∧ E.verifies s = true ∧ ok s = true := by
  unfold signers at h
  rw [mem_distinct] at h
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
  obtain ⟨hs, hc⟩ := List.mem_filter.mp hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact ⟨s, hs, rfl, hc.1.1, hc.1.2, hc.2⟩

theorem signer_of_threshold {l : LineId} {n : Nat} {d : D} {kl : Pin D}
    {ok : Sig D → Bool} {sigs : List (Sig D)} {t : Nat} (ht : 1 ≤ t)
    (h : t ≤ (signers E l n d kl ok sigs).length) :
    ∃ s ∈ sigs, s.Signs l n d kl ∧ E.verifies s = true ∧ ok s = true := by
  cases hs : signers E l n d kl ok sigs with
  | nil => rw [hs] at h; simp at h; omega
  | cons k _ =>
    obtain ⟨s, hs', _, h1, h2, h3⟩ := mem_signers E (k := k) (by rw [hs]; simp)
    exact ⟨s, hs', h1, h2, h3⟩

theorem signers_mono {l : LineId} {n : Nat} {d : D} {kl : Pin D}
    {ok ok' : Sig D → Bool} {sigs sigs' : List (Sig D)}
    (hok : ∀ s, ok s = true → ok' s = true) (hsub : ∀ s ∈ sigs, s ∈ sigs')
    {k : Key} (h : k ∈ signers E l n d kl ok sigs) : k ∈ signers E l n d kl ok' sigs' := by
  obtain ⟨s, hs, rfl, h1, h2, h3⟩ := mem_signers E h
  unfold signers
  rw [mem_distinct]
  refine List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hsub s hs, ?_⟩, rfl⟩
  simp [h1, h2, hok s h3]

omit [DecidableEq D] in
theorem distinct_nodup {α : Type} [DecidableEq α] (ks : List α) : (distinct ks).Nodup := by
  induction ks with
  | nil => simp [distinct]
  | cons j ks ih =>
    simp only [distinct]
    split
    · exact ih
    · rename_i h; exact List.nodup_cons.mpr ⟨h, ih⟩

omit [DecidableEq D] in
theorem length_le_of_sub {α : Type} [DecidableEq α] {l m : List α} (hl : l.Nodup)
    (h : ∀ k ∈ l, k ∈ m) : l.length ≤ (distinct m).length := by
  have hsub : ∀ k ∈ l, k ∈ distinct m := fun k hk => mem_distinct.mpr (h k hk)
  exact List.Nodup.length_le_of_subset hl hsub

theorem signers_length_mono {l : LineId} {n : Nat} {d : D} {kl : Pin D}
    {ok ok' : Sig D → Bool} {sigs sigs' : List (Sig D)}
    (hok : ∀ s, ok s = true → ok' s = true) (hsub : ∀ s ∈ sigs, s ∈ sigs') :
    (signers E l n d kl ok sigs).length ≤ (signers E l n d kl ok' sigs').length := by
  have hnd : (signers E l n d kl ok sigs).Nodup := by unfold signers; exact distinct_nodup _
  have h := length_le_of_sub hnd (m := (sigs'.filter fun s => decide (s.Signs l n d kl) &&
      E.verifies s && ok' s).map (·.key)) (fun k hk => by
    have := signers_mono E hok hsub hk
    unfold signers at this
    exact mem_distinct.mp this)
  unfold signers
  exact h

/-- The distinct digests, among those that `next` of `pk` commits to, of the
keys of the signature files of `sigs` that sign version `n` of `l` with digest
`d` against `kl` and verify (section 6.1). -/
def rotationSigners (l : LineId) (n : Nat) (d : D) (kl : Pin D) (pk : Keys D)
    (sigs : List (Sig D)) : List D :=
  distinct ((signers E l n d kl (fun s => decide (E.keyDigest s.key ∈ pk.next)) sigs).map
    E.keyDigest)

theorem rotation_signer {l : LineId} {n : Nat} {d : D} {kl : Pin D} {pk : Keys D}
    {sigs : List (Sig D)} {t : Nat} (ht : 1 ≤ t)
    (h : t ≤ (rotationSigners E l n d kl pk sigs).length) :
    ∃ s ∈ sigs, s.Signs l n d kl ∧ E.verifies s = true ∧ E.keyDigest s.key ∈ pk.next := by
  cases hs : rotationSigners E l n d kl pk sigs with
  | nil => rw [hs] at h; simp at h; omega
  | cons x _ =>
    have hx : x ∈ rotationSigners E l n d kl pk sigs := by rw [hs]; simp
    unfold rotationSigners at hx
    rw [mem_distinct] at hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    obtain ⟨s, hs', rfl, h1, h2, h3⟩ := mem_signers E hk
    exact ⟨s, hs', h1, h2, by simpa using h3⟩

theorem rotationSigners_length_mono {l : LineId} {n : Nat} {d : D} {kl : Pin D} {pk : Keys D}
    {sigs sigs' : List (Sig D)} (hsub : ∀ s ∈ sigs, s ∈ sigs') :
    (rotationSigners E l n d kl pk sigs).length ≤
      (rotationSigners E l n d kl pk sigs').length := by
  unfold rotationSigners
  apply length_le_of_sub (distinct_nodup _)
  intro x hx
  rw [mem_distinct] at hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨k, signers_mono E (fun _ h => h) hsub hk, rfl⟩

/-- The shape of `keys.json`: a version with keys, or an ending version
(sections 6.1 and 6.3). -/
def Keys.Shape (k : Keys D) : Prop :=
  (k.ended = false ∧ 1 ≤ k.threshold ∧ k.threshold ≤ k.keys.length ∧
    1 ≤ k.nextThreshold ∧ k.nextThreshold ≤ k.next.length ∧ k.successor = none) ∨
  (k.ended = true ∧ k.keys = [] ∧ k.threshold = 0 ∧ k.next = [] ∧ k.nextThreshold = 0)

instance (k : Keys D) : Decidable k.Shape := by unfold Keys.Shape; infer_instance

/-- The rules of section 6.1 on `keys.json` `k`, after the versions `prev` of its
side. -/
def KeysOk (prev : List (Keys D)) (k : Keys D) : Prop :=
  k.Shape ∧ k.keys.Nodup ∧ k.next.Nodup ∧
  (∀ key ∈ k.keys, ∀ j ∈ prev ++ [k], key ∉ j.exposed ∧ E.keyDigest key ∉ j.next) ∧
  (∀ d ∈ k.next, (∀ j ∈ prev ++ [k], ∀ key ∈ j.keys, E.keyDigest key ≠ d) ∧
    ∀ j ∈ prev, d ∉ j.next) ∧
  (∀ key ∈ k.exposed, ∃ j ∈ prev, key ∈ j.keys)

instance (prev : List (Keys D)) (k : Keys D) : Decidable (KeysOk E prev k) := by
  unfold KeysOk; infer_instance

/-- The first version of a key log, computed from the owner's genesis record
(section 6.1). -/
def firstKeyVersion (g : Genesis D) : Version D :=
  { documentVersion := 0, files := [], description := "", keys := g.keys,
    depositor := "", message := "" }

/-- The pin of version `n` of the key log `o` of `X`. -/
def keyPin (X : OwnerName) (o : Obj D) (n : Nat) : Pin D :=
  ⟨keyLogLine X, n, E.hash (o.inventory n), []⟩

/-- Version `n + 1` of the key log `o` of `X` is signed by `nextThreshold`
distinct rotation keys of version `n`, whose keys are `pk`, counted by their
digests (section 6.1). -/
def RotationSigned (X : OwnerName) (o : Obj D) (n : Nat) (pk : Keys D) : Prop :=
  pk.ended = false ∧ pk.nextThreshold ≤
    (rotationSigners E (keyLogLine X) (n + 1) (E.hash (o.inventory (n + 1))) (keyPin E X o n)
      pk o.sigs).length

instance (X : OwnerName) (o : Obj D) (n : Nat) (pk : Keys D) :
    Decidable (RotationSigned E X o n pk) := by
  unfold RotationSigned; infer_instance

/-- The version a fork record carries. -/
def Carried.toVersion (c : Carried D) : Version D :=
  { documentVersion := 0, files := c.files, description := c.description, keys := some c.keys,
    status := c.status, depositor := c.depositor, message := c.message }

/-- The carried versions `cs` follow the versions `base` of the key log `X`,
whose genesis record is `gen`, the last of which is version `n`, with digest `d`
and keys `pk`, after the versions with keys `prevs` on their side: each is the
version its digest names, obeys the rules of section 6.1, and is signed by
`nextThreshold` rotation keys of the one before (section 6.3). -/
def carriedChain (X : OwnerName) (gen : Option (Genesis D)) :
    List (Keys D) → List (Version D) → Nat → D → Keys D → List (Carried D) → Bool
  | _, _, _, _, _, [] => true
  | prevs, base, n, d, pk, c :: cs =>
    decide (c.version = n + 1) && decide (c.status = .active) && !pk.ended &&
    decide (pk.nextThreshold ≤ (rotationSigners E (keyLogLine X) c.version c.digest
      ⟨keyLogLine X, n, d, []⟩ pk c.sigs).length) &&
    decide (KeysOk E (prevs ++ [pk]) c.keys) && decide (c.keys.successor ≠ some X) &&
    decide (c.digest = E.hash ⟨.line (keyLogLine X), gen, base ++ [c.toVersion]⟩) &&
    carriedChain X gen (prevs ++ [pk]) (base ++ [c.toVersion]) c.version c.digest c.keys cs

theorem carriedChain_cons {X : OwnerName} {gen : Option (Genesis D)} {prevs : List (Keys D)}
    {base : List (Version D)} {n : Nat} {d : D} {pk : Keys D} {c : Carried D}
    {cs : List (Carried D)} :
    carriedChain E X gen prevs base n d pk (c :: cs) = true ↔
      c.version = n + 1 ∧ c.status = .active ∧ pk.ended = false ∧
      pk.nextThreshold ≤ (rotationSigners E (keyLogLine X) c.version c.digest
        ⟨keyLogLine X, n, d, []⟩ pk c.sigs).length ∧
      KeysOk E (prevs ++ [pk]) c.keys ∧ c.keys.successor ≠ some X ∧
      c.digest = E.hash ⟨.line (keyLogLine X), gen, base ++ [c.toVersion]⟩ ∧
      carriedChain E X gen (prevs ++ [pk]) (base ++ [c.toVersion]) c.version c.digest c.keys cs =
        true := by
  simp only [carriedChain, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', and_assoc]

/-- A version of an owner object: no document version, no member list, no
references, no parent, active (sections 4.1 and 4.3). -/
def Version.Plain (x : Version D) : Prop :=
  x.documentVersion = 0 ∧ x.members = none ∧ x.refs = [] ∧ x.parent = none ∧ x.status = .active

instance (x : Version D) : Decidable x.Plain := by unfold Version.Plain; infer_instance

/-- The keys of the versions of a history that have them. -/
def keysOf (l : List (Version D)) : List (Keys D) := l.filterMap (·.keys)

/-- The keys of version `n` of `o`, if it has them. -/
def keysAt (o : Obj D) (n : Nat) : Option (Keys D) :=
  (o.versionAt n).bind (·.keys)

/-- The carried versions `c :: cs` follow the version before `c` held in the key
log `o` of `X`, which has keys (section 6.3). -/
def ForkBase (X : OwnerName) (o : Obj D) (c : Carried D) (cs : List (Carried D)) : Prop :=
  match keysAt o (c.version - 1) with
  | none => False
  | some pk => carriedChain E X o.genesis (keysOf (o.versions.take (c.version - 2)))
      (o.versions.take (c.version - 1)) (c.version - 1)
      (E.hash (o.inventory (c.version - 1))) pk (c :: cs) = true

instance (X : OwnerName) (o : Obj D) (c : Carried D) (cs : List (Carried D)) :
    Decidable (ForkBase E X o c cs) := by
  unfold ForkBase; split <;> infer_instance

/-- The versions a fork record carries, after the `j` versions of the key log `o`
of `X`: some, from a fork point after the first version and within the `j`, the
first differing from the version of its number held (section 6.3). -/
def ForkCarried (X : OwnerName) (o : Obj D) (j : Nat) : List (Carried D) → Prop
  | [] => False
  | c :: cs => 2 ≤ c.version ∧ c.version ≤ j ∧ c.digest ≠ E.hash (o.inventory c.version) ∧
      ForkBase E X o c cs

instance (X : OwnerName) (o : Obj D) (j : Nat) (cs : List (Carried D)) :
    Decidable (ForkCarried E X o j cs) := by
  cases cs <;> unfold ForkCarried <;> infer_instance

/-- The fork record `x`, appended after the `j` versions of the key log `o` of
`X`, is valid (section 6.3). -/
def ForkRecordOk (X : OwnerName) (o : Obj D) (j : Nat) (x : Version D) : Prop :=
  x.files = [] ∧ x.description = "" ∧ x.Plain ∧ ForkCarried E X o j x.carried

instance (X : OwnerName) (o : Obj D) (j : Nat) (x : Version D) :
    Decidable (ForkRecordOk E X o j x) := by
  unfold ForkRecordOk; infer_instance

/-- Version `j + 1` of the key log `o` of `X`, `x`, follows version `j`,
`prev` (sections 6.1 and 6.3). -/
def KeyStep (X : OwnerName) (o : Obj D) (j : Nat) (prev x : Version D) : Prop :=
  match prev.keys, x.keys with
  | some pk, some k =>
    x.carried = [] ∧ KeysOk E (keysOf (o.versions.take j)) k ∧ RotationSigned E X o j pk ∧
      k.successor ≠ some X ∧ x.Plain
  | some _, none => j + 1 = o.versions.length ∧ ForkRecordOk E X o j x
  | none, _ => False

instance (X : OwnerName) (o : Obj D) (j : Nat) (prev x : Version D) :
    Decidable (KeyStep E X o j prev x) := by
  unfold KeyStep; split <;> infer_instance

theorem KeyStep.keyed {X : OwnerName} {o : Obj D} {j : Nat} {prev x : Version D}
    (h : KeyStep E X o j prev x) {k : Keys D} (hk : x.keys = some k) :
    ∃ pk, prev.keys = some pk ∧ x.carried = [] ∧ KeysOk E (keysOf (o.versions.take j)) k ∧
      RotationSigned E X o j pk ∧ k.successor ≠ some X ∧ x.Plain := by
  unfold KeyStep at h
  rw [hk] at h
  cases hp : prev.keys with
  | none => rw [hp] at h; exact h.elim
  | some pk => rw [hp] at h; exact ⟨pk, rfl, h⟩

theorem KeyStep.fork {X : OwnerName} {o : Obj D} {j : Nat} {prev x : Version D}
    (h : KeyStep E X o j prev x) (hk : x.keys = none) :
    ∃ pk, prev.keys = some pk ∧ j + 1 = o.versions.length ∧ ForkRecordOk E X o j x := by
  unfold KeyStep at h
  rw [hk] at h
  cases hp : prev.keys with
  | none => rw [hp] at h; exact h.elim
  | some pk => rw [hp] at h; exact ⟨pk, rfl, h⟩

theorem KeyStep.prev_keys {X : OwnerName} {o : Obj D} {j : Nat} {prev x : Version D}
    (h : KeyStep E X o j prev x) : ∃ pk, prev.keys = some pk := by
  cases hk : x.keys with
  | none => obtain ⟨pk, hp, _⟩ := h.fork E hk; exact ⟨pk, hp⟩
  | some k => obtain ⟨pk, hp, _⟩ := h.keyed E hk; exact ⟨pk, hp⟩

theorem KeyStep.of_keyed {X : OwnerName} {o : Obj D} {j : Nat} {prev x : Version D}
    {pk k : Keys D} (hp : prev.keys = some pk) (hk : x.keys = some k)
    (h : x.carried = [] ∧ KeysOk E (keysOf (o.versions.take j)) k ∧
      RotationSigned E X o j pk ∧ k.successor ≠ some X ∧ x.Plain) :
    KeyStep E X o j prev x := by
  unfold KeyStep; rw [hp, hk]; exact h

theorem KeyStep.of_fork {X : OwnerName} {o : Obj D} {j : Nat} {prev x : Version D}
    {pk : Keys D} (hp : prev.keys = some pk) (hk : x.keys = none)
    (h : j + 1 = o.versions.length ∧ ForkRecordOk E X o j x) : KeyStep E X o j prev x := by
  unfold KeyStep; rw [hp, hk]; exact h

/-- A valid key log of the owner `X` (section 6). -/
def KeyLogOk (X : OwnerName) (o : Obj D) : Prop :=
  match o.genesis with
  | none => False
  | some g =>
    o.id = .line (keyLogLine X) ∧ o.kind = .owner ∧ g.kind = .owner ∧ E.nameOf g 0 = X ∧
    (match g.keys with
     | none => False
     | some k1 => KeysOk E [] k1 ∧ k1.ended = false) ∧
    o.versions.head? = some (firstKeyVersion g) ∧
    ∀ i (h : i < o.versions.length - 1),
      KeyStep E X o (i + 1) (o.versions[i]'(by omega)) (o.versions[i + 1]'(by omega))

instance (X : OwnerName) (o : Obj D) : Decidable (KeyLogOk E X o) := by
  unfold KeyLogOk; split
  · infer_instance
  · split <;> infer_instance

/-- The parts of a valid key log of `X`, with the genesis record `g` and its
first keys `k1`. -/
structure KeyLogOk.Parts (X : OwnerName) (o : Obj D) (g : Genesis D) (k1 : Keys D) : Prop where
  genesis : o.genesis = some g
  id : o.id = .line (keyLogLine X)
  kind : o.kind = .owner
  gkind : g.kind = .owner
  name : E.nameOf g 0 = X
  keys : g.keys = some k1
  keysOk : KeysOk E [] k1
  notEnded : k1.ended = false
  head : o.versions.head? = some (firstKeyVersion g)
  steps : ∀ i (h : i < o.versions.length - 1),
    KeyStep E X o (i + 1) (o.versions[i]'(by omega)) (o.versions[i + 1]'(by omega))

theorem KeyLogOk.parts {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) :
    ∃ g k1, KeyLogOk.Parts E X o g k1 := by
  unfold KeyLogOk at h
  split at h
  · contradiction
  · rename_i g hg
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    split at h5
    · contradiction
    · rename_i k1 hk1
      exact ⟨g, k1, ⟨hg, h1, h2, h3, h4, hk1, h5.1, h5.2, h6, h7⟩⟩

theorem KeyLogOk.Parts.getElem_zero {X : OwnerName} {o : Obj D} {g : Genesis D}
    {k1 : Keys D} (hp : KeyLogOk.Parts E X o g k1) (h0 : 0 < o.versions.length) :
    o.versions[0] = firstKeyVersion g := by
  have := hp.head
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0] at this
  exact Option.some.inj this

theorem KeyLogOk.keysOk_at {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) {i : Nat}
    (hi : i < o.versions.length) {k : Keys D} (hk : (o.versions[i]'hi).keys = some k) :
    KeysOk E (keysOf (o.versions.take i)) k := by
  obtain ⟨g, k1, hp⟩ := h.parts
  cases i with
  | zero =>
    rw [hp.getElem_zero E hi] at hk
    simp only [firstKeyVersion] at hk
    rw [hp.keys] at hk
    cases hk
    simpa [keysOf] using hp.keysOk
  | succ i =>
    obtain ⟨_, _, _, hok, _⟩ := (hp.steps i (by omega)).keyed E hk
    exact hok

theorem KeyLogOk.first {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) :
    ∃ g k1, o.genesis = some g ∧ g.keys = some k1 ∧ k1.ended = false ∧
      o.versionAt 1 = some (firstKeyVersion g) := by
  obtain ⟨g, k1, hp⟩ := h.parts
  refine ⟨g, k1, hp.genesis, hp.keys, hp.notEnded, ?_⟩
  rw [Obj.versionAt_succ, ← List.head?_eq_getElem?]; exact hp.head

/-- The genesis records `g` and `g'` do not collide under algorithm 0. -/
def NamesNoCollision (g g' : Genesis D) : Prop := E.nameOf g 0 = E.nameOf g' 0 → g = g'

/-- **A key log never forks at its first version.** -/
theorem no_fork_at_first {X : OwnerName} {o o' : Obj D} (h : KeyLogOk E X o)
    (h' : KeyLogOk E X o')
    (hcol : ∀ g g', o.genesis = some g → o'.genesis = some g' → NamesNoCollision E g g') :
    o.versionAt 1 = o'.versionAt 1 ∧ o.inventory 1 = o'.inventory 1 := by
  obtain ⟨g, _, hp⟩ := h.parts
  obtain ⟨g', _, hp'⟩ := h'.parts
  have hgg : g = g' := hcol g g' hp.genesis hp'.genesis (hp.name.trans hp'.name.symm)
  subst hgg
  have hv : o.versions.take 1 = o'.versions.take 1 := by
    rw [List.take_one, List.take_one, hp.head, hp'.head]
  refine ⟨?_, ?_⟩
  · rw [Obj.versionAt_succ, Obj.versionAt_succ, ← List.head?_eq_getElem?,
      ← List.head?_eq_getElem?, hp.head, hp'.head]
  · simp only [Obj.inventory, hp.id, hp'.id, hp.genesis, hp'.genesis, hv]

omit [DecidableEq D] in
theorem keys_mem_keysOf {l : List (Version D)} {i j : Nat} (hij : i < j) (hi : i < l.length)
    {k : Keys D} (hk : (l[i]'hi).keys = some k) : k ∈ keysOf (l.take j) := by
  unfold keysOf
  refine List.mem_filterMap.mpr ⟨l[i], ?_, hk⟩
  have : (l.take j)[i]'(by simp; omega) = l[i] := List.getElem_take ..
  rw [← this]; exact List.getElem_mem ..

/-- **No key is both a current key and a rotation key**, in any two versions of a
valid key log. -/
theorem KeyLogOk.disjoint {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) {i j : Nat}
    (hi : i < o.versions.length) (hj : j < o.versions.length) {ki kj : Keys D}
    (hki : (o.versions[i]'hi).keys = some ki) (hkj : (o.versions[j]'hj).keys = some kj)
    {key : Key} (hkey : key ∈ ki.keys) : E.keyDigest key ∉ kj.next := by
  intro hd
  by_cases hji : j ≤ i
  · have hr := (h.keysOk_at E hi hki).2.2.2.1 key hkey
    rcases Nat.lt_or_eq_of_le hji with hlt | heq
    · exact (hr kj (List.mem_append_left _ (keys_mem_keysOf hlt hj hkj))).2 hd
    · subst heq; rw [hki] at hkj; cases hkj
      exact (hr ki (List.mem_append_right _ (List.mem_singleton_self _))).2 hd
  · have hr := (h.keysOk_at E hj hkj).2.2.2.2.1 _ hd
    exact hr.1 ki (List.mem_append_left _ (keys_mem_keysOf (by omega) hi hki)) key hkey rfl

theorem KeyLogOk.rotationSigner {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) {i : Nat}
    (hi : i < o.versions.length) {pk : Keys D} (hpk : (o.versions[i]'hi).keys = some pk)
    {n : Nat} {d : D} {kl : Pin D} {sigs : List (Sig D)} (hend : pk.ended = false)
    (hsig : pk.nextThreshold ≤ (rotationSigners E (keyLogLine X) n d kl pk sigs).length) :
    ∃ s ∈ sigs, s.Signs (keyLogLine X) n d kl ∧ E.verifies s = true ∧
      E.keyDigest s.key ∈ pk.next := by
  have hpos : 1 ≤ pk.nextThreshold := by
    rcases (h.keysOk_at E hi hpk).1 with ⟨_, _, _, h1, _⟩ | ⟨he, _⟩
    · exact h1
    · rw [hend] at he; cases he
  exact rotation_signer E hpos hsig

/-- **A new version of a key log needs its rotation keys.** -/
theorem extend_needs_rotation {X : OwnerName} {o : Obj D} {x : Version D}
    {ss : List (Sig D)} (h : KeyLogOk E X (o.append x ss)) (hne : o.versions ≠ [])
    {k : Keys D} (hx : x.keys = some k) :
    ∃ pk, keysAt o o.versions.length = some pk ∧ ∃ s ∈ o.sigs ++ ss,
      E.verifies s = true ∧ s.line = keyLogLine X ∧ s.version = o.versions.length + 1 ∧
      E.keyDigest s.key ∈ pk.next := by
  obtain ⟨_, _, hp⟩ := h.parts
  have hlen : 0 < o.versions.length := List.length_pos_iff.mpr hne
  have hs := hp.steps (o.versions.length - 1) (by simp [Obj.append]; omega)
  have hlast := append_getElem_last (o := o) (x := x) (ss := ss)
  have hprev := append_getElem_old (o := o) (x := x) (ss := ss)
    (i := o.versions.length - 1) (by omega)
  simp only [Nat.sub_add_cancel hlen] at hs
  rw [hlast, hprev] at hs
  obtain ⟨pk, hpk, _, _, ⟨hpe, hsig⟩, _⟩ := hs.keyed E hx
  obtain ⟨s, hs, ⟨hl, hv, _⟩, hver, hd⟩ := h.rotationSigner E
    (i := o.versions.length - 1) (by simp [Obj.append]; omega) (by rw [hprev]; exact hpk) hpe hsig
  refine ⟨pk, ?_, s, hs, hver, hl, hv, hd⟩
  obtain ⟨m, hm⟩ : ∃ m, o.versions.length = m + 1 := ⟨o.versions.length - 1, by omega⟩
  simp only [keysAt, hm, Obj.versionAt_succ]
  rw [List.getElem?_eq_getElem (by omega)]
  simpa [hm] using hpk

/-- **Current keys cannot change a key log.** -/
theorem current_keys_cannot_extend {X : OwnerName} {o : Obj D} {x : Version D}
    {ss : List (Sig D)} (hne : o.versions ≠ []) {k : Keys D} (hx : x.keys = some k)
    (hcur : ∀ s ∈ o.sigs ++ ss, E.verifies s = true → s.line = keyLogLine X →
      s.version = o.versions.length + 1 →
      ∃ i, ∃ hi : i < o.versions.length, ∃ ki, (o.versions[i]'hi).keys = some ki ∧
        s.key ∈ ki.keys) :
    ¬ KeyLogOk E X (o.append x ss) := by
  intro h
  obtain ⟨pk, hpk, s, hs, hver, hl, hv, hd⟩ := extend_needs_rotation E h hne hx
  obtain ⟨i, hi, ki, hki, hkey⟩ := hcur s hs hver hl hv
  have hlen : 0 < o.versions.length := List.length_pos_iff.mpr hne
  obtain ⟨m, hm⟩ : ∃ m, o.versions.length = m + 1 := ⟨o.versions.length - 1, by omega⟩
  have hpk' : ((o.append x ss).versions[o.versions.length - 1]'(by
      simp [Obj.append]; omega)).keys = some pk := by
    rw [append_getElem_old (by omega)]
    simp only [keysAt, hm, Obj.versionAt_succ] at hpk
    rw [List.getElem?_eq_getElem (by omega)] at hpk
    simpa [hm] using hpk
  exact h.disjoint E (i := i) (by simp [Obj.append]; omega) _
    (by rw [append_getElem_old hi]; exact hki) hpk' hkey hd

/-- **After an ending version, only a fork record.** -/
theorem KeyLogOk.after_end {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) {i : Nat}
    (hi : i + 1 < o.versions.length) {k : Keys D}
    (hk : (o.versions[i]'(by omega)).keys = some k) (hend : k.ended = true) :
    (o.versions[i + 1]'hi).keys = none := by
  obtain ⟨_, _, hp⟩ := h.parts
  have hs := hp.steps i (by omega)
  cases hx : (o.versions[i + 1]'hi).keys with
  | none => rfl
  | some k' =>
    obtain ⟨pk, hpk, _, _, ⟨hpe, _⟩, _⟩ := hs.keyed E hx
    rw [hk] at hpk; cases hpk
    rw [hpe] at hend; cases hend

/-- **A fork record is the last version.** -/
theorem KeyLogOk.fork_last {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) {i : Nat}
    (hi : i < o.versions.length) (hk : (o.versions[i]'hi).keys = none) :
    i + 1 = o.versions.length := by
  obtain ⟨_, _, hp⟩ := h.parts
  refine Nat.le_antisymm hi (Nat.not_lt.mp fun hlt => ?_)
  obtain ⟨pk, hpk⟩ := (hp.steps i (by omega)).prev_keys E
  rw [hk] at hpk; cases hpk

/-- **A fork record carries a version signed by a rotation key of the version
before the fork point.** -/
theorem KeyLogOk.fork_needs_rotation {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o)
    {j : Nat} (hj : j < o.versions.length) (hk : (o.versions[j]'hj).keys = none) :
    ∃ c ∈ (o.versions[j]'hj).carried, 2 ≤ c.version ∧ c.version ≤ j ∧
      c.digest ≠ E.hash (o.inventory c.version) ∧
      ∃ pk, keysAt o (c.version - 1) = some pk ∧
        ∃ s ∈ c.sigs, E.verifies s = true ∧
          s.Signs (keyLogLine X) c.version c.digest (keyPin E X o (c.version - 1)) ∧
          E.keyDigest s.key ∈ pk.next := by
  obtain ⟨g, k1, hp⟩ := h.parts
  cases j with
  | zero =>
    rw [hp.getElem_zero E hj] at hk; simp [firstKeyVersion, hp.keys] at hk
  | succ j =>
    obtain ⟨_, _, _, hfr⟩ := (hp.steps j (by omega)).fork E hk
    obtain ⟨_, _, _, hfr⟩ := hfr
    cases hcs : (o.versions[j + 1]'hj).carried with
    | nil => rw [hcs] at hfr; exact hfr.elim
    | cons c cs =>
      rw [hcs] at hfr
      obtain ⟨h2, hle, hne, hbase⟩ := hfr
      unfold ForkBase at hbase
      split at hbase
      · exact hbase.elim
      · rename_i pk hpk
        obtain ⟨_, _, hpe, hsig, _⟩ := (carriedChain_cons E).mp hbase
        obtain ⟨v, hva⟩ : ∃ v, o.versionAt (c.version - 1) = some v := by
          cases hva : o.versionAt (c.version - 1) with
          | none => simp [keysAt, hva] at hpk
          | some v => exact ⟨v, rfl⟩
        have hb := Obj.versionAt_bounds hva
        obtain ⟨m, hm⟩ : ∃ m, c.version - 1 = m + 1 := ⟨c.version - 2, by omega⟩
        have hvi : o.versions[m]'(by omega) = v := by
          rw [hm, Obj.versionAt_succ, List.getElem?_eq_getElem (by omega)] at hva
          exact Option.some.inj hva
        have hkv : (o.versions[m]'(by omega)).keys = some pk := by
          rw [hvi]; simp [keysAt, hva] at hpk; exact hpk
        obtain ⟨s, hs, hsg, hver, hd⟩ := h.rotationSigner E (by omega) hkv hpe hsig
        exact ⟨c, List.mem_cons_self .., h2, by omega, hne, pk, hpk,
          s, hs, hver, hsg, hd⟩

/-- **A held version is signed by a rotation key of the version before.** -/
theorem KeyLogOk.held_rotation {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) {i : Nat}
    (hi : i + 1 < o.versions.length) {k : Keys D}
    (hk : (o.versions[i + 1]'hi).keys = some k) :
    ∃ pk, (o.versions[i]'(by omega)).keys = some pk ∧ ∃ s ∈ o.sigs, E.verifies s = true ∧
      s.line = keyLogLine X ∧ s.version = i + 2 ∧ s.digest = E.hash (o.inventory (i + 2)) ∧
      E.keyDigest s.key ∈ pk.next := by
  obtain ⟨_, _, hp⟩ := h.parts
  obtain ⟨pk, hpk, _, _, ⟨hpe, hsig⟩, _⟩ := (hp.steps i (by omega)).keyed E hk
  obtain ⟨s, hs, ⟨hl, hv, hd, _⟩, hver, hkd⟩ := h.rotationSigner E (by omega) hpk hpe hsig
  exact ⟨pk, hpk, s, hs, hver, hl, hv, hd, hkd⟩

/-- **Current keys cannot fork a key log.** -/
theorem current_keys_cannot_fork {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o)
    {j : Nat} (hj : j < o.versions.length) (hk : (o.versions[j]'hj).keys = none)
    (hcur : ∀ c ∈ (o.versions[j]'hj).carried, ∀ s ∈ c.sigs, E.verifies s = true →
      ∃ i, ∃ hi : i < o.versions.length, ∃ ki, (o.versions[i]'hi).keys = some ki ∧
        s.key ∈ ki.keys) : False := by
  obtain ⟨c, hc, h2, hle, _, pk, hpk, s, hs, hver, _, hd⟩ := h.fork_needs_rotation E hj hk
  obtain ⟨i, hi, ki, hki, hkey⟩ := hcur c hc s hs hver
  obtain ⟨m, hm⟩ : ∃ m, c.version - 1 = m + 1 := ⟨c.version - 2, by omega⟩
  have hb : m < o.versions.length := by omega
  have hpk' : (o.versions[m]'hb).keys = some pk := by
    simp only [keysAt, hm, Obj.versionAt_succ] at hpk
    rw [List.getElem?_eq_getElem hb] at hpk
    exact hpk
  exact h.disjoint E hi hb hki hpk' hkey hd

theorem KeyStep.more_sigs {X : OwnerName} {o o' : Obj D} (hid : o'.id = o.id)
    (hg : o'.genesis = o.genesis) (hv : o'.versions = o.versions)
    (hs : ∀ s ∈ o.sigs, s ∈ o'.sigs) {j : Nat} {prev x : Version D}
    (h : KeyStep E X o j prev x) : KeyStep E X o' j prev x := by
  have hinv : ∀ n, o'.inventory n = o.inventory n := fun n => by
    simp [Obj.inventory, hid, hg, hv]
  have hva : ∀ n, o'.versionAt n = o.versionAt n := fun n => by simp [Obj.versionAt, hv]
  cases hx : x.keys with
  | some k =>
    obtain ⟨pk, hp, h1, h2, ⟨h3, h4⟩, h5⟩ := h.keyed E hx
    refine KeyStep.of_keyed E hp hx ⟨h1, by rw [hv]; exact h2, ⟨h3, ?_⟩, h5⟩
    unfold keyPin; rw [hinv, hinv]
    exact Nat.le_trans h4 (rotationSigners_length_mono E hs)
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

theorem KeyLogOk.more_sigs {X : OwnerName} {o o' : Obj D} (hid : o'.id = o.id)
    (hk : o'.kind = o.kind) (hg : o'.genesis = o.genesis) (hv : o'.versions = o.versions)
    (hs : ∀ s ∈ o.sigs, s ∈ o'.sigs) (h : KeyLogOk E X o) : KeyLogOk E X o' := by
  obtain ⟨g, k1, hp⟩ := h.parts
  unfold KeyLogOk
  rw [hg, hp.genesis]
  refine ⟨hid ▸ hp.id, hk ▸ hp.kind, hp.gkind, hp.name, ?_, by rw [hv]; exact hp.head,
    fun i hi => ?_⟩
  · rw [hp.keys]; exact ⟨hp.keysOk, hp.notEnded⟩
  · have hi' : i < o.versions.length - 1 := by rw [← hv]; exact hi
    have := (hp.steps i hi').more_sigs E hid hg hv hs
    simp only [hv]
    exact this

theorem KeyLogOk.witness {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o)
    (ss : List (Sig D)) : KeyLogOk E X { o with sigs := o.sigs ++ ss } :=
  KeyLogOk.more_sigs E (o := o) (o' := { o with sigs := o.sigs ++ ss }) rfl rfl rfl rfl
    (fun _ hs => List.mem_append_left ss hs) h

end OpenSheaf
