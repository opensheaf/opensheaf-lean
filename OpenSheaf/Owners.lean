-- Generated from literate/35-owners.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Archive

namespace OpenSheaf

variable {D : Type} [DecidableEq D] (E : Env D)

omit [DecidableEq D] in
/-- The distinct keys of a list. -/
def distinct : List Key → List Key
  | [] => []
  | k :: ks => if k ∈ distinct ks then distinct ks else k :: distinct ks

omit [DecidableEq D] in
theorem mem_distinct {k : Key} {ks : List Key} : k ∈ distinct ks ↔ k ∈ ks := by
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
theorem distinct_nodup (ks : List Key) : (distinct ks).Nodup := by
  induction ks with
  | nil => simp [distinct]
  | cons j ks ih =>
    simp only [distinct]
    split
    · exact ih
    · rename_i h; exact List.nodup_cons.mpr ⟨h, ih⟩

omit [DecidableEq D] in
theorem length_le_of_sub {l m : List Key} (hl : l.Nodup) (h : ∀ k ∈ l, k ∈ m) :
    l.length ≤ (distinct m).length := by
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

omit [DecidableEq D] in
/-- The first version of a key log, computed from the owner's genesis record
(section 6.1). -/
def firstKeyVersion (g : Genesis D) : Version D :=
  { documentVersion := 0, files := [], description := "", keys := g.keys,
    depositor := "", message := "" }

/-- The pin of version `n` of the key log `o` of `X`. -/
def keyPin (X : OwnerName) (o : Obj D) (n : Nat) : Pin D :=
  ⟨keyLogLine X, n, E.hash (o.inventory n), []⟩

/-- Version `n + 1` of the key log `o` of `X` is signed by `nextThreshold`
rotation keys of version `n`, whose keys are `pk` (section 6.1). -/
def RotationSigned (X : OwnerName) (o : Obj D) (n : Nat) (pk : Keys D) : Prop :=
  pk.ended = false ∧ pk.nextThreshold ≤
    (signers E (keyLogLine X) (n + 1) (E.hash (o.inventory (n + 1))) (keyPin E X o n)
      (fun s => decide (E.keyDigest s.key ∈ pk.next)) o.sigs).length

instance (X : OwnerName) (o : Obj D) (n : Nat) (pk : Keys D) :
    Decidable (RotationSigned E X o n pk) := by
  unfold RotationSigned; infer_instance

omit [DecidableEq D] in
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
    decide (pk.nextThreshold ≤ (signers E (keyLogLine X) c.version c.digest
      ⟨keyLogLine X, n, d, []⟩ (fun s => decide (E.keyDigest s.key ∈ pk.next)) c.sigs).length) &&
    decide (KeysOk E (prevs ++ [pk]) c.keys) && decide (c.keys.successor ≠ some X) &&
    decide (c.digest = E.hash ⟨.line (keyLogLine X), gen, base ++ [c.toVersion]⟩) &&
    carriedChain X gen (prevs ++ [pk]) (base ++ [c.toVersion]) c.version c.digest c.keys cs

omit [DecidableEq D] in
/-- A version of an owner object: no document version, no member list, no
references, no parent, active (sections 4.1 and 4.3). -/
def Version.Plain (x : Version D) : Prop :=
  x.documentVersion = 0 ∧ x.members = none ∧ x.refs = [] ∧ x.parent = none ∧ x.status = .active

omit [DecidableEq D] in
instance (x : Version D) : Decidable x.Plain := by unfold Version.Plain; infer_instance

/-- The keys of the versions of a history that have them. -/
def keysOf (l : List (Version D)) : List (Keys D) := l.filterMap (·.keys)

/-- The keys of version `n` of `o`, if it has them. -/
def keysAt (o : Obj D) (n : Nat) : Option (Keys D) :=
  (o.versionAt n).bind (·.keys)

/-- The fork record `x`, appended after the `j` versions of the key log `o` of
`X`, is valid (section 6.3). -/
def ForkRecordOk (X : OwnerName) (o : Obj D) (j : Nat) (x : Version D) : Prop :=
  x.files = [] ∧ x.description = "" ∧ x.Plain ∧
  match x.carried with
  | [] => False
  | c :: cs =>
    2 ≤ c.version ∧ c.version ≤ j ∧ c.digest ≠ E.hash (o.inventory c.version) ∧
    match keysAt o (c.version - 1) with
    | none => False
    | some pk => carriedChain E X o.genesis (keysOf (o.versions.take (c.version - 2)))
        (o.versions.take (c.version - 1)) (c.version - 1)
        (E.hash (o.inventory (c.version - 1))) pk (c :: cs) = true

instance (X : OwnerName) (o : Obj D) (j : Nat) (x : Version D) :
    Decidable (ForkRecordOk E X o j x) := by
  unfold ForkRecordOk
  have : Decidable (match x.carried with
    | [] => False
    | c :: cs =>
      2 ≤ c.version ∧ c.version ≤ j ∧ c.digest ≠ E.hash (o.inventory c.version) ∧
      match keysAt o (c.version - 1) with
      | none => False
      | some pk => carriedChain E X o.genesis (keysOf (o.versions.take (c.version - 2)))
          (o.versions.take (c.version - 1)) (c.version - 1)
          (E.hash (o.inventory (c.version - 1))) pk (c :: cs) = true) := by
    split
    · infer_instance
    · split <;> infer_instance
  infer_instance

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

theorem KeyLogOk.parts {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) :
    ∃ g k1, o.genesis = some g ∧ o.id = .line (keyLogLine X) ∧ o.kind = .owner ∧
      g.kind = .owner ∧ E.nameOf g 0 = X ∧ g.keys = some k1 ∧ KeysOk E [] k1 ∧
      k1.ended = false ∧ o.versions.head? = some (firstKeyVersion g) ∧
      ∀ i (h : i < o.versions.length - 1),
        KeyStep E X o (i + 1) (o.versions[i]'(by omega)) (o.versions[i + 1]'(by omega)) := by
  unfold KeyLogOk at h
  split at h
  · contradiction
  · rename_i g hg
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    split at h5
    · contradiction
    · rename_i k1 hk1
      exact ⟨g, k1, hg, h1, h2, h3, h4, hk1, h5.1, h5.2, h6, h7⟩

theorem KeyLogOk.keysOk_at {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) {i : Nat}
    (hi : i < o.versions.length) {k : Keys D} (hk : (o.versions[i]'hi).keys = some k) :
    KeysOk E (keysOf (o.versions.take i)) k := by
  obtain ⟨g, k1, _, _, _, _, _, hg1, hok1, _, hhead, hsteps⟩ := h.parts
  cases i with
  | zero =>
    have h0 : o.versions[0]'hi = firstKeyVersion g := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hi] at hhead
      exact Option.some.inj hhead
    rw [h0] at hk
    simp only [firstKeyVersion] at hk
    rw [hg1] at hk
    cases hk
    simpa [keysOf] using hok1
  | succ i =>
    have hs := hsteps i (by omega)
    unfold KeyStep at hs
    split at hs
    · rename_i pk k' _ hx
      rw [hk] at hx; cases hx
      exact hs.2.1
    · rename_i _ hx
      rw [hk] at hx; cases hx
    · exact hs.elim

theorem KeyLogOk.first {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) :
    ∃ g k1, o.genesis = some g ∧ g.keys = some k1 ∧ k1.ended = false ∧
      o.versionAt 1 = some (firstKeyVersion g) := by
  obtain ⟨g, k1, hg, _, _, _, _, hg1, _, hend, hhead, _⟩ := h.parts
  refine ⟨g, k1, hg, hg1, hend, ?_⟩
  simp only [Obj.versionAt, show (1 : Nat) ≠ 0 by omega, ite_false, Nat.sub_self]
  rw [← List.head?_eq_getElem?]; exact hhead

/-- The genesis records `g` and `g'` do not collide under algorithm 0. -/
def NamesNoCollision (g g' : Genesis D) : Prop := E.nameOf g 0 = E.nameOf g' 0 → g = g'

/-- **A key log never forks at its first version.** -/
theorem no_fork_at_first {X : OwnerName} {o o' : Obj D} (h : KeyLogOk E X o)
    (h' : KeyLogOk E X o')
    (hcol : ∀ g g', o.genesis = some g → o'.genesis = some g' → NamesNoCollision E g g') :
    o.versionAt 1 = o'.versionAt 1 ∧ o.inventory 1 = o'.inventory 1 := by
  obtain ⟨g, _, hg, hid, _, _, hname, _, _, _, hhead, _⟩ := h.parts
  obtain ⟨g', _, hg', hid', _, _, hname', _, _, _, hhead', _⟩ := h'.parts
  have hgg : g = g' := hcol g g' hg hg' (hname.trans hname'.symm)
  subst hgg
  have hv : o.versions.take 1 = o'.versions.take 1 := by
    rw [List.take_one, List.take_one, hhead, hhead']
  refine ⟨?_, ?_⟩
  · simp only [Obj.versionAt, show (1 : Nat) ≠ 0 by omega, ite_false, Nat.sub_self]
    rw [← List.head?_eq_getElem?, ← List.head?_eq_getElem?, hhead, hhead']
  · simp only [Obj.inventory, hid, hid', hg, hg', hv]

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

/-- **A new version of a key log needs its rotation keys.** -/
theorem extend_needs_rotation {X : OwnerName} {o : Obj D} {x : Version D}
    {ss : List (Sig D)} (h : KeyLogOk E X (o.append x ss)) (hne : o.versions ≠ [])
    {k : Keys D} (hx : x.keys = some k) :
    ∃ pk, keysAt o o.versions.length = some pk ∧ ∃ s ∈ o.sigs ++ ss,
      E.verifies s = true ∧ s.line = keyLogLine X ∧ s.version = o.versions.length + 1 ∧
      E.keyDigest s.key ∈ pk.next := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsteps⟩ := h.parts
  have hlen : 0 < o.versions.length := List.length_pos_iff.mpr hne
  have hs := hsteps (o.versions.length - 1) (by simp [Obj.append]; omega)
  have hlast := append_getElem_last (o := o) (x := x) (ss := ss)
  have hprev := append_getElem_old (o := o) (x := x) (ss := ss)
    (i := o.versions.length - 1) (by omega)
  simp only [Nat.sub_add_cancel hlen] at hs
  rw [hlast, hprev] at hs
  unfold KeyStep at hs
  split at hs
  · rename_i pk k' hpk hk'
    obtain ⟨_, _, ⟨hpe, hsig⟩, _⟩ := hs
    have hpos : 1 ≤ pk.nextThreshold := by
      have hkpk := (h.keysOk_at E (i := o.versions.length - 1) (by simp [Obj.append]; omega)
        (by rw [hprev]; exact hpk)).1
      rcases hkpk with ⟨_, _, _, h1, _⟩ | ⟨hend, _⟩
      · exact h1
      · rw [hpe] at hend; cases hend
    obtain ⟨s, hs, ⟨hl, hv, _⟩, hver, hok'⟩ := signer_of_threshold E hpos hsig
    refine ⟨pk, ?_, s, hs, hver, hl, hv, by simpa using hok'⟩
    have hn0 : o.versions.length ≠ 0 := by omega
    simp only [keysAt, Obj.versionAt, hn0, ite_false]
    rw [List.getElem?_eq_getElem (by omega)]
    exact hpk
  · rename_i hx'; rw [hx] at hx'; cases hx'
  · exact hs.elim

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
  have hpk' : ((o.append x ss).versions[o.versions.length - 1]'(by
      simp [Obj.append]; omega)).keys = some pk := by
    rw [append_getElem_old (by omega)]
    simp only [keysAt, Obj.versionAt, show o.versions.length ≠ 0 by omega, ite_false] at hpk
    rw [List.getElem?_eq_getElem (by omega)] at hpk
    exact hpk
  exact h.disjoint E (i := i) (by simp [Obj.append]; omega) _
    (by rw [append_getElem_old hi]; exact hki) hpk' hkey hd

/-- **After an ending version, only a fork record.** -/
theorem KeyLogOk.after_end {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) {i : Nat}
    (hi : i + 1 < o.versions.length) {k : Keys D}
    (hk : (o.versions[i]'(by omega)).keys = some k) (hend : k.ended = true) :
    (o.versions[i + 1]'hi).keys = none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsteps⟩ := h.parts
  have hs := hsteps i (by omega)
  unfold KeyStep at hs
  split at hs
  · rename_i pk _ hpk _
    rw [hk] at hpk; cases hpk
    rw [hs.2.2.1.1] at hend; cases hend
  · assumption
  · rename_i hpk; rw [hk] at hpk; cases hpk

/-- **A fork record is the last version.** -/
theorem KeyLogOk.fork_last {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) {i : Nat}
    (hi : i < o.versions.length) (hk : (o.versions[i]'hi).keys = none) :
    i + 1 = o.versions.length := by
  obtain ⟨g, k1, _, _, _, _, _, hg1, _, _, hhead, hsteps⟩ := h.parts
  refine Nat.le_antisymm hi (Nat.not_lt.mp fun hlt => ?_)
  have hs := hsteps i (by omega)
  unfold KeyStep at hs
  split at hs
  · rename_i hpk _; rw [hk] at hpk; cases hpk
  · rename_i hpk _; rw [hk] at hpk; cases hpk
  · exact hs

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
  obtain ⟨g, k1, _, _, _, _, _, hg1, _, _, hhead, hsteps⟩ := h.parts
  cases j with
  | zero =>
    have h0 : o.versions[0]'hj = firstKeyVersion g := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hj] at hhead
      exact Option.some.inj hhead
    rw [h0] at hk; simp [firstKeyVersion, hg1] at hk
  | succ j =>
    have hs := hsteps j (by omega)
    unfold KeyStep at hs
    split at hs
    · rename_i _ hx; rw [hk] at hx; cases hx
    · obtain ⟨_, hfr⟩ := hs
      unfold ForkRecordOk at hfr
      obtain ⟨_, _, _, hfr⟩ := hfr
      split at hfr
      · exact hfr.elim
      · rename_i c cs hcs
        obtain ⟨h2, hle, hne, hchain⟩ := hfr
        split at hchain
        · exact hchain.elim
        · rename_i pk hpk
          simp only [carriedChain, Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true'] at hchain
          obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, hpe⟩, hsig⟩, _⟩, _⟩, _⟩, _⟩ := hchain
          have hpos : 1 ≤ pk.nextThreshold := by
            have hv : (o.versionAt (c.version - 1)).isSome := by
              cases hva : o.versionAt (c.version - 1) with
              | none => simp [keysAt, hva] at hpk
              | some _ => rfl
            obtain ⟨v, hva⟩ := Option.isSome_iff_exists.mp hv
            have hb := Obj.versionAt_bounds hva
            have hvi : o.versions[c.version - 1 - 1]'(by omega) = v := by
              simp only [Obj.versionAt, show c.version - 1 ≠ 0 by omega, ite_false] at hva
              rw [List.getElem?_eq_getElem (by omega)] at hva
              exact Option.some.inj hva
            have hkv : (o.versions[c.version - 1 - 1]'(by omega)).keys = some pk := by
              rw [hvi]; simp [keysAt, hva] at hpk; exact hpk
            rcases (h.keysOk_at E _ hkv).1 with ⟨_, _, _, h1, _⟩ | ⟨hend, _⟩
            · exact h1
            · rw [hpe] at hend; cases hend
          obtain ⟨s, hs, hsg, hver, hok⟩ := signer_of_threshold E hpos hsig
          refine ⟨c, by rw [hcs]; exact List.mem_cons_self .., h2, by omega, hne, pk, hpk,
            s, hs, hver, hsg, by simpa using hok⟩
    · exact hs.elim

/-- **A held version is signed by a rotation key of the version before.** -/
theorem KeyLogOk.held_rotation {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o) {i : Nat}
    (hi : i + 1 < o.versions.length) {k : Keys D}
    (hk : (o.versions[i + 1]'hi).keys = some k) :
    ∃ pk, (o.versions[i]'(by omega)).keys = some pk ∧ ∃ s ∈ o.sigs, E.verifies s = true ∧
      s.line = keyLogLine X ∧ s.version = i + 2 ∧ s.digest = E.hash (o.inventory (i + 2)) ∧
      E.keyDigest s.key ∈ pk.next := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hsteps⟩ := h.parts
  have hs := hsteps i (by omega)
  unfold KeyStep at hs
  split at hs
  · rename_i pk k' hpk hk'
    obtain ⟨_, _, ⟨hpe, hsig⟩, _⟩ := hs
    have hpos : 1 ≤ pk.nextThreshold := by
      rcases (h.keysOk_at E (by omega) hpk).1 with ⟨_, _, _, h1, _⟩ | ⟨hend, _⟩
      · exact h1
      · rw [hpe] at hend; cases hend
    obtain ⟨s, hs, ⟨hl, hv, hd, _⟩, hver, hok⟩ := signer_of_threshold E hpos hsig
    exact ⟨pk, hpk, s, hs, hver, hl, hv, hd, by simpa using hok⟩
  · rename_i _ hx; rw [hk] at hx; cases hx
  · exact hs.elim

/-- **Current keys cannot fork a key log.** -/
theorem current_keys_cannot_fork {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o)
    {j : Nat} (hj : j < o.versions.length) (hk : (o.versions[j]'hj).keys = none)
    (hcur : ∀ c ∈ (o.versions[j]'hj).carried, ∀ s ∈ c.sigs, E.verifies s = true →
      ∃ i, ∃ hi : i < o.versions.length, ∃ ki, (o.versions[i]'hi).keys = some ki ∧
        s.key ∈ ki.keys) : False := by
  obtain ⟨c, hc, h2, hle, _, pk, hpk, s, hs, hver, _, hd⟩ := h.fork_needs_rotation E hj hk
  obtain ⟨i, hi, ki, hki, hkey⟩ := hcur c hc s hs hver
  have hb : c.version - 1 - 1 < o.versions.length := by omega
  have hpk' : (o.versions[c.version - 1 - 1]'hb).keys = some pk := by
    simp only [keysAt, Obj.versionAt, show c.version - 1 ≠ 0 by omega, ite_false] at hpk
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
  unfold KeyStep at h ⊢
  cases hp : prev.keys with
  | none => rw [hp] at h; exact h
  | some pk =>
    cases hx : x.keys with
    | some k =>
      rw [hp, hx] at h
      dsimp only at h ⊢
      obtain ⟨h1, h2, ⟨h3, h4⟩, h5⟩ := h
      refine ⟨h1, by rw [hv]; exact h2, ⟨h3, ?_⟩, h5⟩
      unfold keyPin; rw [hinv, hinv]
      exact Nat.le_trans h4 (signers_length_mono E (fun _ h => h) hs)
    | none =>
      rw [hp, hx] at h
      dsimp only at h ⊢
      obtain ⟨h1, h2⟩ := h
      refine ⟨by rw [hv]; exact h1, ?_⟩
      unfold ForkRecordOk keysAt at h2 ⊢
      simpa only [hinv, hva, hv, hg] using h2

theorem KeyLogOk.more_sigs {X : OwnerName} {o o' : Obj D} (hid : o'.id = o.id)
    (hk : o'.kind = o.kind) (hg : o'.genesis = o.genesis) (hv : o'.versions = o.versions)
    (hs : ∀ s ∈ o.sigs, s ∈ o'.sigs) (h : KeyLogOk E X o) : KeyLogOk E X o' := by
  obtain ⟨g, k1, hg1, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h.parts
  unfold KeyLogOk
  rw [hg, hg1]
  refine ⟨hid ▸ h1, hk ▸ h2, h3, h4, ?_, by rw [hv]; exact h8, fun i hi => ?_⟩
  · rw [h5]; exact ⟨h6, h7⟩
  · have hi' : i < o.versions.length - 1 := by rw [← hv]; exact hi
    have := (h9 i hi').more_sigs E hid hg hv hs
    simp only [hv]
    exact this

theorem KeyLogOk.witness {X : OwnerName} {o : Obj D} (h : KeyLogOk E X o)
    (ss : List (Sig D)) : KeyLogOk E X { o with sigs := o.sigs ++ ss } :=
  KeyLogOk.more_sigs E (o := o) (o' := { o with sigs := o.sigs ++ ss }) rfl rfl rfl rfl
    (fun _ hs => List.mem_append_left ss hs) h

end OpenSheaf
