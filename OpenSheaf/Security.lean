-- Generated from literate/66-security.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Impossible

namespace OpenSheaf

variable {D : Type} [DecidableEq D] (E : Env D)

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

theorem KeyStep.prev_congr {X : OwnerName} {o : Obj D} {j : Nat} {prev prev' x : Version D}
    (hp : prev'.keys = prev.keys) (h : KeyStep E X o j prev x) : KeyStep E X o j prev' x := by
  unfold KeyStep at h ⊢; rw [hp]; exact h

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

omit [DecidableEq D] in
theorem Frozen.prefix {kl kl' : Obj D} (ht : ∃ t, kl'.versions = kl.versions ++ t)
    (h : Frozen kl) : Frozen kl' := by
  obtain ⟨t, ht⟩ := ht
  obtain ⟨v, hv, hk⟩ := h
  exact ⟨v, by rw [ht]; exact List.mem_append_left _ hv, hk⟩

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

theorem IdentityOk.owner_line {l : LineId} {o : Obj D} (h : IdentityOk E l o)
    (hk : o.kind = .owner) : l = keyLogLine l.owner := by
  unfold IdentityOk at h
  split at h
  · exact h.elim
  · rw [if_yes hk] at h; exact h.2.1

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

omit [DecidableEq D] in
/-- **An owner's key is a current key of a version held.** -/
theorem OwnerKey.held {w : World D} {X : OwnerName} {s : Sig D} (h : OwnerKey E w X s) :
    ∃ b kl, lookup w b (.line (keyLogLine X)) = some (.live kl) ∧
      ∃ v ∈ kl.versions, ∃ kv, v.keys = some kv ∧ kv.ended = false ∧ s.key ∈ kv.keys := by
  obtain ⟨_, b, kl, hkl, v, hv, _, kv, hkv, hend, hkey⟩ := h
  exact ⟨b, kl, hkl, v, versionAt_mem hv, kv, hkv, hend, hkey⟩

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

/-- `kl'` is a longer copy of the key log `kl`. -/
structure LongerCopy (kl kl' : Obj D) : Prop where
  id : kl'.id = kl.id
  genesis : kl'.genesis = kl.genesis
  versions : ∃ t, kl'.versions = kl.versions ++ t

theorem keyVersion_same {kl kl' : Obj D} (hid : kl'.id = kl.id)
    (hg : kl'.genesis = kl.genesis) (hv : kl'.versions = kl.versions) (p : Pin D) :
    keyVersion E kl' p = keyVersion E kl p := by
  simp only [keyVersion, carriedOf, Obj.versionAt, Obj.inventory, hid, hg, hv]; rfl

omit [DecidableEq D] in
theorem exposed_same {kl kl' : Obj D} (hv : kl'.versions = kl.versions) :
    exposedIn kl' = exposedIn kl ∧ forkPoint kl' = forkPoint kl := by
  simp only [exposedIn, forkPoint, carriedOf, hv]; exact ⟨trivial, trivial⟩

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

/-- **Signatures stay good** against a longer copy of the key log. -/
theorem SignedWith.longer {X : OwnerName} {kl kl' : Obj D} (h : KeyLogOk E X kl)
    (h' : KeyLogOk E X kl') (hlc : LongerCopy kl kl') {l : LineId} {n : Nat} {d : D}
    {sigs : List (Sig D)} {ok : Sig D → Bool} (hs : SignedWith E kl l n d sigs ok) :
    SignedWith E kl' l n d sigs ok := by
  obtain ⟨s, hs, hl, kv, hkv, hend, hpos, hc⟩ := hs
  refine ⟨s, hs, hl, kv, ?_, hend, hpos, hc⟩
  rw [keyVersion_longer E h h' hlc (Option.mem_toList.mp hkv)]
  simp

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

end OpenSheaf
