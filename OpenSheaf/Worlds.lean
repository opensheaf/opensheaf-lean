-- Generated from literate/45-worlds.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Collection
import OpenSheaf.Lines

namespace OpenSheaf

variable {D : Type} [DecidableEq D] (E : Env D)

/-- The member list of a version, if any, is well formed. -/
def Version.membersOk (v : Version D) : Prop :=
  match v.members with
  | none => True
  | some c => c.WF

instance (v : Version D) : Decidable v.membersOk := by
  unfold Version.membersOk; split <;> infer_instance

/-- The identifier names a line, not a draft. -/
def ObjectId.isLine : ObjectId → Bool
  | .line _ => true
  | .draft _ => false

/-- A well-formed object stored under `oid` (sections 4, 4.2, 8.2 and 10.1). -/
structure Obj.WF (o : Obj D) (oid : ObjectId) : Prop where
  id : o.id = oid
  nonempty : o.versions ≠ []
  history : o.kind ≠ .owner → WellFormed o.versions
  kinds : ∀ v ∈ o.versions, v.members.isSome = true ↔ o.kind = .collection
  members : ∀ v ∈ o.versions, v.membersOk
  statuses : StatusOk o.versions
  genesis : o.genesis.isSome = oid.isLine

/-- At one of its hints, the pin's line has been taken down. -/
def RemovedAt (w : World D) (p : Pin D) : Prop :=
  ∃ b ∈ p.hints, resolveAt E.hash w b p = .removed

/-- The pin is found, or reports `removed`, at one of its hints. -/
abbrev Held (w : World D) (p : Pin D) : Prop :=
  Found E.hash w p ∨ RemovedAt E w p

/-- Every pin held by a version of a live object is found. -/
def PinsOk (w : World D) : Prop :=
  ∀ a oid o, lookup w a oid = some (.live o) →
    ∀ v ∈ o.versions, ∀ p ∈ v.pins, Found E.hash w p

/-- No object has been taken down. -/
def NoTombs (w : World D) : Prop := ∀ a oid n d, lookup w a oid ≠ some (.tomb n d)

/-- A well-formed world. -/
def WFWorld (w : World D) : Prop :=
  (∀ a oid o, lookup w a oid = some (.live o) → o.WF oid) ∧ PinsOk E w ∧ NoTombs w

theorem WFWorld.empty : WFWorld E (fun _ => (none : Option (Archive D))) :=
  ⟨fun _ _ _ h => by simp [lookup] at h, fun _ _ _ h => by simp [lookup] at h,
    fun _ _ _ _ h => by simp [lookup] at h⟩

/-- `o` is a copy of a prefix of a live copy of the same line, kept by another
archive (section 11.1). -/
def CopyOf (w : World D) (a : ArchiveId) (o : Obj D) : Prop :=
  ∃ b c, b ≠ a ∧ lookup w b o.id = some (.live c) ∧ c.genesis = o.genesis ∧
    ∃ t, c.versions = o.versions ++ t

/-- The new state `o` of the copy of the line `l` (not a key log) kept by
archive `a` is signed and allowed there (sections 7.5 and 11.1). -/
def LineOk (w : World D) (a : ArchiveId) (ar : Archive D) (l : LineId) (o : Obj D) : Prop :=
  ∃ kl, lookup w a (.line (keyLogLine l.owner)) = some (.live kl) ∧ KeyLogOk E l.owner kl ∧
    ¬ Frozen kl ∧ SignedClean E kl l o o.versions.length ∧
    ((l.owner ∈ ar.owners ∧ ¬ HasEnding kl) ∨ CopyOf w a o)

/-- The identity of the line `l`, whose object is `o` (sections 5, 6 and 9.1). -/
def IdentityOk (l : LineId) (o : Obj D) : Prop :=
  match o.genesis with
  | none => False
  | some g =>
    g.kind = o.kind ∧
    if o.kind = .owner then l = keyLogLine l.owner ∧ KeyLogOk E l.owner o
    else
      (l.owner = g.originator ∧ l.name = E.nameOf g 0 ∧ ∀ v ∈ o.versions, v.parent = none) ∨
      (l.owner ≠ g.originator ∧ (∃ k, k < 16 ∧ l.name = E.nameOf g k) ∧
        ∀ v ∈ o.versions, ∃ pa, v.parent = some pa ∧ pa.pin.line.owner ≠ l.owner ∧
          ∃ k, k < 16 ∧ pa.pin.line.name = E.nameOf g k)

/-- A draft has no signature files, is not an owner, and has no parent
(section 10.1). -/
def DraftOk (o : Obj D) : Prop :=
  o.sigs = [] ∧ o.kind ≠ .owner ∧ ∀ v ∈ o.versions, v.parent = none

/-- The object `o`, written under `oid` by archive `a`, is authorised. -/
def Authorised (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D) :
    Prop :=
  match oid with
  | .draft _ => DraftOk o
  | .line l => IdentityOk E l o ∧ (o.kind ≠ .owner → LineOk E w a ar l o)

/-- The branch point of `x`, after a version whose branch point is `prev`
(sections 9.1 to 9.4). -/
def BranchPointOk (w : World D) (prev : Option (Parent D)) (x : Version D) : Prop :=
  match x.parent with
  | none => prev = none
  | some pa =>
    Parent.Keeps prev pa ∨
    ((∀ pp, prev = some pp → pp.pin.line = pa.pin.line ∧ pp.pin.version < pa.pin.version ∧
        pp.documentVersion < pa.documentVersion) ∧
      ∃ b ∈ pa.pin.hints, ∃ u, resolveAt E.hash w b pa.pin = .ok u ∧
        x.files = u.files ∧ u.documentVersion = pa.documentVersion ∧
        ∀ pp, prev = some pp → ∃ u0, resolveAt E.hash w b pp.pin = .ok u0)

/-- The branch point of the version before version `i` of a history. -/
def prevParent (l : List (Version D)) (i : Nat) : Option (Parent D) :=
  match i with
  | 0 => none
  | j + 1 => (l[j]?).bind (·.parent)

theorem revise_branchPoint (w : World D) (l : List (Version D)) (fs : List (LogicalPath × D))
    (ms : Option (Members D)) (d a m : String) :
    BranchPointOk E w (headParent l) (Version.revise l fs ms d a m) := by
  unfold BranchPointOk
  cases h : headParent l with
  | none => simp [Version.revise, h]
  | some pa => simp only [Version.revise, h]; exact Or.inl (Parent.same_refl pa)

theorem describe_branchPoint (w : World D) (l : List (Version D)) (v : Version D)
    (d a m : String) : BranchPointOk E w (headParent l) (Version.describe l v d a m) := by
  unfold BranchPointOk
  cases h : headParent l with
  | none => simp [Version.describe, h]
  | some pa => simp only [Version.describe, h]; exact Or.inl (Parent.same_refl pa)

/-- Some version of a live object of the world holds a pin naming the same
object version. -/
def HeldBy (w : World D) (p : Pin D) : Prop :=
  ∃ b i c v q, lookup w b i = some (.live c) ∧ v ∈ c.versions ∧ q ∈ v.pins ∧ q.names p

/-- A pin a new version may hold: it names no key log, and it is found, or it
reports `removed` and is carried over from a version the world already holds. -/
def PinOk (w : World D) (p : Pin D) : Prop :=
  p.line ≠ keyLogLine p.line.owner ∧ (Found E.hash w p ∨ (RemovedAt E w p ∧ HeldBy w p))

theorem PinOk.held {w : World D} {p : Pin D} (h : PinOk E w p) : Held E w p :=
  h.2.elim Or.inl fun h => Or.inr h.1

omit [DecidableEq D] in
theorem heldBy_setEntry {w : World D} {a : ArchiveId} {oid : ObjectId} {e : Entry D}
    {p : Pin D} (h : HeldBy (setEntry w a oid e) p)
    (he : ∀ c, e = .live c → ∀ v ∈ c.versions, ∀ q ∈ v.pins, ¬ q.names p) : HeldBy w p := by
  obtain ⟨b, i, c, v, q, hl, hv, hq, hn⟩ := h
  cases ha : w a with
  | none =>
    have : setEntry w a oid e = w := by
      funext b'; unfold setEntry; by_cases hb : b' = a <;> simp [hb, ha]
    rw [this] at hl; exact ⟨b, i, c, v, q, hl, hv, hq, hn⟩
  | some ar =>
    rw [lookup_setEntry ha] at hl
    by_cases hbi : b = a ∧ i = oid
    · simp only [hbi, and_self, ite_true, Option.some.injEq] at hl
      exact absurd hn (he c hl v hv q hq)
    · simp only [hbi, ite_false] at hl
      exact ⟨b, i, c, v, q, hl, hv, hq, hn⟩

omit [DecidableEq D] in
theorem heldBy_newArchive {w : World D} {a : ArchiveId} {ar : Archive D} (h : w a = none)
    (hempty : ∀ x, ar.entries x = none) {p : Pin D}
    (hb : HeldBy (fun b => if b = a then some ar else w b) p) : HeldBy w p := by
  unfold HeldBy at hb ⊢
  simp only [lookup_newArchive h hempty] at hb
  exact hb

/-- The result is a version. -/
def Resolution.isOk : Resolution D → Bool
  | .ok _ => true
  | _ => false

/-- The member's single pin may be kept although `p` is the head: `p` is no
later, or no copy at the hints holds both. -/
def Member.MayKeep (w : World D) (m : Member D) (p : Pin D) : Prop :=
  match m.pins with
  | [q] => p.version ≤ q.version ∨
      ¬ ∃ b ∈ m.hints, (resolveAt E.hash w b q).isOk = true ∧ (resolveAt E.hash w b p).isOk = true
  | _ => False

/-- A followed member pins the head of its line at its hints, if any, or keeps
its pin when the head does not extend it. -/
def Member.FollowsHead (w : World D) (m : Member D) : Prop :=
  match headPin E.hash w m.hints m.line with
  | some p => m.pins = [p] ∨ m.MayKeep E w p
  | none => True

instance (w : World D) (m : Member D) (p : Pin D) : Decidable (m.MayKeep E w p) := by
  unfold Member.MayKeep; split <;> infer_instance

instance (w : World D) (m : Member D) : Decidable (m.FollowsHead E w) := by
  unfold Member.FollowsHead; split <;> infer_instance

/-- In a catalogue version, the followed members pin the heads of their lines
(section 8.3). -/
def Version.FollowsHeads (w : World D) (v : Version D) : Prop :=
  match v.members with
  | some c => c.type = .catalogue → ∀ m ∈ c.members, m.follow = true → m.FollowsHead E w
  | none => True

instance (w : World D) (v : Version D) : Decidable (v.FollowsHeads E w) := by
  unfold Version.FollowsHeads; split <;> infer_instance

/-- The last version of a history, if any, follows heads. -/
def HeadFollows (w : World D) (l : List (Version D)) : Prop :=
  match l.getLast? with
  | some x => x.FollowsHeads E w
  | none => True

instance (w : World D) (l : List (Version D)) : Decidable (HeadFollows E w l) := by
  unfold HeadFollows; split <;> infer_instance

/-- The key of `s` is a rotation key of the version of the key log `o` before the
one it signs (section 6.1). -/
def RotationKeyOk (o : Obj D) (s : Sig D) : Prop :=
  match keysAt o (s.version - 1) with
  | some pk => E.keyDigest s.key ∈ pk.next
  | none => False

instance (o : Obj D) (s : Sig D) : Decidable (RotationKeyOk E o s) := by
  unfold RotationKeyOk; split <;> infer_instance

/-- The key of `s` is a current key of the key-log version it names, in the copy
of its owner's key log that archive `a` keeps (sections 7.2 and 7.3). -/
def CurrentKeyOk (w : World D) (a : ArchiveId) (s : Sig D) : Prop :=
  match lookup w a (.line (keyLogLine s.line.owner)) with
  | some (.live kl) => ∃ kv ∈ (keyVersion E kl s.keyLog).toList, s.key ∈ kv.keys
  | _ => False

instance (w : World D) (a : ArchiveId) (s : Sig D) : Decidable (CurrentKeyOk E w a s) := by
  unfold CurrentKeyOk; split <;> infer_instance

/-- The key-log version named by `s`, a signature file of the object `o` kept by
archive `a`, allows its key (sections 6.1, 7.2 and 7.3). -/
def WitnessKeyOk (w : World D) (a : ArchiveId) (o : Obj D) (s : Sig D) : Prop :=
  if o.kind = .owner then
    2 ≤ s.version ∧ s.keyLog.line = s.line ∧ s.keyLog.version = s.version - 1 ∧
      s.keyLog.digest = E.hash (o.inventory (s.version - 1)) ∧ RotationKeyOk E o s
  else
    s.keyLog.line = keyLogLine s.line.owner ∧ CurrentKeyOk E w a s

instance (w : World D) (a : ArchiveId) (o : Obj D) (s : Sig D) :
    Decidable (WitnessKeyOk E w a o s) := by
  unfold WitnessKeyOk; infer_instance

/-- The signature file `s` of the object `o`, added by archive `a`, is valid. -/
def SigOk (w : World D) (a : ArchiveId) (o : Obj D) (s : Sig D) : Prop :=
  E.verifies s = true ∧ o.id = .line s.line ∧ 1 ≤ s.version ∧ s.version ≤ o.versions.length ∧
    s.digest = E.hash (o.inventory s.version) ∧ WitnessKeyOk E w a o s

instance (w : World D) (a : ArchiveId) (o : Obj D) (s : Sig D) : Decidable (SigOk E w a o s) := by
  unfold SigOk; infer_instance

/-- The valid steps: the model's reading of what the specification allows. -/
inductive ValidStep : World D → World D → Prop
  | newArchive (w : World D) (a : ArchiveId) (ar : Archive D) (h : w a = none)
      (hempty : ∀ x, ar.entries x = none) :
      ValidStep w (fun b => if b = a then some ar else w b)
  | create (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
      (ha : w a = some ar) (ho : ar.entries oid = none) (hwf : o.WF oid)
      (hpins : ∀ v ∈ o.versions, ∀ p ∈ v.pins, PinOk E w p)
      (hbranch : ¬ CopyOf w a o → ∀ i (h : i < o.versions.length),
        BranchPointOk E w (prevParent o.versions i) o.versions[i])
      (hfollow : ¬ CopyOf w a o → HeadFollows E w o.versions)
      (hauth : Authorised E w a ar oid o) (hsigs : ∀ s ∈ o.sigs, SigOk E w a o s) :
      ValidStep w (setEntry w a oid (.live o))
  | append (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
      (x : Version D) (ss : List (Sig D)) (ha : w a = some ar)
      (ho : ar.entries oid = some (.live o))
      (hf : o.kind ≠ .owner → Extends o.versions x) (hst : NoReinstatement o.versions x)
      (hk : x.members.isSome = true ↔ o.kind = .collection) (hm : x.membersOk)
      (hpins : ∀ p ∈ x.pins, PinOk E w p)
      (hbranch : ¬ CopyOf w a (o.append x ss) →
        BranchPointOk E w (o.versions.getLast?.bind (·.parent)) x)
      (hfollow : ¬ CopyOf w a (o.append x ss) →
        x.documentVersion = docCount o.versions + 1 → x.FollowsHeads E w)
      (hauth : Authorised E w a ar oid (o.append x ss))
      (hsigs : ∀ s ∈ ss, SigOk E w a (o.append x ss) s) :
      ValidStep w (setEntry w a oid (.live (o.append x ss)))
  | witness (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
      (ss : List (Sig D)) (ha : w a = some ar) (ho : ar.entries oid = some (.live o))
      (hss : ∀ s ∈ ss, SigOk E w a o s) :
      ValidStep w (setEntry w a oid (.live { o with sigs := o.sigs ++ ss }))

/-- Any number of valid steps. -/
abbrev ValidSteps : World D → World D → Prop := Star (ValidStep E)

theorem ValidStep.toStep {w w' : World D} (h : ValidStep E w w') : Step w w' := by
  cases h with
  | newArchive a ar h _ => exact .newArchive w a ar h
  | create a ar oid o ha ho => exact .create w a ar oid o ha ho
  | append a ar oid o x ss ha ho => exact .append w a ar oid o x ss ha ho
  | witness a ar oid o ss ha ho => exact .witness w a ar oid o ss ha ho

theorem ValidSteps.toSteps {w w' : World D} (h : ValidSteps E w w') : Steps w w' :=
  h.mono (·.toStep E)

/-- `o'` is `o`, possibly with more versions and more signature files. -/
structure Grows (o o' : Obj D) : Prop where
  id : o'.id = o.id
  kind : o'.kind = o.kind
  genesis : o'.genesis = o.genesis
  versions : ∃ t, o'.versions = o.versions ++ t
  sigs : ∀ s ∈ o.sigs, s ∈ o'.sigs

omit [DecidableEq D] in
theorem Grows.refl (o : Obj D) : Grows o o := ⟨rfl, rfl, rfl, ⟨[], by simp⟩, fun _ h => h⟩

omit [DecidableEq D] in
theorem Grows.trans {o o' o'' : Obj D} (h1 : Grows o o') (h2 : Grows o' o'') : Grows o o'' := by
  obtain ⟨t1, ht1⟩ := h1.versions
  obtain ⟨t2, ht2⟩ := h2.versions
  exact ⟨h2.id.trans h1.id, h2.kind.trans h1.kind, h2.genesis.trans h1.genesis,
    ⟨t1 ++ t2, by rw [ht2, ht1, List.append_assoc]⟩, fun s hs => h2.sigs s (h1.sigs s hs)⟩

omit [DecidableEq D] in
theorem Grows.append (o : Obj D) (x : Version D) (ss : List (Sig D)) :
    Grows o (o.append x ss) :=
  ⟨rfl, rfl, rfl, ⟨[x], rfl⟩, fun _ h => List.mem_append_left _ h⟩

omit [DecidableEq D] in
theorem Grows.witness (o : Obj D) (ss : List (Sig D)) :
    Grows o { o with sigs := o.sigs ++ ss } :=
  ⟨rfl, rfl, rfl, ⟨[], by simp⟩, fun _ h => List.mem_append_left _ h⟩

omit [DecidableEq D] in
theorem Step.lookup_cases {w w' : World D} (hs : Step w w') (b : ArchiveId) (x : ObjectId) :
    lookup w' b x = lookup w b x ∨ lookup w b x = none ∨
    (∃ o o', lookup w b x = some (.live o) ∧ lookup w' b x = some (.live o') ∧ Grows o o') := by
  cases hs with
  | newArchive a ar ha =>
    by_cases hb : b = a
    · subst hb; exact Or.inr (Or.inl (by simp [lookup, ha]))
    · exact Or.inl (by simp [lookup, hb])
  | create a ar oid o ha ho =>
    rw [lookup_setEntry ha]
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr (Or.inl (by simp [lookup, ha, ho]))
    · exact Or.inl rfl
  | append a ar oid o v ss ha ho =>
    rw [lookup_setEntry ha]
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr (Or.inr ⟨o, _, by simp [lookup, ha, ho], rfl, Grows.append o v ss⟩)
    · exact Or.inl rfl
  | witness a ar oid o ss ha ho =>
    rw [lookup_setEntry ha]
    split
    · rename_i h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr (Or.inr ⟨o, _, by simp [lookup, ha, ho], rfl, Grows.witness o ss⟩)
    · exact Or.inl rfl

/-- What a valid step did to a live entry after it. -/
theorem ValidStep.live_cases {w w' : World D} (hs : ValidStep E w w') {b : ArchiveId}
    {x : ObjectId} {o' : Obj D} (h : lookup w' b x = some (.live o')) :
    lookup w b x = some (.live o') ∨
    (∃ ar, w b = some ar ∧ Authorised E w b ar x o' ∧
      ((lookup w b x = none ∧ ∀ v ∈ o'.versions, ∀ p ∈ v.pins, PinOk E w p) ∨
        ∃ o y ss, lookup w b x = some (.live o) ∧ o' = o.append y ss ∧
          ∀ p ∈ y.pins, PinOk E w p)) ∨
    ∃ o ss, lookup w b x = some (.live o) ∧ o' = { o with sigs := o.sigs ++ ss } ∧
      ∀ s ∈ ss, SigOk E w b o s := by
  cases hs with
  | newArchive a ar ha hempty =>
    rw [lookup_newArchive ha hempty] at h; exact Or.inl h
  | create a ar oid o ha ho _ hpins _ _ hauth =>
    rw [lookup_setEntry ha] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h
      exact Or.inr (Or.inl ⟨ar, ha, hauth, Or.inl ⟨by simp [lookup, ha, ho], hpins⟩⟩)
    · exact Or.inl h
  | append a ar oid o y ss ha ho _ _ _ _ hpins _ _ hauth =>
    rw [lookup_setEntry ha] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h
      exact Or.inr (Or.inl ⟨ar, ha, hauth,
        Or.inr ⟨o, y, ss, by simp [lookup, ha, ho], rfl, hpins⟩⟩)
    · exact Or.inl h
  | witness a ar oid o ss ha ho hss =>
    rw [lookup_setEntry ha] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h
      exact Or.inr (Or.inr ⟨o, ss, by simp [lookup, ha, ho], rfl, hss⟩)
    · exact Or.inl h

omit [DecidableEq D] in
/-- **A tombstone stays.** -/
theorem Step.tomb_stays {w w' : World D} (hs : Step w w') {b : ArchiveId} {x : ObjectId}
    {n : Nat} {d : D} (h : lookup w b x = some (.tomb n d)) :
    lookup w' b x = some (.tomb n d) := by
  rcases hs.lookup_cases b x with h1 | h1 | ⟨o, _, h1, _⟩
  · rw [h1, h]
  · rw [h] at h1; cases h1
  · rw [h] at h1; cases h1

omit [DecidableEq D] in
theorem Steps.tomb_stays {w w' : World D} (hs : Steps w w') {b : ArchiveId} {x : ObjectId}
    {n : Nat} {d : D} (h : lookup w b x = some (.tomb n d)) :
    lookup w' b x = some (.tomb n d) :=
  hs.invariant (fun w => lookup w b x = some (.tomb n d)) (·.tomb_stays) h

omit [DecidableEq D] in
/-- **Objects only grow.** -/
theorem Step.live_grows {w w' : World D} (hs : Step w w') {b : ArchiveId} {x : ObjectId}
    {o : Obj D} (h : lookup w b x = some (.live o)) :
    ∃ o', lookup w' b x = some (.live o') ∧ Grows o o' := by
  rcases hs.lookup_cases b x with h1 | h1 | ⟨o1, o', h1, h2, hg⟩
  · exact ⟨o, by rw [h1, h], Grows.refl o⟩
  · rw [h] at h1; cases h1
  · rw [h] at h1; cases h1; exact ⟨o', h2, hg⟩

omit [DecidableEq D] in
theorem Steps.live_grows {w w' : World D} (hs : Steps w w') {b : ArchiveId} {x : ObjectId}
    {o : Obj D} (h : lookup w b x = some (.live o)) :
    ∃ o', lookup w' b x = some (.live o') ∧ Grows o o' := by
  refine hs.invariant (fun w => ∃ o', lookup w b x = some (.live o') ∧ Grows o o') ?_
    ⟨o, h, Grows.refl o⟩
  rintro _ _ hstep ⟨o1, h1, hg1⟩
  obtain ⟨o2, h2, hg2⟩ := hstep.live_grows h1
  exact ⟨o2, h2, hg1.trans hg2⟩

theorem WF_witness {o : Obj D} {oid : ObjectId} (h : o.WF oid) (ss : List (Sig D)) :
    ({ o with sigs := o.sigs ++ ss } : Obj D).WF oid :=
  ⟨h.id, h.nonempty, h.history, h.kinds, h.members, h.statuses, h.genesis⟩

theorem ValidStep.entry {w w' : World D} (hs : ValidStep E w w')
    (hobj : ∀ a oid o, lookup w a oid = some (.live o) → o.WF oid)
    {Q : Pin D → Prop} (hq : ∀ a oid o, lookup w a oid = some (.live o) →
      ∀ v ∈ o.versions, ∀ p ∈ v.pins, Q p)
    {b : ArchiveId} {x : ObjectId} {o' : Obj D} (h : lookup w' b x = some (.live o')) :
    o'.WF x ∧ ∀ v ∈ o'.versions, ∀ p ∈ v.pins, Q p ∨ Held E w p := by
  cases hs with
  | newArchive a ar ha hempty =>
    rw [lookup_newArchive ha hempty] at h
    exact ⟨hobj _ _ _ h, fun v hv p hp => Or.inl (hq _ _ _ h v hv p hp)⟩
  | create a ar oid o ha ho hwf hpins =>
    rw [lookup_setEntry ha] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h
      exact ⟨hwf, fun v hv p hp => Or.inr ((hpins v hv p hp).held E)⟩
    · exact ⟨hobj _ _ _ h, fun v hv p hp => Or.inl (hq _ _ _ h v hv p hp)⟩
  | append a ar oid o y ss ha ho hf hst hk hm hpins =>
    rw [lookup_setEntry ha] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h
      have hl : lookup w b x = some (.live o) := by simp [lookup, ha, ho]
      have hwf := hobj _ _ _ hl
      refine ⟨⟨hwf.id, by simp [Obj.append], fun hko => (hwf.history hko).snoc (hf hko), ?_, ?_,
        hwf.statuses.snoc hst, hwf.genesis⟩, ?_⟩
      · simpa [Obj.append, or_imp, forall_and] using ⟨hwf.kinds, hk⟩
      · simpa [Obj.append, or_imp, forall_and] using ⟨hwf.members, hm⟩
      · simpa [Obj.append, or_imp, forall_and] using
          ⟨fun v hv p hp => Or.inl (hq _ _ _ hl v hv p hp),
            fun p hp => Or.inr ((hpins p hp).held E)⟩
    · exact ⟨hobj _ _ _ h, fun v hv p hp => Or.inl (hq _ _ _ h v hv p hp)⟩
  | witness a ar oid o ss ha ho =>
    rw [lookup_setEntry ha] at h
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases h
      have hl : lookup w b x = some (.live o) := by simp [lookup, ha, ho]
      exact ⟨WF_witness (hobj _ _ _ hl) ss, fun v hv p hp => Or.inl (hq _ _ _ hl v hv p hp)⟩
    · exact ⟨hobj _ _ _ h, fun v hv p hp => Or.inl (hq _ _ _ h v hv p hp)⟩

theorem ValidStep.noTombs {w w' : World D} (hs : ValidStep E w w') (h : NoTombs w) :
    NoTombs w' := by
  intro b x n d hl
  have := (hs.toStep E).lookup_cases b x
  rcases this with h1 | h1 | ⟨o, o', _, h2, _⟩
  · rw [h1] at hl; exact h _ _ _ _ hl
  · cases hs with
    | newArchive a ar ha hempty =>
      rw [lookup_newArchive ha hempty] at hl; exact h _ _ _ _ hl
    | create a ar oid o ha =>
      rw [lookup_setEntry ha] at hl
      split at hl
      · cases hl
      · exact h _ _ _ _ hl
    | append a ar oid o y ss ha =>
      rw [lookup_setEntry ha] at hl
      split at hl
      · cases hl
      · exact h _ _ _ _ hl
    | witness a ar oid o ss ha =>
      rw [lookup_setEntry ha] at hl
      split at hl
      · cases hl
      · exact h _ _ _ _ hl
  · rw [h2] at hl; cases hl

theorem Step.removedAt {w w' : World D} (hs : Step w w') {p : Pin D}
    (h : RemovedAt E w p) : RemovedAt E w' p := by
  obtain ⟨b, hb, hr⟩ := h
  obtain ⟨n, d, hl⟩ := (resolveAt_removed_iff E.hash).mp hr
  exact ⟨b, hb, (resolveAt_removed_iff E.hash).mpr ⟨n, d, hs.tomb_stays hl⟩⟩

theorem Step.held {w w' : World D} (hs : Step w w') {p : Pin D} (h : Held E w p) :
    Held E w' p :=
  h.elim (fun hf => Or.inl (hs.found E.hash hf)) (fun hr => Or.inr (hs.removedAt E hr))

/-- **Valid steps keep worlds well formed.** -/
theorem ValidStep.wf {w w' : World D} (hs : ValidStep E w w') (hw : WFWorld E w) :
    WFWorld E w' :=
  ⟨fun _ _ _ h => (hs.entry E hw.1 hw.2.1 h).1,
   fun _ _ _ h v hv p hp => by
     rcases (hs.entry E hw.1 hw.2.1 h).2 v hv p hp with hf | hf | ⟨b, _, hr⟩
     · exact (hs.toStep E).found E.hash hf
     · exact (hs.toStep E).found E.hash hf
     · obtain ⟨n, d, hl⟩ := (resolveAt_removed_iff E.hash).mp hr
       exact absurd hl (hw.2.2 _ _ _ _),
   hs.noTombs E hw.2.2⟩

theorem ValidSteps.wf {w w' : World D} (hs : ValidSteps E w w') (hw : WFWorld E w) :
    WFWorld E w' :=
  hs.invariant _ (·.wf E) hw

/-- **Nothing dangles.** -/
theorem ValidSteps.pins_ok {w : World D}
    (hs : ValidSteps E (fun _ => (none : Option (Archive D))) w) : PinsOk E w :=
  (hs.wf E (WFWorld.empty E)).2.1

/-- **Every member is pinned.** -/
theorem ValidSteps.members_pinned {w : World D}
    (hs : ValidSteps E (fun _ => (none : Option (Archive D))) w)
    {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
    {v : Version D} (hv : v ∈ o.versions) {c : Members D} (hc : v.members = some c)
    {m : Member D} (hm : m ∈ c.members) :
    m.pins ≠ [] ∧ ∀ p ∈ m.pins, Found E.hash w p := by
  have hw := hs.wf E (WFWorld.empty E)
  have hmo := (hw.1 _ _ _ hl).members v hv
  unfold Version.membersOk at hmo
  rw [hc] at hmo
  refine ⟨(hmo m hm).2.1, fun p hp => hw.2.1 _ _ _ hl v hv p ?_⟩
  simp only [Version.pins, Version.memberPins, hc, Members.pins]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨m, hm, hp⟩))

/-- A valid step, or a takedown (section 13.2). -/
inductive Event : World D → World D → Prop
  | step {w w' : World D} : ValidStep E w w' → Event w w'
  | takedown (w : World D) (a : ArchiveId) (l : LineId) (o : Obj D)
      (hk : l ≠ keyLogLine l.owner) (hl : lookup w a (.line l) = some (.live o)) :
      Event w (takedown E.hash w a (.line l) o)

/-- Any number of events. -/
abbrev Events : World D → World D → Prop := Star (Event E)

/-- Every pin held is found, or reports `removed`. -/
def PinsHeld (w : World D) : Prop :=
  ∀ a oid o, lookup w a oid = some (.live o) →
    ∀ v ∈ o.versions, ∀ p ∈ v.pins, Held E w p

/-- A sound world: well-formed objects, and pins held are found or report
removed. -/
def SoundWorld (w : World D) : Prop :=
  (∀ a oid o, lookup w a oid = some (.live o) → o.WF oid) ∧ PinsHeld E w

theorem SoundWorld.empty : SoundWorld E (fun _ => (none : Option (Archive D))) :=
  ⟨(WFWorld.empty E).1, fun _ _ _ h => by simp [lookup] at h⟩

theorem ValidStep.sound {w w' : World D} (hs : ValidStep E w w') (hw : SoundWorld E w) :
    SoundWorld E w' :=
  ⟨fun _ _ _ h => (hs.entry E hw.1 hw.2 h).1,
   fun _ _ _ h v hv p hp => by
     rcases (hs.entry E hw.1 hw.2 h).2 v hv p hp with hh | hh
     · exact (hs.toStep E).held E hh
     · exact (hs.toStep E).held E hh⟩

theorem takedown_held {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) {p : Pin D} (h : Held E w p) :
    Held E (takedown E.hash w a oid o) p := by
  have key : ∀ b ∈ p.hints, (∃ t, resolveAt E.hash w b p = .ok t) ∨
      resolveAt E.hash w b p = .removed →
      Held E (takedown E.hash w a oid o) p := by
    intro b hb hr
    by_cases hc : b = a ∧ ObjectId.line p.line = oid
    · obtain ⟨rfl, hc⟩ := hc
      exact Or.inr ⟨b, hb, takedown_removed E.hash hl hc⟩
    · rw [← takedown_other E.hash hl hc] at hr
      rcases hr with ⟨t, ht⟩ | hr
      · exact Or.inl ⟨b, hb, t, ht⟩
      · exact Or.inr ⟨b, hb, hr⟩
  rcases h with ⟨b, hb, t, ht⟩ | ⟨b, hb, hr⟩
  · exact key b hb (Or.inl ⟨t, ht⟩)
  · exact key b hb (Or.inr hr)

theorem takedown_sound {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) (hw : SoundWorld E w) :
    SoundWorld E (takedown E.hash w a oid o) :=
  ⟨fun _ _ _ h => hw.1 _ _ _ (lookup_takedown E.hash hl h).2,
   fun _ _ _ h v hv p hp =>
     takedown_held E hl (hw.2 _ _ _ (lookup_takedown E.hash hl h).2 v hv p hp)⟩

theorem Event.sound {w w' : World D} (he : Event E w w') (hw : SoundWorld E w) :
    SoundWorld E w' := by
  cases he with
  | step hs => exact hs.sound E hw
  | takedown a oid o _ hl => exact takedown_sound E hl hw

/-- **Only a takedown stops a pin from being found, and then it reports
removed.** In a world built by events from nothing, every pin held by any
version is found, or reports `removed`, at one of its hints. -/
theorem Events.sound {w : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w) : SoundWorld E w :=
  hs.invariant _ (·.sound E) (SoundWorld.empty E)

theorem Event.tomb_stays {w w' : World D} (he : Event E w w') {b : ArchiveId}
    {x : ObjectId} {n : Nat} {d : D} (h : lookup w b x = some (.tomb n d)) :
    lookup w' b x = some (.tomb n d) := by
  cases he with
  | step hs => exact (hs.toStep E).tomb_stays h
  | takedown a oid o _ hl =>
    rw [lookup_takedown_eq E.hash hl, if_no (by rintro ⟨rfl, rfl⟩; simp [hl] at h)]
    exact h

theorem Events.tomb_stays {w w' : World D} (hs : Events E w w') {b : ArchiveId}
    {x : ObjectId} {n : Nat} {d : D} (h : lookup w b x = some (.tomb n d)) :
    lookup w' b x = some (.tomb n d) :=
  hs.invariant (fun w => lookup w b x = some (.tomb n d)) (·.tomb_stays E) h

end OpenSheaf
