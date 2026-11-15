-- Generated from literate/49-acts.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Worlds

namespace OpenSheaf

variable {D : Type} [DecidableEq D] (hash : Hash D)

omit [DecidableEq D] in
/-- The writers of archive `a`. -/
def writersOf (w : World D) (a : ArchiveId) : Option (List Agent) :=
  (w a).map (·.writers)

omit [DecidableEq D] in
theorem writersOf_setEntry (w : World D) (a : ArchiveId) (oid : ObjectId) (e : Entry D)
    (c : ArchiveId) : writersOf (setEntry w a oid e) c = writersOf w c := by
  unfold writersOf setEntry
  by_cases hc : c = a
  · subst hc; cases w c <;> simp
  · simp [hc]

/-- A valid step made by the agent `u`. -/
inductive StepBy (u : Agent) : World D → World D → Prop
  | newArchive (w : World D) (a : ArchiveId) (ar : Archive D) (h : w a = none)
      (hempty : ∀ x, ar.entries x = none) (hu : u ∈ ar.writers) :
      StepBy u w (fun b => if b = a then some ar else w b)
  | create (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
      (ha : w a = some ar) (ho : ar.entries oid = none) (hwf : o.WF oid)
      (hpins : ∀ v ∈ o.versions, ∀ p ∈ v.pins, PinOk hash w p)
      (hhome : o.archive = a ∨ MirrorOf w o) (hu : u ∈ ar.writers)
      (hdep : o.archive = a → ∀ v ∈ o.versions, v.depositor ∈ ar.writers)
      (hfollow : o.archive = a → HeadFollows hash w o.versions)
      (hsrc : ∀ v ∈ o.versions, SourceOk hash w v) :
      StepBy u w (setEntry w a oid (.live o))
  | append (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
      (x : Version D) (ha : w a = some ar) (ho : ar.entries oid = some (.live o))
      (hf : Extends o.versions x) (hst : NoReinstatement o.versions x)
      (hk : x.members.isSome = true ↔ o.kind = .collection) (hm : x.membersOk)
      (hpins : ∀ p ∈ x.pins, PinOk hash w p)
      (hhome : o.archive = a ∨ MirrorOf w (o.append x)) (hu : u ∈ ar.writers)
      (hdep : o.archive = a → x.depositor = u)
      (hfollow : o.archive = a → x.FollowsHeads hash w)
      (hsrc : SourceOk hash w x) :
      StepBy u w (setEntry w a oid (.live (o.append x)))

/-- A step or a takedown, made by the agent `u`. -/
inductive Act (u : Agent) : World D → World D → Prop
  | step {w w' : World D} : StepBy hash u w w' → Act u w w'
  | takedown (w : World D) (a : ArchiveId) (ar : Archive D) (oid : ObjectId) (o : Obj D)
      (ha : w a = some ar) (hl : lookup w a oid = some (.live o)) (hu : u ∈ ar.writers) :
      Act u w (takedown hash w a oid o)

/-- An act of some agent. -/
def AnyAct (w w' : World D) : Prop := ∃ u, Act hash u w w'

/-- Acts, by any agents. -/
abbrev Acts : World D → World D → Prop := Star (AnyAct hash)

theorem StepBy.toValidStep {u : Agent} {w w' : World D} (h : StepBy hash u w w') :
    ValidStep hash w w' := by
  cases h with
  | newArchive a ar h hempty _ => exact .newArchive w a ar h hempty
  | create a ar oid o ha ho hwf hpins hhome _ _ hfo hsrc =>
    exact .create w a ar oid o ha ho hwf hpins hhome hfo hsrc
  | append a ar oid o x ha ho hf hst hk hm hpins hhome _ _ hfo hsrc =>
    exact .append w a ar oid o x ha ho hf hst hk hm hpins hhome hfo hsrc

theorem Act.toEvent {u : Agent} {w w' : World D} (h : Act hash u w w') : Event hash w w' := by
  cases h with
  | step hs => exact .step hs.toValidStep
  | takedown a ar oid o _ hl _ => exact .takedown w a oid o hl

theorem Acts.toEvents {w w' : World D} (h : Acts hash w w') : Events hash w w' :=
  h.mono fun ⟨_, ha⟩ => ha.toEvent

/-- **An outsider changes nothing.** -/
theorem Act.outsider {u : Agent} {w w' : World D} (h : Act hash u w w') {a : ArchiveId}
    (hout : ∀ ar, w a = some ar → u ∉ ar.writers) (x : ObjectId) :
    lookup w' a x = lookup w a x := by
  cases h with
  | step hs =>
    cases hs with
    | newArchive b ar hb hempty _ =>
      rw [lookup_newArchive hb hempty]
    | create b ar oid o hb _ _ _ _ hu _ =>
      rw [lookup_setEntry hb]
      split
      · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; exact absurd hu (hout ar hb)
      · rfl
    | append b ar oid o y hb _ _ _ _ _ _ _ hu _ =>
      rw [lookup_setEntry hb]
      split
      · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; exact absurd hu (hout ar hb)
      · rfl
  | takedown b ar oid o hb hl hu =>
    rw [lookup_takedown_eq hash hl]
    split
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; exact absurd hu (hout ar hb)
    · rfl

/-- Every version was deposited by a writer of its object's own archive. -/
def DepositorsOk (w : World D) : Prop :=
  ∀ b x o, lookup w b x = some (.live o) →
    ∃ ws, writersOf w o.archive = some ws ∧ ∀ v ∈ o.versions, v.depositor ∈ ws

theorem StepBy.depositors {u : Agent} {w w' : World D} (h : StepBy hash u w w')
    (hw : DepositorsOk w) : DepositorsOk w' := by
  intro b x o' hl
  cases h with
  | newArchive a ar ha hempty _ =>
    rw [lookup_newArchive ha hempty] at hl
    obtain ⟨ws, hws, hdep⟩ := hw b x o' hl
    have hna : o'.archive ≠ a := by
      intro he; rw [he] at hws; simp [writersOf, ha] at hws
    exact ⟨ws, by simpa [writersOf, hna] using hws, hdep⟩
  | create a ar oid o ha ho _ _ hhome _ hdep =>
    rw [writersOf_setEntry]
    rw [lookup_setEntry ha] at hl
    split at hl
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases hl
      rcases hhome with hown | ⟨orig, hlo, harch, t, ht⟩
      · refine ⟨ar.writers, by simp [writersOf, hown, ha], fun v hv => hdep hown v hv⟩
      · obtain ⟨ws, hws, hd⟩ := hw _ _ _ hlo
        rw [harch] at hws
        exact ⟨ws, hws, fun v hv => hd v (by rw [ht]; exact List.mem_append_left _ hv)⟩
    · exact hw _ _ _ hl
  | append a ar oid o y ha ho _ _ _ _ _ hhome hu hdep =>
    rw [writersOf_setEntry]
    rw [lookup_setEntry ha] at hl
    split at hl
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      cases hl
      have hlo : lookup w b x = some (.live o) := by simp [lookup, ha, ho]
      obtain ⟨ws, hws, hd⟩ := hw _ _ _ hlo
      refine ⟨ws, hws, fun v hv => ?_⟩
      simp only [Obj.append, List.mem_append, List.mem_singleton] at hv
      rcases hv with hv | rfl
      · exact hd v hv
      · rcases hhome with hown | ⟨orig, hlor, harch, t, ht⟩
        · rw [hdep hown]
          have : ws = ar.writers := by
            rw [hown] at hws; simp [writersOf, ha] at hws; exact hws.symm
          rw [this]; exact hu
        · obtain ⟨ws', hws', hd'⟩ := hw _ _ _ hlor
          rw [harch, show (o.append _).archive = o.archive from rfl, hws] at hws'
          cases hws'
          exact hd' _ (by rw [ht]; simp [Obj.append])
    · exact hw _ _ _ hl

theorem Act.depositors {u : Agent} {w w' : World D} (h : Act hash u w w')
    (hw : DepositorsOk w) : DepositorsOk w' := by
  cases h with
  | step hs => exact hs.depositors hash hw
  | takedown a ar oid o ha hlo _ =>
    intro b x o' hl
    have hl0 := (lookup_takedown hash hlo hl).2
    obtain ⟨ws, hws, hd⟩ := hw _ _ _ hl0
    exact ⟨ws, by unfold OpenSheaf.takedown tombstone; rw [writersOf_setEntry]; exact hws, hd⟩

theorem Acts.depositors {w : World D}
    (h : Acts hash (fun _ => (none : Option (Archive D))) w) : DepositorsOk w :=
  h.invariant _ (fun ⟨_, ha⟩ => ha.depositors hash) fun b x o hl => by simp [lookup] at hl

/-- **A selection changes only by an act of its curator** (section 10.2). -/
theorem Acts.curated {w : World D}
    (h : Acts hash (fun _ => (none : Option (Archive D))) w) {a : ArchiveId}
    {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
    (hown : o.archive = a) {ar : Archive D} (ha : w a = some ar) :
    ∀ v ∈ o.versions, v.depositor ∈ ar.writers := by
  obtain ⟨ws, hws, hd⟩ := Acts.depositors hash h a oid o hl
  rw [hown] at hws
  simp [writersOf, ha] at hws
  rw [← hws] at hd
  exact hd

end OpenSheaf
