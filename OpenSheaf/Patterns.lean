-- Generated from literate/60-patterns.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Copies
import OpenSheaf.Acts

namespace OpenSheaf.Patterns

open OpenSheaf

variable {D : Type} [DecidableEq D] (hash : Hash D)

/-- What a verifier reports for a member list: each pin with its result. -/
def verify (w : World D) (c : Members D) : List (Pin D × Resolution D) :=
  c.pins.map fun p => (p, resolve hash w p)

/-- Every pin of the member list resolves. -/
def AllOk (w : World D) (c : Members D) : Prop :=
  ∀ p ∈ c.pins, ∃ v, resolve hash w p = .ok v

/-- A member list that verified verifies the same after any steps. -/
theorem verify_stable {w w' : World D} (hs : Steps w w') {c : Members D}
    (hok : AllOk hash w c) : verify hash w' c = verify hash w c := by
  unfold verify
  apply List.map_congr_left
  intro p hp
  obtain ⟨v, hv⟩ := hok p hp
  rw [Steps.resolve_ok hash hs hv, hv]

/-- **A vetted selection is stable.** If every pin of a selection resolves,
then after any number of steps the verifier reports exactly the same, and
updating the selection leaves it as it is. -/
theorem selection_stable {w w' : World D} (hs : Steps w w') {c : Members D}
    (hsel : c.type = .selection) (hok : AllOk hash w c) :
    verify hash w' c = verify hash w c ∧ collect hash w' c = c :=
  ⟨verify_stable hash hs hok, collect_selection hash w' hsel⟩

/-- **Nested pins are stable.** If a pin resolves to a collection version
whose pins all resolve, then after any number of steps it resolves to the
same version, and the member list read through it verifies as before. -/
theorem nested_stable {w w' : World D} (hs : Steps w w') {q : Pin D} {cv : Version D}
    (hq : resolve hash w q = .ok cv)
    (hok : ∀ c, cv.members = some c → AllOk hash w c) :
    resolve hash w' q = .ok cv ∧
      ∀ c, cv.members = some c → verify hash w' c = verify hash w c :=
  ⟨Steps.resolve_ok hash hs hq, fun c hc => verify_stable hash hs (hok c hc)⟩

/-- After a deposit, the head of the object resolves to the version
deposited. -/
theorem head_after_deposit {w : World D} {a : ArchiveId} {ar : Archive D}
    {oid : ObjectId} {o : Obj D} (x : Version D) (ha : w a = some ar) :
    ∃ p, headPin hash (setEntry w a oid (.live (o.append x))) a oid = some p ∧
      resolve hash (setEntry w a oid (.live (o.append x))) p = .ok x := by
  have hl : lookup (setEntry w a oid (.live (o.append x))) a oid =
      some (.live (o.append x)) := by
    rw [lookup_setEntry ha]; simp
  have hp : headPin hash (setEntry w a oid (.live (o.append x))) a oid =
      some ⟨a, oid, (o.append x).versions.length,
        hash ((o.append x).inventory (o.append x).versions.length)⟩ := by
    unfold headPin; rw [hl]; simp [Obj.append]
  refine ⟨_, hp, ?_⟩
  obtain ⟨o', hl', hne, hr⟩ := headPin_resolves hash hp
  rw [hl] at hl'
  cases hl'
  simpa [Obj.append] using hr

/-- **A followed paper is pinned at its new version.** After the authors
deposit `x`, updating a catalogue that follows the paper gives the member
a pin that resolves to `x`. -/
theorem follow_after_deposit {w : World D} {a : ArchiveId} {ar : Archive D}
    {oid : ObjectId} {o : Obj D} (x : Version D) (ha : w a = some ar)
    {c : Members D} (hcat : c.type = .catalogue)
    {m : Member D} (hm : m ∈ c.members) (hf : m.follow = true)
    (hma : m.archive = a) (hmo : m.object = oid) :
    ∃ p, { m with pins := [p] } ∈
        (collect hash (setEntry w a oid (.live (o.append x))) c).members ∧
      resolve hash (setEntry w a oid (.live (o.append x))) p = .ok x := by
  obtain ⟨p, hp, hr⟩ := head_after_deposit hash (o := o) x ha
  refine ⟨p, collect_follow hash _ hcat hm hf ?_, hr⟩
  rw [hma, hmo]; exact hp

/-- **A description-only version is not a new document version.** -/
theorem correction_same_document_version {o : Obj D} (hwf : WellFormed o.versions)
    {v : Version D} (hv : v ∈ o.versions) (d a m : String) :
    WellFormed (o.append (Version.describe o.versions v d a m)).versions ∧
      (Version.describe o.versions v d a m).documentVersion = v.documentVersion :=
  ⟨WellFormed.snoc hwf (describe_extends hv d a m), rfl⟩

/-- **Withdrawal keeps the vetted revision.** -/
theorem withdrawal_keeps_vetted {w : World D} {a : ArchiveId} {ar : Archive D}
    {oid : ObjectId} {o : Obj D} (ha : w a = some ar) (ho : ar.entries oid = some (.live o))
    (hne : o.versions ≠ []) (dep msg : String) {p : Pin D} {v : Version D}
    (hp : resolve hash w p = .ok v) :
    let x := (o.versions.getLast hne).withdraw dep msg
    resolve hash (setEntry w a oid (.live (o.append x))) p = .ok v ∧
      x.status = .withdrawn :=
  ⟨Step.resolve_ok hash (Step.append w a ar oid o _ ha ho) hp, rfl⟩

/-- **A withdrawal, in both columns.** A catalogue following the paper pins
the withdrawal; a selection of it verifies as before and does not move. -/
theorem withdrawal_both_columns {w : World D} {a : ArchiveId} {ar : Archive D}
    {oid : ObjectId} {o : Obj D} (ha : w a = some ar) (ho : ar.entries oid = some (.live o))
    (hne : o.versions ≠ []) (dep msg : String)
    {c : Members D} (hcat : c.type = .catalogue) {m : Member D} (hm : m ∈ c.members)
    (hf : m.follow = true) (hma : m.archive = a) (hmo : m.object = oid)
    {s : Members D} (hsel : s.type = .selection) (hok : AllOk hash w s) :
    let x := (o.versions.getLast hne).withdraw dep msg
    let w' := setEntry w a oid (.live (o.append x))
    (∃ p, { m with pins := [p] } ∈ (collect hash w' c).members ∧
        resolve hash w' p = .ok x ∧ x.status = .withdrawn) ∧
      verify hash w' s = verify hash w s ∧ collect hash w' s = s := by
  intro x w'
  obtain ⟨p, hp, hr⟩ := follow_after_deposit hash (o := o) x ha hcat hm hf hma hmo
  exact ⟨⟨p, hp, hr, rfl⟩,
    selection_stable hash (.tail (.refl _) (Step.append w a ar oid o x ha ho)) hsel hok⟩

/-- **A takedown is reported.** -/
theorem takedown_reported {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) (p : Pin D) :
    resolve hash (takedown hash w a oid o) p =
      if p.archive = a ∧ p.object = oid then .removed else resolve hash w p := by
  split
  · rename_i h
    exact takedown_removed hash hl h
  · rename_i h
    exact takedown_other hash hl h

/-- **The owner decides.** Every version of an object kept in its own archive
was deposited by a writer of the archive, and nobody else can change it. -/
theorem owner_controls {w : World D} (h : Acts hash (fun _ => (none : Option (Archive D))) w)
    {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
    (hown : o.archive = a) {ar : Archive D} (ha : w a = some ar) :
    (∀ v ∈ o.versions, v.depositor ∈ ar.writers) ∧
      ∀ u w', u ∉ ar.writers → Act hash u w w' → lookup w' a oid = lookup w a oid :=
  ⟨Acts.curated hash h hl hown ha, fun _ _ hu hact =>
    hact.outsider hash (fun ar' h' => by rw [ha] at h'; cases h'; exact hu) oid⟩

/-- **A mirror is a receipt.** In a world built by events, every version of a
mirror is the original's version at the same number. -/
theorem mirror_receipt {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w)
    {b : ArchiveId} {x : ObjectId} {m o : Obj D} (hm : lookup w b x = some (.live m))
    (hb : m.archive ≠ b) (ho : lookup w m.archive m.id = some (.live o))
    {n : Nat} {v : Version D} (hv : m.versionAt n = some v) : o.versionAt n = some v := by
  obtain ⟨_, t, ht⟩ := (Events.mirrorsOk hash hs b x m hm hb).2 o ho
  exact versionAt_prefix (t := []) (by simp) ht (Obj.versionAt_bounds hv).2 hv

/-- **Retention.** After a takedown of the record, its pins report `removed`
forever, and every other pin resolves as before. -/
theorem record_retention {w : World D} {a : ArchiveId} {oid : ObjectId} {r : Obj D}
    (hl : lookup w a oid = some (.live r)) :
    (∀ p : Pin D, p.archive = a ∧ p.object = oid → ∀ w',
        Events hash (takedown hash w a oid r) w' → resolve hash w' p = .removed) ∧
      (∀ q : Pin D, ¬ (q.archive = a ∧ q.object = oid) → ∀ v, resolve hash w q = .ok v →
        ∀ w', ValidSteps hash (takedown hash w a oid r) w' → resolve hash w' q = .ok v) := by
  refine ⟨fun p hp w' hs => ?_, fun q hq v hv w' hs => ?_⟩
  · obtain ⟨n, d, h⟩ := (resolve_removed_iff hash).mp (takedown_removed hash hl hp)
    exact (resolve_removed_iff hash).mpr ⟨n, d, Events.tomb_stays hash hs h⟩
  · exact Steps.resolve_ok hash (ValidSteps.toSteps hash hs)
      (by rw [takedown_other hash hl hq]; exact hv)

end OpenSheaf.Patterns
