-- Generated from literate/60-patterns.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Collection

namespace OpenSheaf.Patterns

open OpenSheaf

variable {D : Type} [DecidableEq D] (hash : Hash D)

/-- Every pin of a member list. -/
def allPins (c : Members D) : List (Pin D) :=
  c.members.flatMap (·.pins)

/-- What a verifier reports for a member list: each pin with its result. -/
def verify (w : World D) (c : Members D) : List (Pin D × Resolution D) :=
  (allPins c).map fun p => (p, resolve hash w p)

/-- Every pin of the member list resolves. -/
def AllOk (w : World D) (c : Members D) : Prop :=
  ∀ p ∈ allPins c, ∃ v, resolve hash w p = .ok v

/-- **A vetted selection is stable.** If every pin of a selection resolves,
then after any number of steps the verifier reports exactly the same, and
updating the selection leaves it as it is. -/
theorem selection_stable {w w' : World D} (hs : Steps w w') {c : Members D}
    (hsel : c.type = .selection) (hok : AllOk hash w c) :
    verify hash w' c = verify hash w c ∧ collect hash w' c = c := by
  refine ⟨?_, collect_selection hash w' hsel⟩
  unfold verify
  apply List.map_congr_left
  intro p hp
  obtain ⟨v, hv⟩ := hok p hp
  rw [Steps.resolve_ok hash hs hv, hv]

/-- **Nested pins are stable.** If a pin resolves to a collection version
whose pins all resolve, then after any number of steps it resolves to the
same version, and the member list read through it verifies as before. -/
theorem nested_stable {w w' : World D} (hs : Steps w w') {q : Pin D} {cv : Version D}
    (hq : resolve hash w q = .ok cv)
    (hok : ∀ c, cv.members = some c → AllOk hash w c) :
    resolve hash w' q = .ok cv ∧
      ∀ c, cv.members = some c → verify hash w' c = verify hash w c := by
  refine ⟨Steps.resolve_ok hash hs hq, fun c hc => ?_⟩
  unfold verify
  apply List.map_congr_left
  intro p hp
  obtain ⟨v, hv⟩ := hok c hc p hp
  rw [Steps.resolve_ok hash hs hv, hv]

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

end OpenSheaf.Patterns
