-- Generated from literate/60-patterns.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Copies

namespace OpenSheaf.Patterns

open OpenSheaf

variable {D : Type} [DecidableEq D] (E : Env D)

/-- What a verifier reports for a member list: each pin with its result. -/
def verify (w : World D) (c : Members D) : List (Pin D × Resolution D) :=
  c.pins.map fun p => (p, resolve E.hash w p)

/-- Every pin of the member list resolves. -/
def AllOk (w : World D) (c : Members D) : Prop :=
  ∀ p ∈ c.pins, ∃ v, resolve E.hash w p = .ok v

/-- The owners of the lines pinned are honest, and no pin names a key log. -/
def Honest (w : World D) (ps : List (Pin D)) : Prop :=
  ∀ p ∈ ps, OneHistory E w p.line ∧ p.line ≠ keyLogLine p.line.owner

/-- A member list that verified verifies the same after any steps. -/
theorem verify_stable {w w' : World D}
    (hw' : Events E (fun _ => (none : Option (Archive D))) w') (hs : Steps w w')
    {c : Members D} (hh : Honest E w' c.pins) (hok : AllOk E w c) :
    verify E w' c = verify E w c := by
  unfold verify
  apply List.map_congr_left
  intro p hp
  obtain ⟨v, hv⟩ := hok p hp
  rw [Steps.resolve_ok E hw' hs (hh p hp).1 (hh p hp).2 hv, hv]

/-- **A vetted selection is stable.** If every pin of a selection resolves,
then after any number of steps the verifier reports exactly the same, and
updating the selection leaves it as it is. -/
theorem selection_stable {w w' : World D}
    (hw' : Events E (fun _ => (none : Option (Archive D))) w') (hs : Steps w w')
    {c : Members D} (hsel : c.type = .selection) (hh : Honest E w' c.pins) (hok : AllOk E w c) :
    verify E w' c = verify E w c ∧ collect E.hash w' c = c :=
  ⟨verify_stable E hw' hs hh hok, collect_selection E.hash w' hsel⟩

/-- **Nested pins are stable.** If a pin resolves to a collection version whose
pins all resolve, then after any number of steps it resolves to the same
version, and the member list read through it verifies as before. -/
theorem nested_stable {w w' : World D}
    (hw' : Events E (fun _ => (none : Option (Archive D))) w') (hs : Steps w w')
    {q : Pin D} {cv : Version D} (hq : resolve E.hash w q = .ok cv) (hhq : Honest E w' [q])
    (hok : ∀ c, cv.members = some c → Honest E w' c.pins ∧ AllOk E w c) :
    resolve E.hash w' q = .ok cv ∧
      ∀ c, cv.members = some c → verify E w' c = verify E w c := by
  have := hhq q (List.mem_singleton_self _)
  exact ⟨Steps.resolve_ok E hw' hs this.1 this.2 hq,
    fun c hc => verify_stable E hw' hs (hok c hc).1 (hok c hc).2⟩

/-- After a deposit at the first hint, the head of the line resolves there to
the version deposited. -/
theorem head_after_deposit {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
    {o : Obj D} (x : Version D) (ss : List (Sig D)) (ha : w a = some ar)
    (rest : List ArchiveId) :
    ∃ p, headPin E.hash (setEntry w a (.line l) (.live (o.append x ss))) (a :: rest) l = some p ∧
      resolveAt E.hash (setEntry w a (.line l) (.live (o.append x ss))) a p = .ok x := by
  have hl : lookup (setEntry w a (.line l) (.live (o.append x ss))) a (.line l) =
      some (.live (o.append x ss)) := by
    rw [lookup_setEntry ha]; simp
  have hp : headPin E.hash (setEntry w a (.line l) (.live (o.append x ss))) (a :: rest) l =
      some ⟨l, (o.append x ss).versions.length,
        E.hash ((o.append x ss).inventory (o.append x ss).versions.length), a :: rest⟩ := by
    unfold headPin headIn; rw [hl]; simp [Obj.append]
  refine ⟨_, hp, ?_⟩
  unfold resolveAt
  rw [hl]
  apply resolveEntry_live_of
  · simp [Obj.versionAt, Obj.append]
  · rfl

/-- **A followed paper is pinned at its new version.** After the owner deposits
`x` at the first hint of a member that follows the paper, updating the
catalogue gives the member a pin that resolves there to `x`. -/
theorem follow_after_deposit {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
    {o : Obj D} (x : Version D) (ss : List (Sig D)) (ha : w a = some ar)
    {c : Members D} (hcat : c.type = .catalogue)
    {m : Member D} (hm : m ∈ c.members) (hf : m.follow = true)
    {rest : List ArchiveId} (hma : m.hints = a :: rest) (hml : m.line = l) :
    ∃ p, { m with pins := [p] } ∈
        (collect E.hash (setEntry w a (.line l) (.live (o.append x ss))) c).members ∧
      resolveAt E.hash (setEntry w a (.line l) (.live (o.append x ss))) a p = .ok x := by
  obtain ⟨p, hp, hr⟩ := head_after_deposit E (o := o) (l := l) x ss ha rest
  refine ⟨p, collect_follow E.hash _ hcat hm hf ?_, hr⟩
  rw [hma, hml]; exact hp

/-- **A description-only version is not a new document version.** -/
theorem correction_same_document_version {o : Obj D} (hwf : WellFormed o.versions)
    {v : Version D} (hv : v ∈ o.versions) (d a m : String) (ss : List (Sig D)) :
    WellFormed (o.append (Version.describe o.versions v d a m) ss).versions ∧
      (Version.describe o.versions v d a m).documentVersion = v.documentVersion :=
  ⟨WellFormed.snoc hwf (describe_extends hv d a m), rfl⟩

/-- **Withdrawal keeps the vetted revision.** -/
theorem withdrawal_keeps_vetted {w : World D} {a : ArchiveId} {ar : Archive D}
    {oid : ObjectId} {o : Obj D} (ha : w a = some ar) (ho : ar.entries oid = some (.live o))
    (hne : o.versions ≠ []) (dep msg : String) (ss : List (Sig D)) {b : ArchiveId}
    {p : Pin D} {v : Version D} (hp : resolveAt E.hash w b p = .ok v) :
    let x := (o.versions.getLast hne).withdraw dep msg
    resolveAt E.hash (setEntry w a oid (.live (o.append x ss))) b p = .ok v ∧
      x.status = .withdrawn :=
  ⟨Step.resolveAt_ok E.hash (Step.append w a ar oid o _ ss ha ho) hp, rfl⟩

/-- **A withdrawal, in both columns.** A catalogue following the paper pins
the withdrawal; every pin of a selection that resolved at a hint resolves there
as before, and the selection does not move. -/
theorem withdrawal_both_columns {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
    {o : Obj D} (ha : w a = some ar) (ho : ar.entries (.line l) = some (.live o))
    (hne : o.versions ≠ []) (dep msg : String) (ss : List (Sig D))
    {c : Members D} (hcat : c.type = .catalogue) {m : Member D} (hm : m ∈ c.members)
    (hf : m.follow = true) {rest : List ArchiveId} (hma : m.hints = a :: rest)
    (hml : m.line = l) {s : Members D} (hsel : s.type = .selection) :
    let x := (o.versions.getLast hne).withdraw dep msg
    let w' := setEntry w a (.line l) (.live (o.append x ss))
    (∃ p, { m with pins := [p] } ∈ (collect E.hash w' c).members ∧
        resolveAt E.hash w' a p = .ok x ∧ x.status = .withdrawn) ∧
      (∀ p ∈ s.pins, ∀ b v, resolveAt E.hash w b p = .ok v → resolveAt E.hash w' b p = .ok v) ∧
      collect E.hash w' s = s := by
  intro x w'
  obtain ⟨p, hp, hr⟩ := follow_after_deposit E (o := o) x ss ha hcat hm hf hma hml
  exact ⟨⟨p, hp, hr, rfl⟩,
    fun _ _ _ _ h => Step.resolveAt_ok E.hash (Step.append w a ar _ o x ss ha ho) h,
    collect_selection E.hash w' hsel⟩

/-- **Only the owner adds to a member.** Every copy of a member, wherever it is
kept, ends in a version signed with a current key of the owner's key log as
the world holds it. -/
theorem member_signed {w : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w) {m : Member D}
    (hnk : m.line ≠ keyLogLine m.line.owner) {b : ArchiveId} {o : Obj D}
    (hl : lookup w b (.line m.line) = some (.live o)) : HeadSigned E w m.line o :=
  Events.headsSigned E hs hl fun hk => hnk (Events.keyLog_line E hs hl hk)

/-- **A takedown is reported.** -/
theorem takedown_reported {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl : lookup w a oid = some (.live o)) (b : ArchiveId) (p : Pin D) :
    resolveAt E.hash (takedown E.hash w a oid o) b p =
      if b = a ∧ ObjectId.line p.line = oid then .removed else resolveAt E.hash w b p := by
  split
  · rename_i h
    obtain ⟨rfl, h⟩ := h
    exact takedown_removed E.hash hl h
  · rename_i h
    exact takedown_other E.hash hl h

/-- **The owner decides.** A valid step that writes a copy of a line, which is
not a key log, writes one whose head the line's owner signed. -/
theorem owner_decides {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
    {o' : Obj D} (hauth : Authorised E w a ar (.line l) o') (hk : o'.kind ≠ .owner) :
    HeadSigned E w l o' :=
  (authorised_ownersSign E hauth).1 hk

/-- **A mirror is a receipt.** In a world built by events, a version of any
copy of a line is the version of every other copy at the same number, when
the owner signs one history. -/
theorem mirror_receipt {w : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w) {l : LineId}
    (h1 : OneHistory E w l) (hnk : l ≠ keyLogLine l.owner)
    {b b' : ArchiveId} {m o : Obj D} (hm : lookup w b (.line l) = some (.live m))
    (ho : lookup w b' (.line l) = some (.live o))
    {n : Nat} {v u : Version D} (hv : m.versionAt n = some v) (hu : o.versionAt n = some u) :
    u = v :=
  ((Events.copiesAgree E hs h1 b b' m o hm ho (fun hk => hnk (Events.keyLog_line E hs hm hk))
    (fun hk => hnk (Events.keyLog_line E hs ho hk))).versionAt hv hu).symm

/-- **Retention.** After a takedown of the record, its pins report `removed`
there forever, and every other pin resolves as before. -/
theorem record_retention {w : World D} {a : ArchiveId} {oid : ObjectId} {r : Obj D}
    (hl : lookup w a oid = some (.live r)) :
    (∀ p : Pin D, ObjectId.line p.line = oid → ∀ w',
        Events E (takedown E.hash w a oid r) w' → resolveAt E.hash w' a p = .removed) ∧
      (∀ b (q : Pin D), ¬ (b = a ∧ ObjectId.line q.line = oid) → ∀ v,
        resolveAt E.hash w b q = .ok v →
        ∀ w', ValidSteps E (takedown E.hash w a oid r) w' → resolveAt E.hash w' b q = .ok v) := by
  refine ⟨fun p hp w' hs => ?_, fun b q hq v hv w' hs => ?_⟩
  · obtain ⟨n, d, h⟩ := (resolveAt_removed_iff E.hash).mp (takedown_removed E.hash hl hp)
    exact (resolveAt_removed_iff E.hash).mpr ⟨n, d, Events.tomb_stays E hs h⟩
  · exact Steps.resolveAt_ok E.hash (ValidSteps.toSteps E hs)
      (by rw [takedown_other E.hash hl hq]; exact hv)

end OpenSheaf.Patterns
