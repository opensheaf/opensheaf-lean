-- Generated from literate/50-drafts.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Worlds

namespace OpenSheaf

variable {D : Type} [DecidableEq D] (E : Env D)

omit [DecidableEq D] in
/-- Remove the entry of an object of an existing archive. -/
def clearEntry (w : World D) (a : ArchiveId) (oid : ObjectId) : World D :=
  fun b => if b = a then
      (w b).map fun ar => { ar with entries := fun x => if x = oid then none else ar.entries x }
    else w b

omit [DecidableEq D] in
theorem lookup_clearEntry {w : World D} {a : ArchiveId} {ar : Archive D} {oid : ObjectId}
    (ha : w a = some ar) (b : ArchiveId) (x : ObjectId) :
    lookup (clearEntry w a oid) b x = if b = a ∧ x = oid then none else lookup w b x := by
  unfold lookup clearEntry
  by_cases hb : b = a
  · subst hb
    by_cases hx : x = oid <;> simp [ha, hx]
  · simp [hb]

/-- A draft rewritten or deleted (section 10.1). -/
inductive DraftEvent : World D → World D → Prop
  | rewrite (w : World D) (a : ArchiveId) (ar : Archive D) (d : DraftId) (o o' : Obj D)
      (ha : w a = some ar) (ho : ar.entries (.draft d) = some (.live o))
      (hwf : o'.WF (.draft d)) (hdr : DraftOk o')
      (hpins : ∀ v ∈ o'.versions, ∀ p ∈ v.pins, PinOk E w p) :
      DraftEvent w (setEntry w a (.draft d) (.live o'))
  | delete (w : World D) (a : ArchiveId) (ar : Archive D) (d : DraftId) (o : Obj D)
      (ha : w a = some ar) (ho : ar.entries (.draft d) = some (.live o)) :
      DraftEvent w (clearEntry w a (.draft d))

/-- **A draft event touches no line.** -/
theorem DraftEvent.lines {w w' : World D} (he : DraftEvent E w w') (b : ArchiveId)
    (l : LineId) : lookup w' b (.line l) = lookup w b (.line l) := by
  cases he with
  | rewrite a ar d o o' ha =>
    rw [lookup_setEntry ha, if_no (fun h => nomatch h.2)]
  | delete a ar d o ha =>
    rw [lookup_clearEntry ha, if_no (fun h => nomatch h.2)]

theorem DraftEvent.resolveAt {w w' : World D} (he : DraftEvent E w w') (b : ArchiveId)
    (p : Pin D) : resolveAt E.hash w' b p = resolveAt E.hash w b p := by
  unfold OpenSheaf.resolveAt; rw [he.lines]

theorem DraftEvent.resolve {w w' : World D} (he : DraftEvent E w w') (p : Pin D) :
    resolve E.hash w' p = resolve E.hash w p := by
  unfold OpenSheaf.resolve
  congr 1
  exact List.map_congr_left fun b _ => he.resolveAt E b p

theorem DraftEvent.held {w w' : World D} (he : DraftEvent E w w') {p : Pin D}
    (h : Held E w p) : Held E w' p := by
  rcases h with ⟨b, hb, t, ht⟩ | ⟨b, hb, hr⟩
  · exact Or.inl ⟨b, hb, t, by rw [he.resolveAt E]; exact ht⟩
  · exact Or.inr ⟨b, hb, by rw [he.resolveAt E]; exact hr⟩

/-- **Draft events keep worlds sound.** -/
theorem DraftEvent.sound {w w' : World D} (he : DraftEvent E w w') (hw : SoundWorld E w) :
    SoundWorld E w' := by
  have hhe := he
  cases he with
  | rewrite a ar d o o' ha ho hwf _ hpins =>
    refine ⟨fun b x c h => ?_, fun b x c h v hv p hp => ?_⟩
    · rw [lookup_setEntry ha] at h
      split at h
      · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; cases h; exact hwf
      · exact hw.1 _ _ _ h
    · rw [lookup_setEntry ha] at h
      split at h
      · cases h; exact hhe.held E ((hpins v hv p hp).held E)
      · exact hhe.held E (hw.2 _ _ _ h v hv p hp)
  | delete a ar d o ha ho =>
    refine ⟨fun b x c h => ?_, fun b x c h v hv p hp => ?_⟩
    · rw [lookup_clearEntry ha] at h
      split at h
      · cases h
      · exact hw.1 _ _ _ h
    · rw [lookup_clearEntry ha] at h
      split at h
      · cases h
      · exact hhe.held E (hw.2 _ _ _ h v hv p hp)

omit [DecidableEq D] in
/-- The first version of a line sealed from the draft version `v`
(section 10.2): its content, as document version 1, without a parent. -/
def sealVersion (v : Version D) (description depositor message : String) : Version D :=
  { v with
    documentVersion := 1, parent := none, keys := none, carried := [], status := .active
    description, depositor, message }

omit [DecidableEq D] in
theorem sealVersion_content (v : Version D) (d a m : String) :
    (sealVersion v d a m).files = v.files ∧ (sealVersion v d a m).members = v.members ∧
      (sealVersion v d a m).documentVersion = 1 :=
  ⟨rfl, rfl, rfl⟩

end OpenSheaf
