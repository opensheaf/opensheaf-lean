# Drafts and sealing

"A draft is a sandbox for a work not yet sealed, on which nothing may
rely" (section 10). It belongs to the reserved owner `draft`, has no
genesis record, is never signed, pinned, copied or named by a `sheaf:` URI,
and is "the only object that MAY be rewritten or deleted" (section 10.1).
**Sealing** makes from a work "the first version of its originator's line"
(section 10), under a new genesis record.

An earlier version of this chapter modelled a proposal of issue
[#29](https://github.com/opensheaf/opensheaf.github.io/issues/29): drafts
as a tail of an object's history, with a rule that a version pins only
versions at least as fixed as itself. Version 0.2 of the specification
settles the matter differently, and more simply: drafts are objects of
their own, outside every line, and nothing can pin them. Whether and how
drafts are shared before sealing is still open (#29, section 10.2).

The model needs no rule to keep drafts harmless: a pin names a line
([chapter 1](10-basic.md)), never a draft, so resolution never looks at a
draft. This chapter adds the two changes that only drafts allow, rewriting
and deleting, and proves that they change nothing about any line: every
pin resolves as before, at every archive (`DraftEvent.resolveAt`), and
worlds stay sound (`DraftEvent.sound`). Sealing is a valid step that
creates a line; drafts stay outside it.

    -- in OpenSheaf/Drafts.lean:
    import OpenSheaf.Worlds

    namespace OpenSheaf

    variable {D : Type} [DecidableEq D] (E : Env D)

## Deleting an entry

A draft deleted "leaves no tombstone" (section 10.1): its entry is gone.

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

## Rewriting and deleting drafts

A draft may be replaced by another, in the format of any object of its kind
(section 10.1): the model asks the new draft to be well formed, to be a
draft (`DraftOk`: no signatures, no parent, not an owner), and its pins to
be ones a new version may hold, as for any object (a draft may pin
lines; nothing pins a draft). Or it may be deleted.

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

## Lines are untouched

A draft event changes the entry of a draft, and no other: the copies and
tombstones of every line, in every archive, are as they were.

    /-- **A draft event touches no line.** -/
    theorem DraftEvent.lines {w w' : World D} (he : DraftEvent E w w') (b : ArchiveId)
        (l : LineId) : lookup w' b (.line l) = lookup w b (.line l) := by
      cases he with
      | rewrite a ar d o o' ha =>
        rw [lookup_setEntry ha, if_no (fun h => nomatch h.2)]
      | delete a ar d o ha =>
        rw [lookup_clearEntry ha, if_no (fun h => nomatch h.2)]

Resolution looks only at lines, so every pin resolves as before, at every
archive and through its hints: rewriting a draft never breaks a pin, and
no pin can depend on a draft.

    theorem DraftEvent.resolveAt {w w' : World D} (he : DraftEvent E w w') (b : ArchiveId)
        (p : Pin D) : resolveAt E.hash w' b p = resolveAt E.hash w b p := by
      unfold OpenSheaf.resolveAt; rw [he.lines]

    theorem DraftEvent.resolve {w w' : World D} (he : DraftEvent E w w') (p : Pin D) :
        resolve E.hash w' p = resolve E.hash w p := by
      unfold OpenSheaf.resolve
      congr 1
      exact List.map_congr_left fun b _ => he.resolveAt E b p

And worlds stay sound: the draft written is well formed and its pins are
held; the other objects are as they were, and their pins resolve as
before.

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

## Sealing

"An owner tool seals a work by writing its genesis record (section 5.1),
with the owner as `originator`, and making a new object: the line
`sheaf:<name>:<owner>` ..., whose first version holds the genesis record
and the work as document version 1 (section 4.2), and is signed by the
owner (section 7.1)" (section 10.2). In the model, sealing is a valid step
that creates a line ([chapter 7](45-worlds.md)): its identity check asks
the name to be the genesis record's by algorithm 0 and the owner to be the
originator, and its signature check asks the owner's keys to sign it.

"The versions of a draft are never part of the line sealed from it, and
nothing in the line refers to them" (section 10.2): the line is a new
object, under a new identifier, and its first version is document version
1 whatever the draft's numbering was. Rewriting or deleting the draft
afterwards changes nothing in the line (`DraftEvent.lines`). The first
version of a sealed work, from a draft's version `v`:

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
