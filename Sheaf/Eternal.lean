-- Generated from literate-sheaf/70-eternal.md by opensheaf-literate: edit the document, not this file.
import Sheaf.Acyclic

namespace OpenSheaf.Sheaf

variable {D : Type} [DecidableEq D] (E : Env D)

theorem holds_line {w : World D} (hw : SoundWorld E w) {x : Name} {v : Version D}
    (h : Holds w x v) : ∃ b l c, lookup w b (.line l) = some (.live c) ∧ c.kind ≠ .owner ∧
      v ∈ c.versions ∧ x = ⟨.line l, v.documentVersion⟩ := by
  obtain ⟨b, l, c, hl, hk, hv, rfl⟩ := h
  exact ⟨b, l, c, hl, hk, hv, by simp only [Obj.name, (hw.1 _ _ _ hl).id]⟩

/-- **Names are eternal.** A named document version held in two worlds built by
events has the same content in both, when owners are honest. -/
theorem names_eternal {w w' : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w)
    (hs' : Events E (fun _ => (none : Option (Archive D))) w') {H : Histories D}
    (hh : Honest E H w) (hh' : Honest E H w')
    {x : Name} {v v' : Version D} (h : Holds w x v) (h' : Holds w' x v') :
    v.content = v'.content := by
  obtain ⟨b, l, c, hl, hk, hv, rfl⟩ := holds_line E (Events.sound E hs) h
  obtain ⟨b', l', c', hl', hk', hv', hx⟩ := holds_line E (Events.sound E hs') h'
  simp only [Name.mk.injEq, ObjectId.line.injEq] at hx
  obtain ⟨rfl, hd⟩ := hx
  have hc := honest_comparable E hs hs' hh hh' hl hl' hk hk'
  apply content_eq_iff.mpr
  rcases hc with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact one_number_one_content (((Events.sound E hs').1 _ _ _ hl').history hk')
      (by rw [ht]; exact List.mem_append_left _ hv) hv' hd
  · exact one_number_one_content (((Events.sound E hs).1 _ _ _ hl).history hk)
      hv (by rw [ht]; exact List.mem_append_left _ hv') hd

/-- **Gluing across worlds.** The glued sections of two worlds built by events
agree wherever both are defined, when owners are honest. -/
theorem glue_eternal {w w' : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w)
    (hs' : Events E (fun _ => (none : Option (Archive D))) w') {H : Histories D}
    (hh : Honest E H w) (hh' : Honest E H w')
    {g : Sec (HeldIn w) (Content D)} (hg : Glues (sections w) g)
    {g' : Sec (HeldIn w') (Content D)} (hg' : Glues (sections w') g')
    {x : Name} (hx : HeldIn w x) (hx' : HeldIn w' x) : g x hx = g' x hx' := by
  have hk := Events.sound E hs
  have hk' := Events.sound E hs'
  obtain ⟨v, hv⟩ := (heldIn_iff E hk x).mp hx
  obtain ⟨v', hv'⟩ := (heldIn_iff E hk' x).mp hx'
  rw [glue_value E hk hg hv hx, glue_value E hk' hg' hv' hx']
  exact names_eternal E hs hs' hh hh' hv hv'

omit [DecidableEq D] in
theorem Step.holds {w w' : World D} (hs : Step w w') {x : Name} {v : Version D}
    (h : Holds w x v) : Holds w' x v := by
  obtain ⟨b, l, c, hl, hk, hv, rfl⟩ := h
  obtain ⟨c', hl', hg⟩ := hs.live_grows hl
  obtain ⟨t, ht⟩ := hg.versions
  exact ⟨b, l, c', hl', by rw [hg.kind]; exact hk, by rw [ht]; exact List.mem_append_left _ hv,
    by simp only [Obj.name, hg.id]⟩

omit [DecidableEq D] in
theorem Steps.holds {w w' : World D} (hs : Steps w w') {x : Name} {v : Version D}
    (h : Holds w x v) : Holds w' x v :=
  hs.invariant (fun w => Holds w x v) (fun h1 h2 => Step.holds h1 h2) h

omit [DecidableEq D] in
theorem takedown_holds {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    (hl0 : lookup w a oid = some (.live o)) {x : Name} {v : Version D}
    (h : Holds (takedown E.hash w a oid o) x v) : Holds w x v := by
  obtain ⟨b, l, c, hl, hk, hv, hx⟩ := h
  exact ⟨b, l, c, (lookup_takedown E.hash hl0 hl).2, hk, hv, hx⟩

end OpenSheaf.Sheaf
