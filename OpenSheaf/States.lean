-- Generated from literate/50-states.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Archive

namespace OpenSheaf.States

open OpenSheaf

/-- How fixed a version is. -/
inductive Fixity
  | draft
  | priv
  | pub
  deriving DecidableEq, Repr

/-- The order draft < private < public. -/
def Fixity.rank : Fixity → Nat
  | .draft => 0
  | .priv => 1
  | .pub => 2

/-- Which objects each archive serves. -/
abbrev Serving := ArchiveId → ObjectId → Bool

variable {D : Type} (isDraft : Version D → Bool)

/-- The fixity of a version of object `oid` of archive `a`. -/
def fixity (served : Serving) (a : ArchiveId) (oid : ObjectId) (v : Version D) : Fixity :=
  if isDraft v then .draft else if served a oid then .pub else .priv

theorem rank_le_two (served : Serving) (a : ArchiveId) (oid : ObjectId) (v : Version D) :
    (fixity isDraft served a oid v).rank ≤ 2 := by
  unfold fixity
  split
  · simp [Fixity.rank]
  · split <;> simp [Fixity.rank]

theorem rank_pos_iff (served : Serving) (a : ArchiveId) (oid : ObjectId) (v : Version D) :
    1 ≤ (fixity isDraft served a oid v).rank ↔ isDraft v = false := by
  unfold fixity
  cases h : isDraft v
  · simp only [Bool.false_eq_true, ite_false]
    split <;> simp [Fixity.rank]
  · simp [Fixity.rank]

/-- Serving more objects makes versions only more fixed. -/
theorem rank_mono {served served' : Serving}
    (hs : ∀ b x, served b x = true → served' b x = true)
    (a : ArchiveId) (oid : ObjectId) (v : Version D) :
    (fixity isDraft served a oid v).rank ≤ (fixity isDraft served' a oid v).rank := by
  unfold fixity
  cases isDraft v
  · cases h : served a oid
    · cases served' a oid <;> simp [Fixity.rank]
    · simp [hs a oid h, Fixity.rank]
  · simp [Fixity.rank]

section Rewrite

variable [DecidableEq D] (hash : Hash D)

/-- Replace the drafts of an object (the tail after `sealed`) by new versions:
drafts revised, or sealed. -/
def rewriteDrafts (w : World D) (a : ArchiveId) (oid : ObjectId) (o : Obj D)
    (sealed newTail : List (Version D)) : World D :=
  setEntry w a oid (.live { o with versions := sealed ++ newTail })

/-- Rewriting drafts does not change what a pin of a sealed version resolves
to. -/
theorem rewrite_keeps_sealed {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
    {sealed drafts newTail : List (Version D)}
    (hl : lookup w a oid = some (.live o)) (hv : o.versions = sealed ++ drafts)
    (hd : ∀ v ∈ drafts, isDraft v = true) {p : Pin D} {t : Version D}
    (hp : resolve hash w p = .ok t) (ht : isDraft t = false) :
    resolve hash (rewriteDrafts w a oid o sealed newTail) p = .ok t := by
  obtain ⟨ar, ha⟩ := lookup_some_archive hl
  unfold resolve rewriteDrafts at *
  rw [lookup_setEntry ha]
  split
  · rename_i hc
    obtain ⟨h1, h2⟩ := hc
    rw [h1, h2, hl] at hp
    obtain ⟨hvat, _⟩ := resolveEntry_live_ok hash hp
    have hn : p.version ≤ sealed.length := by
      obtain ⟨hpos, _⟩ := Obj.versionAt_bounds hvat
      refine Nat.le_of_not_lt fun hlt => ?_
      unfold Obj.versionAt at hvat
      have hne : p.version ≠ 0 := by omega
      simp only [hne, ite_false] at hvat
      rw [hv, List.getElem?_append_right (by omega)] at hvat
      have := hd t (List.mem_of_getElem? hvat)
      rw [ht] at this
      contradiction
    exact resolveEntry_prefix hash (o := o) (o' := { o with versions := sealed ++ newTail })
      ⟨rfl, rfl⟩ hv rfl hn hp
  · exact hp

/-- Versions pin only versions at least as fixed as themselves. -/
def Fixed (w : World D) (served : Serving) : Prop :=
  ∀ a oid o, lookup w a oid = some (.live o) →
    ∀ v ∈ o.versions, ∀ p ∈ v.pins, ∀ t, resolve hash w p = .ok t →
      (fixity isDraft served a oid v).rank ≤
        (fixity isDraft served p.archive p.object t).rank

/-- Under the rule, a sealed version pins only sealed versions. -/
theorem Fixed.target_sealed {w : World D} {served : Serving} (hF : Fixed isDraft hash w served)
    {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
    {v : Version D} (hv : v ∈ o.versions) (hs : isDraft v = false)
    {p : Pin D} (hp : p ∈ v.pins) {t : Version D} (hr : resolve hash w p = .ok t) :
    isDraft t = false := by
  have h := hF a oid o hl v hv p hp t hr
  have h1 := (rank_pos_iff isDraft served a oid v).mpr hs
  exact (rank_pos_iff isDraft served p.archive p.object t).mp (by omega)

/-- **Drafts are safe to rewrite.** Under the rule, rewriting the drafts of an
object never changes what a pin held by a sealed version resolves to. -/
theorem sealed_pins_survive {w : World D} {served : Serving}
    (hF : Fixed isDraft hash w served)
    {a : ArchiveId} {oid : ObjectId} {o : Obj D} {sealed drafts newTail : List (Version D)}
    (hl : lookup w a oid = some (.live o)) (hv : o.versions = sealed ++ drafts)
    (hd : ∀ v ∈ drafts, isDraft v = true)
    {b : ArchiveId} {x : ObjectId} {o' : Obj D} (hl' : lookup w b x = some (.live o'))
    {v : Version D} (hv' : v ∈ o'.versions) (hs : isDraft v = false)
    {p : Pin D} (hp : p ∈ v.pins) {t : Version D} (hr : resolve hash w p = .ok t) :
    resolve hash (rewriteDrafts w a oid o sealed newTail) p = .ok t :=
  rewrite_keeps_sealed isDraft hash hl hv hd hr (hF.target_sealed isDraft hash hl' hv' hs hp hr)

/-- Serve one more object. -/
def publish (served : Serving) (a : ArchiveId) (oid : ObjectId) : Serving :=
  fun b x => if b = a ∧ x = oid then true else served b x

theorem publish_mono (served : Serving) (a : ArchiveId) (oid : ObjectId) (b : ArchiveId)
    (x : ObjectId) (h : served b x = true) : publish served a oid b x = true := by
  unfold publish; split <;> simp_all

/-- **Publication keeps the rule**, when the sealed versions of the object
published pin only public versions. -/
theorem publish_fixed {w : World D} {served : Serving} (hF : Fixed isDraft hash w served)
    {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
    (hpre : ∀ v ∈ o.versions, isDraft v = false → ∀ p ∈ v.pins, ∀ t,
      resolve hash w p = .ok t → served p.archive p.object = true ∧ isDraft t = false) :
    Fixed isDraft hash w (publish served a oid) := by
  intro b x o' hl' v hv p hp t hr
  have hmono := rank_mono isDraft (publish_mono served a oid)
  by_cases hc : b = a ∧ x = oid
  · obtain ⟨rfl, rfl⟩ := hc
    rw [hl] at hl'
    cases hl'
    cases hdv : isDraft v
    · obtain ⟨hsrv, htd⟩ := hpre v hv hdv p hp t hr
      have h2 : (fixity isDraft (publish served b x) p.archive p.object t).rank = 2 := by
        simp [fixity, htd, publish_mono served b x _ _ hsrv, Fixity.rank]
      have := rank_le_two isDraft (publish served b x) b x v
      omega
    · simp [fixity, hdv, Fixity.rank]
  · have hsame : fixity isDraft (publish served a oid) b x v = fixity isDraft served b x v := by
      simp [fixity, publish, hc]
    have := hF b x o' hl' v hv p hp t hr
    have := hmono p.archive p.object t
    rw [hsame]
    omega

end Rewrite

end OpenSheaf.States
