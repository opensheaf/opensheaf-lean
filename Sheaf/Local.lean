-- Generated from literate-sheaf/74-local.md by opensheaf-literate: edit the document, not this file.
import Sheaf.Lifting
import OpenSheaf.Patterns

namespace OpenSheaf.Sheaf

open OpenSheaf.Patterns

variable {D : Type}

/-- The part of a world at the places of `S`: every other entry is dropped. -/
def restrictW (S : ArchiveId → ObjectId → Prop) [∀ a i, Decidable (S a i)] (w : World D) :
    World D :=
  fun a => (w a).map fun ar => { ar with entries := fun i => if S a i then ar.entries i else none }

theorem lookup_restrict (S : ArchiveId → ObjectId → Prop) [∀ a i, Decidable (S a i)]
    (w : World D) (a : ArchiveId) (i : ObjectId) :
    lookup (restrictW S w) a i = if S a i then lookup w a i else none := by
  unfold lookup restrictW
  cases w a <;> by_cases h : S a i <;> simp [h]

theorem restrict_live {S : ArchiveId → ObjectId → Prop} [∀ a i, Decidable (S a i)]
    {w : World D} {a : ArchiveId} {i : ObjectId} {c : Obj D}
    (h : lookup (restrictW S w) a i = some (.live c)) : lookup w a i = some (.live c) := by
  rw [lookup_restrict] at h
  split at h
  · exact h
  · cases h

/-- A source of the part is a source of the world. -/
def Source.lift {S : ArchiveId → ObjectId → Prop} [∀ a i, Decidable (S a i)] {w : World D}
    (i : Source (restrictW S w)) : Source w :=
  ⟨i.archive, i.line, i.obj, restrict_live i.live, i.kind, i.version⟩

theorem heldIn_restrict (S : ArchiveId → ObjectId → Prop) [∀ a i, Decidable (S a i)]
    (w : World D) : Sub (HeldIn (restrictW S w)) (HeldIn w) :=
  fun _ ⟨i, hx⟩ => ⟨i.lift, hx⟩

/-- **Restricting the world restricts the sheaf.** The glued section of a
world, restricted to what a part of it holds, glues the part. -/
theorem restrict_glue (S : ArchiveId → ObjectId → Prop) [∀ a i, Decidable (S a i)]
    {w : World D} {g : Sec (HeldIn w) (Content D)} (hg : Glues (sections w) g) :
    Glues (sections (restrictW S w)) (g.restrict (heldIn_restrict S w)) := by
  intro i
  funext x hx
  exact congrFun (congrFun (hg i.lift) x) hx

variable [DecidableEq D] (E : Env D)

/-- The places of a world that a verifier of `x` and everything below it
needs: the copies that hold a named document version below `x`, and the
entries that a member list below `x` pins, at the pin's hints. -/
def Support (w : World D) (x : Name) (a : ArchiveId) (i : ObjectId) : Prop :=
  (∃ l c, i = .line l ∧ lookup w a i = some (.live c) ∧ c.kind ≠ .owner ∧
    ∃ v ∈ c.versions, (byPins E w).le (c.name v) x) ∨
    (∃ b l c v p, lookup w b (.line l) = some (.live c) ∧ c.kind ≠ .owner ∧ v ∈ c.versions ∧
      (byPins E w).le (c.name v) x ∧ p ∈ v.memberPins ∧ a ∈ p.hints ∧ i = .line p.line)

/-- **Verification is local.** Every member list held below `x` verifies in the
support of `x` exactly as in the whole world. -/
theorem verify_local {w : World D} {x : Name}
    [∀ a i, Decidable (Support E w x a i)] {b : ArchiveId} {l : LineId} {c : Obj D}
    {v : Version D} {ms : Members D} (hl : lookup w b (.line l) = some (.live c))
    (hk : c.kind ≠ .owner) (hv : v ∈ c.versions) (hm : v.members = some ms)
    (hle : (byPins E w).le (c.name v) x) :
    verify E (restrictW (Support E w x) w) ms = verify E w ms := by
  unfold verify
  apply List.map_congr_left
  intro p hp
  have hpm : p ∈ v.memberPins := by unfold Version.memberPins; rw [hm]; exact hp
  unfold resolve
  congr 2
  apply List.map_congr_left
  intro a ha
  have hS : Support E w x a (.line p.line) := Or.inr ⟨b, l, c, v, p, hl, hk, hv, hle, hpm, ha, rfl⟩
  unfold resolveAt
  rw [lookup_restrict, if_yes hS]

end OpenSheaf.Sheaf
