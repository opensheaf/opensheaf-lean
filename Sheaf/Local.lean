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
  ⟨i.archive, i.id, i.obj, restrict_live i.live, i.version⟩

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

variable [DecidableEq D] (hash : Hash D)

/-- The places of a world that a verifier of `x` and everything below it
needs: the copies that hold a named document version below `x`, and the
tombstones. -/
def Support (w : World D) (x : Name) (a : ArchiveId) (i : ObjectId) : Prop :=
  (∃ c, lookup w a i = some (.live c) ∧ ∃ v ∈ c.versions, (byPins hash w).le (c.name v) x) ∨
    ∃ n d, lookup w a i = some (.tomb n d)

/-- **Verification is local.** In a world built by events, every member list
held below `x` verifies in the support of `x` exactly as in the whole world. -/
theorem verify_local {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) {x : Name}
    [∀ a i, Decidable (Support hash w x a i)] {b : ArchiveId} {i : ObjectId} {c : Obj D}
    {v : Version D} {ms : Members D} (hl : lookup w b i = some (.live c))
    (hv : v ∈ c.versions) (hm : v.members = some ms) (hle : (byPins hash w).le (c.name v) x) :
    verify hash (restrictW (Support hash w x) w) ms = verify hash w ms := by
  unfold verify
  apply List.map_congr_left
  intro p hp
  have hpm : p ∈ v.memberPins := by unfold Version.memberPins; rw [hm]; exact hp
  have hS : Support hash w x p.archive p.object := by
    rcases members_below hash hs hl hv hpm with ⟨o, u, ho, hr, hle'⟩ | hr
    · have hre : resolveEntry hash (some (.live o)) p = .ok u := by
        unfold resolve at hr; rw [ho] at hr; exact hr
      exact Or.inl ⟨o, ho, u, versionAt_mem (resolveEntry_live_ok hash hre).1,
        (byPins hash w).trans hle' hle⟩
    · exact Or.inr ((resolve_removed_iff hash).mp hr)
  unfold resolve
  rw [lookup_restrict, if_yes hS]

end OpenSheaf.Sheaf
