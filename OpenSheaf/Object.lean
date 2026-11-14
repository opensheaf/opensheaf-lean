-- Generated from literate/20-object.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Basic

namespace OpenSheaf

/-- An OCFL object of an OpenSheaf archive (section 7). -/
structure Obj (D : Type) where
  id : ObjectId
  kind : Kind
  versions : List (Version D)

/-- A digest function for inventories. -/
abbrev Hash (D : Type) := List (Version D) → D

namespace Obj

variable {D : Type}

/-- Add an object version at the end of the history. -/
def append (o : Obj D) (v : Version D) : Obj D :=
  { o with versions := o.versions ++ [v] }

/-- Object version `n` (`v1` is `1`), if any. -/
def versionAt (o : Obj D) (n : Nat) : Option (Version D) :=
  if n = 0 then none else o.versions[n - 1]?

/-- What the inventory of object version `n` describes: versions `1` to `n`. -/
def inventory (o : Obj D) (n : Nat) : List (Version D) :=
  o.versions.take n

theorem versionAt_bounds {o : Obj D} {n : Nat} {v : Version D}
    (h : o.versionAt n = some v) : 1 ≤ n ∧ n ≤ o.versions.length := by
  unfold versionAt at h
  split at h
  · contradiction
  · obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h
    omega

end Obj

section Prefix

variable {D : Type}

theorem versionAt_prefix {o o' : Obj D} {pre t t' : List (Version D)} {n : Nat}
    {v : Version D} (ho : o.versions = pre ++ t) (ho' : o'.versions = pre ++ t')
    (hn : n ≤ pre.length) (h : o.versionAt n = some v) : o'.versionAt n = some v := by
  unfold Obj.versionAt at *
  split at h
  · contradiction
  · rename_i hn0
    simp only [hn0, ite_false]
    rw [ho'] at *
    rw [ho] at h
    rw [List.getElem?_append_left (by omega)] at h ⊢
    exact h

theorem inventory_prefix {o o' : Obj D} {pre t t' : List (Version D)} {n : Nat}
    (ho : o.versions = pre ++ t) (ho' : o'.versions = pre ++ t')
    (hn : n ≤ pre.length) : o'.inventory n = o.inventory n := by
  unfold Obj.inventory
  rw [ho, ho', List.take_append_of_le_length hn, List.take_append_of_le_length hn]

end Prefix

section DocumentVersions

variable {D : Type} [DecidableEq D]

/-- Two object versions have the same content. -/
def sameContent (v w : Version D) : Bool :=
  v.files == w.files && v.members == w.members

/-- The highest document version of a history. -/
def docCount : List (Version D) → Nat
  | [] => 0
  | v :: l => max v.documentVersion (docCount l)

/-- `x` may follow the history `l` (section 7.3). -/
def Follows (l : List (Version D)) (x : Version D) : Prop :=
  (∃ v ∈ l, sameContent v x = true ∧ x.documentVersion = v.documentVersion) ∨
    ((∀ v ∈ l, sameContent v x = false) ∧ x.documentVersion = docCount l + 1)

instance (l : List (Version D)) (x : Version D) : Decidable (Follows l x) := by
  unfold Follows; infer_instance

/-- A well-formed history: each version follows those before it. -/
def WellFormed (l : List (Version D)) : Prop :=
  ∀ i (h : i < l.length), Follows (l.take i) l[i]

instance (l : List (Version D)) : Decidable (WellFormed l) := by
  unfold WellFormed; infer_instance

/-- Appending a version that follows the history keeps it well formed. -/
theorem WellFormed.snoc {l : List (Version D)} {x : Version D} (h : WellFormed l)
    (hx : Follows l x) : WellFormed (l ++ [x]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hlt : i < l.length
  · rw [List.take_append_of_le_length (Nat.le_of_lt hlt), List.getElem_append_left hlt]
    exact h i hlt
  · have hi' : i = l.length := by omega
    subst hi'
    simpa using hx

theorem WellFormed.single {x : Version D} (hx : x.documentVersion = 1) :
    WellFormed [x] := by
  have := WellFormed.snoc (l := []) (x := x) (fun i h => absurd h (by simp))
    (Or.inr ⟨by simp, by simp [docCount, hx]⟩)
  simpa using this

/-- A description-only version (section 7.3): a new description of the
content of `v`. -/
def Version.describe (v : Version D) (description depositor message : String) :
    Version D :=
  { v with description, depositor, message }

/-- A withdrawal (section 11.1): the same content, with status `withdrawn`. -/
def Version.withdraw (last : Version D) (depositor message : String) : Version D :=
  { last with status := .withdrawn, depositor, message }

/-- A new document version of the history `l`: new content. -/
def Version.revise (l : List (Version D)) (files : List (LogicalPath × D))
    (members : Option (Members D)) (description depositor message : String) :
    Version D :=
  { documentVersion := docCount l + 1, files, members, description, depositor, message }

theorem sameContent_self (v : Version D) : sameContent v v = true := by
  simp [sameContent]

theorem describe_follows {l : List (Version D)} {v : Version D} (hv : v ∈ l)
    (d a m : String) : Follows l (v.describe d a m) :=
  Or.inl ⟨v, hv, by simp [sameContent, Version.describe], rfl⟩

theorem withdraw_follows {l : List (Version D)} {v : Version D} (hv : v ∈ l)
    (a m : String) : Follows l (v.withdraw a m) :=
  Or.inl ⟨v, hv, by simp [sameContent, Version.withdraw], rfl⟩

theorem revise_follows (l : List (Version D)) (fs : List (LogicalPath × D))
    (ms : Option (Members D)) (d a m : String)
    (hnew : ∀ v ∈ l, sameContent v (Version.revise l fs ms d a m) = false) :
    Follows l (Version.revise l fs ms d a m) :=
  Or.inr ⟨hnew, rfl⟩

omit [DecidableEq D] in
/-- A description-only version keeps the document version and the content. -/
theorem describe_keeps (v : Version D) (d a m : String) :
    (v.describe d a m).documentVersion = v.documentVersion ∧
    (v.describe d a m).files = v.files ∧
    (v.describe d a m).members = v.members :=
  ⟨rfl, rfl, rfl⟩

end DocumentVersions

end OpenSheaf
