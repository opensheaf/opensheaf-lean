# Objects and their history

An object is the list of its object versions, oldest first (section 7). This
chapter defines objects, their versions and inventories, proves that a
history which keeps a prefix keeps the versions and inventories within it,
and gives the rules by which document versions are counted.

    -- in OpenSheaf/Object.lean:
    import OpenSheaf.Basic

    namespace OpenSheaf

## Objects

An object has an identifier, a kind, and its history.

    /-- An OCFL object of an OpenSheaf archive (section 7). -/
    structure Obj (D : Type) where
      id : ObjectId
      kind : Kind
      versions : List (Version D)

OCFL writes, with each object version `n`, an inventory describing versions
`1` to `n`, and the pin of version `n` carries the digest of that inventory.
The model takes the prefix of length `n` of the history as what the
inventory describes, and the digest of the inventory as a function `hash` of
that prefix. Since the inventory of version `n` describes all the versions
before it, a pin of version `n` fixes them too: this is why the prefix, and
not version `n` alone, is hashed.

    /-- A digest function for inventories. -/
    abbrev Hash (D : Type) := List (Version D) → D

Three operations on an object: adding a version at the end, finding version
`n` (there is no version 0), and the inventory of version `n`.

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

If version `n` exists, then `n` is between 1 and the length of the history.

    theorem versionAt_bounds {o : Obj D} {n : Nat} {v : Version D}
        (h : o.versionAt n = some v) : 1 ≤ n ∧ n ≤ o.versions.length := by
      unfold versionAt at h
      split at h
      · contradiction
      · obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp h
        omega

    end Obj

## Histories that share a prefix

Two changes of an object keep a prefix of its history: appending a version
keeps the whole history, and rewriting drafts ([chapter 5](50-states.md))
keeps the versions before the drafts. The two lemmas below say that, within
the prefix, versions and inventories are unchanged. They hold whatever the
digest function, since they are about the versions themselves; this is the
heart of every immutability result of the model.

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

## Document versions

The specification distinguishes object versions, which OCFL counts, from
document versions, which count the changes of the content (section 7.3). A
new object version with the same files and members as the previous one (a
description-only version, a withdrawal) keeps the document version; any
other adds one.

    section DocumentVersions

    variable {D : Type} [DecidableEq D]

    /-- Two object versions have the same content. -/
    def sameContent (v w : Version D) : Bool :=
      v.files == w.files && v.members == w.members

    /-- `w` may follow `v` in a history. -/
    def Follows (v w : Version D) : Prop :=
      w.documentVersion = if sameContent v w then v.documentVersion else v.documentVersion + 1

A history is well formed when it starts at document version 1 and each
version follows the previous one. `ChainFrom v l` says that the versions of
`l` follow each other, starting after `v`.

    /-- Each version follows the previous one. -/
    def ChainFrom : Version D → List (Version D) → Prop
      | _, [] => True
      | v, w :: rest => Follows v w ∧ ChainFrom w rest

    /-- A well-formed history: it starts at document version 1, and each version
    follows the previous one. -/
    def WellFormed : List (Version D) → Prop
      | [] => True
      | v :: rest => v.documentVersion = 1 ∧ ChainFrom v rest

Appending a version that follows the last one keeps a history well formed.
The proof goes along the history to its last version.

    theorem ChainFrom.snoc {v x : Version D} {l : List (Version D)} (h : ChainFrom v l)
        (hx : Follows ((v :: l).getLast (List.cons_ne_nil _ _)) x) :
        ChainFrom v (l ++ [x]) := by
      induction l generalizing v with
      | nil => exact ⟨hx, trivial⟩
      | cons w rest ih =>
        obtain ⟨hvw, hrest⟩ := h
        refine ⟨hvw, ih hrest ?_⟩
        simpa [List.getLast_cons] using hx

    /-- Appending a version that follows the last one keeps a history well
    formed. -/
    theorem WellFormed.snoc {l : List (Version D)} {x : Version D} (h : WellFormed l)
        (hne : l ≠ []) (hx : Follows (l.getLast hne) x) : WellFormed (l ++ [x]) := by
      match l, h, hne, hx with
      | v :: rest, ⟨h1, hc⟩, _, hx => exact ⟨h1, ChainFrom.snoc hc hx⟩

## The three kinds of new version

An author's archive makes new object versions in three ways: a
**description-only version** (section 7.3) changes the description; a
**withdrawal** (section 11.1) changes the status; a **revision** changes the
content and adds a document version. Each is built from the last version of
the history.

    /-- A description-only version (section 7.3): a new description, the same
    content. -/
    def Version.describe (last : Version D) (description depositor message : String) :
        Version D :=
      { last with description, depositor, message }

    /-- A withdrawal (section 11.1): the same content, with status `withdrawn`. -/
    def Version.withdraw (last : Version D) (depositor message : String) : Version D :=
      { last with status := .withdrawn, depositor, message }

    /-- A new document version: new content. -/
    def Version.revise (last : Version D) (files : List (LogicalPath × D))
        (members : Option (Members D)) (description depositor message : String) :
        Version D :=
      { documentVersion := last.documentVersion + 1, files, members, description,
        status := last.status, depositor, message }

Each of them follows the last version, so that, by `WellFormed.snoc`, each
keeps a history well formed. A revision follows only if its content is
really new: depositing the same content again with a new document version
would break the count, and is excluded by the hypothesis `hnew`.

    theorem sameContent_self (v : Version D) : sameContent v v = true := by
      simp [sameContent]

    theorem describe_follows (last : Version D) (d a m : String) :
        Follows last (last.describe d a m) := by
      simp [Follows, Version.describe, sameContent]

    theorem withdraw_follows (last : Version D) (a m : String) :
        Follows last (last.withdraw a m) := by
      simp [Follows, Version.withdraw, sameContent]

    theorem revise_follows (last : Version D) (fs : List (LogicalPath × D))
        (ms : Option (Members D)) (d a m : String)
        (hnew : sameContent last (last.revise fs ms d a m) = false) :
        Follows last (last.revise fs ms d a m) := by
      simp only [Follows, hnew]
      rfl

Finally, the statement of section 7.3 itself: a description-only version
keeps the document version and the content.

    omit [DecidableEq D] in
    /-- A description-only version keeps the document version and the content. -/
    theorem describe_keeps (last : Version D) (d a m : String) :
        (last.describe d a m).documentVersion = last.documentVersion ∧
        (last.describe d a m).files = last.files ∧
        (last.describe d a m).members = last.members :=
      ⟨rfl, rfl, rfl⟩

    end DocumentVersions

    end OpenSheaf
