# Objects and their history

An object is the list of its object versions, oldest first (section 7). This
chapter defines objects, their versions and inventories, proves that a
history which keeps a prefix keeps the versions and inventories within it,
and gives the rule by which document versions are counted.

    -- in OpenSheaf/Object.lean:
    import OpenSheaf.Basic

    namespace OpenSheaf

## Objects

An object has the archive it belongs to, an identifier, a kind, and its
history. The archive is the one named by `archiveId` in its `object.json`
(section 9): for a mirror, kept by another archive, it is still the
original's (section 10.4).

    /-- An OCFL object of an OpenSheaf archive (section 7). -/
    structure Obj (D : Type) where
      archive : ArchiveId
      id : ObjectId
      kind : Kind
      versions : List (Version D)

OCFL writes, with each object version `n`, an inventory describing versions
`1` to `n`, and the pin of version `n` carries the digest of that inventory.
An inventory also names its object (OCFL's `id`), and the `object.json` of
each version names the archive and the object (section 9). The model's
inventory is therefore the identity of the object together with the prefix
of length `n` of its history, and its digest is a function `hash` of that.
Since the inventory of version `n` describes all the versions before it, a
pin of version `n` fixes them too. Since it names the object, two objects
with the same versions, such as an accepted copy deposited with the
original's description, still have different inventories.

    /-- What an inventory describes: the object, and its versions up to one. -/
    structure Inventory (D : Type) where
      archive : ArchiveId
      id : ObjectId
      versions : List (Version D)

    /-- A digest function for inventories. -/
    abbrev Hash (D : Type) := Inventory D → D

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

    /-- The inventory of object version `n`: the object, and versions `1` to `n`. -/
    def inventory (o : Obj D) (n : Nat) : Inventory D :=
      ⟨o.archive, o.id, o.versions.take n⟩

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
keeps the whole history, and rewriting drafts ([chapter 8](50-states.md))
keeps the versions before the drafts. Neither changes the identity of the
object. The two lemmas below say that, within the prefix, versions and
inventories are unchanged. They hold whatever the digest function, since
they are about the versions themselves; this is the heart of every
immutability result of the model.

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
        (hid : o'.archive = o.archive ∧ o'.id = o.id)
        (ho : o.versions = pre ++ t) (ho' : o'.versions = pre ++ t')
        (hn : n ≤ pre.length) : o'.inventory n = o.inventory n := by
      unfold Obj.inventory
      rw [hid.1, hid.2, ho, ho', List.take_append_of_le_length hn,
        List.take_append_of_le_length hn]

    end Prefix

## Document versions

The specification distinguishes object versions, which OCFL counts, from
document versions, which count the changes of the content (section 7.3). Its
rule: "a new document version number is assigned exactly when files ... that
were not deposited before are added", and "an object version holding the
same sources, renditions and change note as an earlier document version
keeps its number". This covers a description-only version, which "MAY hold
any document version, not only the current one", and a withdrawal.

The rule does not say what happens to a version that only removes files,
or that combines files of different earlier versions: it adds no new file,
yet holds no earlier version's content. This is
[issue #23](https://github.com/opensheaf/opensheaf.github.io/issues/23) of
the specification, still open. **The model makes a choice**, to be revised
when the issue is settled: a version keeps the number of an earlier version
whose content it holds, and any other version gets a new number. Content is
compared as a set of files, since the order in which files are listed means
nothing, together with the member list, whose order is authoritative
(section 10.2).

Two parts of section 7.3 are not modelled: the completion of a version
deposited without its sources, which keeps its number while adding files,
and `history`, which orders document versions deposited out of order. The
model has no `sourcesMissing` and no `history` yet.

    section DocumentVersions

    variable {D : Type} [DecidableEq D]

    /-- Two lists of files hold the same files. -/
    def sameFiles (a b : List (LogicalPath × D)) : Bool :=
      a.all (· ∈ b) && b.all (· ∈ a)

    theorem sameFiles_iff {a b : List (LogicalPath × D)} :
        sameFiles a b = true ↔ ∀ f, f ∈ a ↔ f ∈ b := by
      simp only [sameFiles, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2⟩ f; exact ⟨h1 f, h2 f⟩
      · intro h; exact ⟨fun f => (h f).1, fun f => (h f).2⟩

    /-- Two object versions have the same content. -/
    def sameContent (v w : Version D) : Bool :=
      sameFiles v.files w.files && v.members == w.members

    theorem sameContent_iff {v u : Version D} :
        sameContent v u = true ↔ (∀ f, f ∈ v.files ↔ f ∈ u.files) ∧ v.members = u.members := by
      simp [sameContent, sameFiles_iff]

    /-- The highest document version of a history. -/
    def docCount : List (Version D) → Nat
      | [] => 0
      | v :: l => max v.documentVersion (docCount l)

A new object version `x` may extend a history `l` in two ways: it holds the
content of an earlier version, and has its document version; or its content
is new, and its document version is the next number.

    /-- `x` may extend the history `l` (section 7.3, with the choice above). -/
    def Extends (l : List (Version D)) (x : Version D) : Prop :=
      (∃ v ∈ l, sameContent v x = true ∧ x.documentVersion = v.documentVersion) ∨
        ((∀ v ∈ l, sameContent v x = false) ∧ x.documentVersion = docCount l + 1)

    instance (l : List (Version D)) (x : Version D) : Decidable (Extends l x) := by
      unfold Extends; infer_instance

A history is well formed when each version extends the versions before it.
The first version has new content, so it is document version 1.

    /-- A well-formed history: each version extends those before it. -/
    def WellFormed (l : List (Version D)) : Prop :=
      ∀ i (h : i < l.length), Extends (l.take i) l[i]

    instance (l : List (Version D)) : Decidable (WellFormed l) := by
      unfold WellFormed; infer_instance

Appending a version that extends the history keeps it well formed: the
versions before it see the same prefixes as before.

    /-- Appending a version that extends the history keeps it well formed. -/
    theorem WellFormed.snoc {l : List (Version D)} {x : Version D} (h : WellFormed l)
        (hx : Extends l x) : WellFormed (l ++ [x]) := by
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

## Status

The status belongs to the object, "whatever document version its head
holds" (section 11.1): a description of an earlier document version of a
withdrawn object does not make it active again. Whether a withdrawal can be
undone at all is
[issue #25](https://github.com/opensheaf/opensheaf.github.io/issues/25) of
the specification, still open. **The model makes a choice**: it cannot. A
new version has the status of the head, or `withdrawn`.

    omit [DecidableEq D] in
    /-- The status of the object: that of the head, `active` before any version. -/
    def headStatus (l : List (Version D)) : Status :=
      (l.getLast?.map (·.status)).getD .active

    omit [DecidableEq D] in
    /-- `x` does not make a withdrawn object active again. -/
    def NoReinstatement (l : List (Version D)) (x : Version D) : Prop :=
      headStatus l = .withdrawn → x.status = .withdrawn

    instance (l : List (Version D)) (x : Version D) : Decidable (NoReinstatement l x) := by
      unfold NoReinstatement; infer_instance

## The three kinds of new version

An author's archive makes new object versions in three ways: a
**description-only version** (section 7.3) changes the description of a
document version, any of them; a **withdrawal** (section 11.1) changes the
status; a **revision** adds new content, and a new document version. Each
is built for the history `l` it extends, and takes the status of its head.

    omit [DecidableEq D] in
    /-- A description-only version (section 7.3) of the history `l`: a new
    description of the content of `v`, with the status of the object. -/
    def Version.describe (l : List (Version D)) (v : Version D)
        (description depositor message : String) : Version D :=
      { v with status := headStatus l, description, depositor, message }

    omit [DecidableEq D] in
    /-- A withdrawal (section 11.1): the same content, with status `withdrawn`. -/
    def Version.withdraw (last : Version D) (depositor message : String) : Version D :=
      { last with status := .withdrawn, depositor, message }

    /-- A new document version of the history `l`: new content. -/
    def Version.revise (l : List (Version D)) (files : List (LogicalPath × D))
        (members : Option (Members D)) (description depositor message : String) :
        Version D :=
      { documentVersion := docCount l + 1, files, members, description,
        status := headStatus l, depositor, message }

Each extends the history it is added to: a description or a withdrawal of
any version of the history, since it holds that version's content; a
revision, if its content is really new. Depositing the same content again
as a revision would break the count, and is excluded by the hypothesis
`hnew`. None of them makes a withdrawn object active.

    theorem sameContent_self (v : Version D) : sameContent v v = true := by
      simp [sameContent_iff]

    theorem describe_extends {l : List (Version D)} {v : Version D} (hv : v ∈ l)
        (d a m : String) : Extends l (Version.describe l v d a m) :=
      Or.inl ⟨v, hv, by simp [sameContent_iff, Version.describe], rfl⟩

    theorem withdraw_extends {l : List (Version D)} {v : Version D} (hv : v ∈ l)
        (a m : String) : Extends l (v.withdraw a m) :=
      Or.inl ⟨v, hv, by simp [sameContent_iff, Version.withdraw], rfl⟩

    theorem revise_extends (l : List (Version D)) (fs : List (LogicalPath × D))
        (ms : Option (Members D)) (d a m : String)
        (hnew : ∀ v ∈ l, sameContent v (Version.revise l fs ms d a m) = false) :
        Extends l (Version.revise l fs ms d a m) :=
      Or.inr ⟨hnew, rfl⟩

    omit [DecidableEq D] in
    theorem describe_noReinstatement (l : List (Version D)) (v : Version D) (d a m : String) :
        NoReinstatement l (Version.describe l v d a m) := fun h => h

    omit [DecidableEq D] in
    theorem withdraw_noReinstatement (l : List (Version D)) (v : Version D) (a m : String) :
        NoReinstatement l (v.withdraw a m) := fun _ => rfl

    omit [DecidableEq D] in
    theorem revise_noReinstatement (l : List (Version D)) (fs : List (LogicalPath × D))
        (ms : Option (Members D)) (d a m : String) :
        NoReinstatement l (Version.revise l fs ms d a m) := fun h => h

Finally, the statement of section 7.3 itself: a description-only version
keeps the document version and the content of the version it describes.

    omit [DecidableEq D] in
    /-- A description-only version keeps the document version and the content. -/
    theorem describe_keeps (l : List (Version D)) (v : Version D) (d a m : String) :
        (Version.describe l v d a m).documentVersion = v.documentVersion ∧
        (Version.describe l v d a m).files = v.files ∧
        (Version.describe l v d a m).members = v.members :=
      ⟨rfl, rfl, rfl⟩

    end DocumentVersions

    end OpenSheaf
