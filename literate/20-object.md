# Objects and their history

An object is the list of its object versions, oldest first (section 4).
This chapter defines objects, their genesis records, versions and
inventories, and the environment that the rest of the model takes as given
(digests, names and signatures); it proves that a history which keeps a
prefix keeps the versions and inventories within it, and gives the rule by
which document versions are counted.

    -- in OpenSheaf/Object.lean:
    import OpenSheaf.Basic

    namespace OpenSheaf

## Genesis records

A work or an owner is named by its **genesis record**, `genesis.json`
(section 5.1): its kind, the date it was written, a random nonce and, for a
work, its `originator`, the owner of the first line; for an owner, instead,
its first current keys and the digests of its first rotation keys, from
which the first version of its key log is computed (section 6.1). The model
keeps the nonce (which stands for the date too), the originator, and the
keys of an owner, as a `Keys` with neither `ended` nor `exposed`. A keeper
and the data of extensions, which an owner's genesis record may also hold,
are left out.

    /-- `genesis.json` (section 5.1): the kind, the nonce, and for a work its
    originator, for an owner its first keys. -/
    structure Genesis (D : Type) where
      kind : Kind
      nonce : String
      originator : OwnerName := ""
      keys : Option (Keys D) := none
      deriving DecidableEq, Repr

## Objects

An object has an identifier, a kind, a genesis record (none for a draft,
section 10.1), its history, and its witness folder, where the signature
files of its versions are kept (section 7.2). Nothing in an object names
the archive that holds it (section 4.3): the same object, a copy of a line,
may be kept by several archives.

    /-- An OCFL object (section 4): its identifier, kind, genesis record (none for
    a draft), versions, and the signature files of its witness folder
    (section 7.2). -/
    structure Obj (D : Type) where
      id : ObjectId
      kind : Kind
      genesis : Option (Genesis D)
      versions : List (Version D)
      sigs : List (Sig D) := []

OCFL writes, with each object version `n`, an inventory describing versions
`1` to `n`, and the pin of version `n` carries the digest of that inventory.
An inventory names its object (OCFL's `id`), and every version holds the
genesis record (section 4.1). The model's inventory is therefore the
identifier and the genesis record of the object together with the prefix
of length `n` of its history, and its digest is a function `hash` of that.
Since the inventory of version `n` describes every version before it, a
pin of version `n` fixes them too, in the model.

In OCFL each version directory keeps its own copy of the inventory of that
version, and an inventory lists the files of earlier versions, not the
bytes of their inventories. Version 0.1 of the specification left those
bytes unfixed, and an earlier version of the model could not tell a copy
whose old inventory files were altered. Version 0.2 closes the gap with the
**inventory chain** (section 4.3, #46): the `object.json` of every sealed
version after the first records `previous`, the digest of the inventory
file before it, so that a pin of version `n` fixes every earlier inventory
byte for byte. The model's inventory, which computes every earlier
inventory from the history, is now exact in this respect.

The signature files are not part of the inventory: they are kept outside
every version, and are not covered by its digests (section 7.2). Since the
inventory names the object, two objects with the same versions, such as a
branch and its parent, have different inventories; and since it names no
archive, every copy of a line has the same inventories as every other copy
holding the same versions.

    /-- What an inventory describes: the object, its genesis record, and its
    versions up to one. -/
    structure Inventory (D : Type) where
      id : ObjectId
      genesis : Option (Genesis D)
      versions : List (Version D)

    /-- A digest function for inventories. -/
    abbrev Hash (D : Type) := Inventory D → D

## The environment

Four things the model takes as given, gathered as its **environment**:

- `hash`, the digest of an inventory (SHA-512, section 4.1);
- `keyDigest`, the digest of a key, which `next` commits to (SHA-256,
  section 6.1);
- `nameOf`, the names of a genesis record: algorithm `k`, for `k` from 0 to
  15, gives one name (section 5.2);
- `verifies`, which signature files verify: those whose signature is a
  valid Ed25519 signature of their message by their key (section 7.2).

`verifies` is the model's abstraction of signing. A signature that verifies
was made by someone holding its key: the model does not say who, and never
assumes that only the owner holds its keys. Theorems about thieves state
which keys made the signatures that verify, as hypotheses on `verifies`.

    /-- The environment: digests of inventories and keys, the names of genesis
    records, and which signature files verify. -/
    structure Env (D : Type) where
      hash : Hash D
      keyDigest : Key → D
      nameOf : Genesis D → Nat → Name
      verifies : Sig D → Bool

Three operations on an object: adding a version at the end, with the
signature files that come with it, finding version `n` (there is no version
0), and the inventory of version `n`.

    namespace Obj

    variable {D : Type}

    /-- Add an object version at the end of the history, and signature files to
    the witness folder. -/
    def append (o : Obj D) (v : Version D) (ss : List (Sig D) := []) : Obj D :=
      { o with versions := o.versions ++ [v], sigs := o.sigs ++ ss }

    /-- Object version `n` (`v1` is `1`), if any. -/
    def versionAt (o : Obj D) (n : Nat) : Option (Version D) :=
      if n = 0 then none else o.versions[n - 1]?

    /-- The inventory of object version `n`: the object, its genesis record, and
    versions `1` to `n`. -/
    def inventory (o : Obj D) (n : Nat) : Inventory D :=
      ⟨o.id, o.genesis, o.versions.take n⟩

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

Every change of a sealed object keeps a prefix of its history: appending a
version keeps the whole history, and a copy holds a prefix of the history
it copies. None changes the identity of the object. The first two lemmas below say that, within the prefix, versions and
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

Version `n` depends only on the first `n` versions: two objects whose
histories agree that far have the same version `n`.

    theorem versionAt_congr_take {o o' : Obj D} {n : Nat}
        (h : o'.versions.take n = o.versions.take n) : o'.versionAt n = o.versionAt n := by
      unfold Obj.versionAt
      split
      · rfl
      · have key : ∀ l : List (Version D), l[n - 1]? = (l.take n)[n - 1]? := by
          intro l; rw [List.getElem?_take]; simp; omega
        rw [key, h, ← key]

    theorem inventory_prefix {o o' : Obj D} {pre t t' : List (Version D)} {n : Nat}
        (hid : o'.id = o.id ∧ o'.genesis = o.genesis)
        (ho : o.versions = pre ++ t) (ho' : o'.versions = pre ++ t')
        (hn : n ≤ pre.length) : o'.inventory n = o.inventory n := by
      unfold Obj.inventory
      rw [hid.1, hid.2, ho, ho', List.take_append_of_le_length hn,
        List.take_append_of_le_length hn]

Four facts about versions by number: a version found at a number is a
version of the object, and one of the versions up to that number; after an
append, a version is an old one or the one appended, at the next number.

    theorem versionAt_mem {o : Obj D} {n : Nat} {v : Version D} (h : o.versionAt n = some v) :
        v ∈ o.versions := by
      unfold Obj.versionAt at h
      split at h
      · contradiction
      · exact List.mem_of_getElem? h

    theorem versionAt_mem_take {o : Obj D} {n : Nat} {v : Version D}
        (h : o.versionAt n = some v) : v ∈ o.versions.take n := by
      unfold Obj.versionAt at h
      split at h
      · contradiction
      · rename_i hn
        have h' : (o.versions.take n)[n - 1]? = some v := by
          rw [List.getElem?_take]; simp [show n - 1 < n by omega, h]
        exact List.mem_of_getElem? h'

    theorem versionAt_append {o : Obj D} {x v : Version D} {ss : List (Sig D)} {n : Nat}
        (h : (o.append x ss).versionAt n = some v) :
        o.versionAt n = some v ∨ (n = o.versions.length + 1 ∧ v = x) := by
      unfold Obj.versionAt Obj.append at *
      split at h
      · contradiction
      · rename_i hn
        simp only [hn, ite_false]
        by_cases hlt : n - 1 < o.versions.length
        · left; rwa [List.getElem?_append_left hlt] at h
        · right
          rw [List.getElem?_append_right (by omega)] at h
          have : n - 1 - o.versions.length = 0 := by
            cases hk : n - 1 - o.versions.length with
            | zero => rfl
            | succ k => rw [hk] at h; simp at h
          rw [this] at h
          simp at h
          exact ⟨by omega, h.symm⟩

After an append, the old versions are where they were, and the new one
comes last.

    theorem append_getElem_last {o : Obj D} {x : Version D} {ss : List (Sig D)} :
        ((o.append x ss).versions[o.versions.length]'(by simp [Obj.append])) = x := by
      simp [Obj.append]

    theorem append_getElem_old {o : Obj D} {x : Version D} {ss : List (Sig D)} {i : Nat}
        (hi : i < o.versions.length) :
        ((o.append x ss).versions[i]'(by simp [Obj.append]; omega)) = o.versions[i] := by
      simp [Obj.append, List.getElem_append_left hi]

    end Prefix

## Document versions

The specification distinguishes object versions, which OCFL counts, from
document versions, which count the changes of the document's own files
(section 4.2): "A new document version is made exactly when the document's
own files change (a file added, changed or removed, the change note
included) ...; an object version holding the same own files as an earlier
document version keeps its number." A collection "makes a new document
version exactly when its member list changes" (section 4.2). This covers a
description-only version, which "MAY hold any document version", and a
withdrawal.

The model follows the rule: a version keeps the number of an earlier
version whose content it holds, and any other version gets a new number.
Content is compared as a set of files, since the order in which files are
listed means nothing, together with the member list, whose order is
authoritative (section 8.2). Version 0.1 of the specification left open the
versions that only remove files or combine files of different earlier
versions ([issue #23](https://github.com/opensheaf/opensheaf.github.io/issues/23)),
and the model chose then what version 0.2 now says: such a version is new.
A file renamed is new content (files are compared by path and digest), and
a version whose content returns to an earlier version's takes the earlier
number. Whether a verifier can decide all this from the files is still
open (#23, section 14.6).

The model does not tell the document's own files (sources, renditions,
change note) from the files of notes, which section 4.2 counts as files of
the document version but not as its own files; see
["Next"](https://github.com/opensheaf/opensheaf-lean#next) in the README.
Every file of the model counts. Two parts of section 4.2 are not modelled:
the completion of a version deposited without its sources, which keeps its
number while adding files, and `history`, which orders document versions
deposited out of order. The model has no `sourcesMissing` and no `history`
yet.

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

    /-- `x` may extend the history `l` (section 4.2). -/
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

The converse of `snoc` takes a well-formed history apart from the end.
Proofs about histories go along it from the end, and Lean's core library
has no induction from the end of a list; it follows from induction on the
reversed list.

    omit [DecidableEq D] in
    theorem snoc_induction {α : Type} {motive : List α → Prop} (nil : motive [])
        (snoc : ∀ l x, motive l → motive (l ++ [x])) (l : List α) : motive l := by
      rw [← List.reverse_reverse l]
      induction l.reverse with
      | nil => exact nil
      | cons x r ih => rw [List.reverse_cons]; exact snoc _ _ ih

    theorem WellFormed.init {l : List (Version D)} {x : Version D}
        (h : WellFormed (l ++ [x])) : WellFormed l ∧ Extends l x := by
      constructor
      · intro i hi
        have := h i (by simp; omega)
        rwa [List.take_append_of_le_length (Nat.le_of_lt hi), List.getElem_append_left hi] at this
      · have := h l.length (by simp)
        simpa using this

More generally, every prefix of a well-formed history is well formed: the
condition on each version looks only at the versions before it.

    theorem WellFormed.prefix {l t : List (Version D)} (h : WellFormed (l ++ t)) :
        WellFormed l := by
      intro i hi
      have := h i (by simp; omega)
      rwa [List.take_append_of_le_length (Nat.le_of_lt hi), List.getElem_append_left hi] at this

Two facts about the count: appending a version takes the maximum, and the
count bounds every document version of the history.

    omit [DecidableEq D] in
    theorem docCount_append (l : List (Version D)) (x : Version D) :
        docCount (l ++ [x]) = max (docCount l) x.documentVersion := by
      induction l with
      | nil => simp [docCount]
      | cons v l ih => simp only [List.cons_append, docCount, ih, Nat.max_assoc]

    omit [DecidableEq D] in
    theorem le_docCount {l : List (Version D)} {v : Version D} (h : v ∈ l) :
        v.documentVersion ≤ docCount l := by
      induction l with
      | nil => cases h
      | cons y l ih =>
        simp only [docCount]
        rcases List.mem_cons.mp h with rfl | h
        · exact Nat.le_max_left _ _
        · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

## Status

The status belongs to the line, read "from its latest signed version
(section 7.3), whatever document version that holds" (section 13.1): a
description of an earlier document version of a withdrawn line does not
make it active again. The model reads it from the last version of a
history; [chapter 5](38-lines.md) says when that version is signed. Whether
a withdrawal can be undone at all, and whether a withdrawn line takes new
document versions, are
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

A history keeps the rule when no version of it reinstates the versions
before it. A history created at once (imported, or copied) is checked as a
whole, and appending a version that keeps the rule keeps it.

    omit [DecidableEq D] in
    /-- No version of the history makes a withdrawn object active again. -/
    def StatusOk (l : List (Version D)) : Prop :=
      ∀ i (h : i < l.length), NoReinstatement (l.take i) l[i]

    omit [DecidableEq D] in
    instance (l : List (Version D)) : Decidable (StatusOk l) := by
      unfold StatusOk; infer_instance

    omit [DecidableEq D] in
    theorem StatusOk.snoc {l : List (Version D)} {x : Version D} (h : StatusOk l)
        (hx : NoReinstatement l x) : StatusOk (l ++ [x]) := by
      intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i < l.length
      · rw [List.take_append_of_le_length (Nat.le_of_lt hlt), List.getElem_append_left hlt]
        exact h i hlt
      · have hi' : i = l.length := by omega
        subst hi'
        simpa using hx

    omit [DecidableEq D] in
    theorem StatusOk.single (x : Version D) : StatusOk [x] := by
      intro i hi
      simp only [List.length_singleton] at hi
      have : i = 0 := by omega
      subst this
      simp [NoReinstatement, headStatus]

## The three kinds of new version

An owner makes new object versions of a document in three ways: a
**description-only version** (section 4.2) changes the description of a
document version, any of them; a **withdrawal** (section 13.1) changes the
status; a **revision** adds new content, and a new document version. Each
is built for the history `l` it extends, and takes the status of its head.

    omit [DecidableEq D] in
    /-- A description-only version (section 4.2) of the history `l`: a new
    description of the content of `v`, with the status of the object. -/
    def Version.describe (l : List (Version D)) (v : Version D)
        (description depositor message : String) : Version D :=
      { v with status := headStatus l, description, depositor, message }

`Version.withdraw` builds a withdrawal as section 13.1 defines it, a
description-only version. The rules do not require it: a version with new
content may also come with status `withdrawn`, which section 13.1 does not
foresee. The model leaves this open, with issue #25.

    omit [DecidableEq D] in
    /-- A withdrawal (section 13.1): the same content, with status `withdrawn`. -/
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

Finally, the statement of section 4.2 itself: a description-only version
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
