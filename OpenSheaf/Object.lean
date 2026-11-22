-- Generated from literate/20-object.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Basic

namespace OpenSheaf

/-- `genesis.json` (section 5.1): the kind, the nonce, and for a work its
originator, for an owner its first keys. -/
structure Genesis (D : Type) where
  kind : Kind
  nonce : String
  originator : OwnerName := ""
  keys : Option (Keys D) := none
  deriving DecidableEq, Repr

/-- An OCFL object (section 4): its identifier, kind, genesis record (none for
a draft), versions, and the signature files of its witness folder
(section 7.2). -/
structure Obj (D : Type) where
  id : ObjectId
  kind : Kind
  genesis : Option (Genesis D)
  versions : List (Version D)
  sigs : List (Sig D) := []

/-- What an inventory describes: the object, its genesis record, and its
versions up to one. -/
structure Inventory (D : Type) where
  id : ObjectId
  genesis : Option (Genesis D)
  versions : List (Version D)

/-- A digest function for inventories. -/
abbrev Hash (D : Type) := Inventory D → D

/-- The environment: digests of inventories and keys, the names of genesis
records, and which signature files verify. -/
structure Env (D : Type) where
  hash : Hash D
  keyDigest : Key → D
  nameOf : Genesis D → Nat → Name
  verifies : Sig D → Bool

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

theorem versionAt_succ (o : Obj D) (n : Nat) : o.versionAt (n + 1) = o.versions[n]? := by
  simp [versionAt]

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

theorem getLast?_take {o : Obj D} {n : Nat} {v : Version D} (h : o.versionAt n = some v) :
    (o.versions.take n).getLast? = some v := by
  obtain ⟨h1, h2⟩ := Obj.versionAt_bounds h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Obj.versionAt_succ] at h
  rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left h2, List.getElem?_take]
  simpa using h

theorem append_getElem_last {o : Obj D} {x : Version D} {ss : List (Sig D)} :
    ((o.append x ss).versions[o.versions.length]'(by simp [Obj.append])) = x := by
  simp [Obj.append]

theorem append_getElem_old {o : Obj D} {x : Version D} {ss : List (Sig D)} {i : Nat}
    (hi : i < o.versions.length) :
    ((o.append x ss).versions[i]'(by simp [Obj.append]; omega)) = o.versions[i] := by
  simp [Obj.append, List.getElem_append_left hi]

end Prefix

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

/-- `x` may extend the history `l` (section 4.2). -/
def Extends (l : List (Version D)) (x : Version D) : Prop :=
  (∃ v ∈ l, sameContent v x = true ∧ x.documentVersion = v.documentVersion) ∨
    ((∀ v ∈ l, v.documentVersion = docCount l → sameContent v x = false) ∧
      x.documentVersion = docCount l + 1)

instance (l : List (Version D)) (x : Version D) : Decidable (Extends l x) := by
  unfold Extends; infer_instance

/-- A well-formed history: each version extends those before it. -/
def WellFormed (l : List (Version D)) : Prop :=
  ∀ i (h : i < l.length), Extends (l.take i) l[i]

instance (l : List (Version D)) : Decidable (WellFormed l) := by
  unfold WellFormed; infer_instance

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

theorem WellFormed.prefix {l t : List (Version D)} (h : WellFormed (l ++ t)) :
    WellFormed l := by
  intro i hi
  have := h i (by simp; omega)
  rwa [List.take_append_of_le_length (Nat.le_of_lt hi), List.getElem_append_left hi] at this

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

/-- The status of the object: that of the head, `active` before any version. -/
def headStatus (l : List (Version D)) : Status :=
  (l.getLast?.map (·.status)).getD .active

/-- The status of `x` follows section 13.1: a new document version is active,
and any other version of a withdrawn object stays withdrawn. -/
def StatusStep (l : List (Version D)) (x : Version D) : Prop :=
  (docCount l < x.documentVersion → x.status = .active) ∧
    (x.documentVersion ≤ docCount l → headStatus l = .withdrawn → x.status = .withdrawn)

instance (l : List (Version D)) (x : Version D) : Decidable (StatusStep l x) := by
  unfold StatusStep; infer_instance

/-- Every version of the history changes the status only as section 13.1 says. -/
def StatusOk (l : List (Version D)) : Prop :=
  ∀ i (h : i < l.length), StatusStep (l.take i) l[i]

instance (l : List (Version D)) : Decidable (StatusOk l) := by
  unfold StatusOk; infer_instance

omit [DecidableEq D] in
theorem StatusOk.snoc {l : List (Version D)} {x : Version D} (h : StatusOk l)
    (hx : StatusStep l x) : StatusOk (l ++ [x]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hlt : i < l.length
  · rw [List.take_append_of_le_length (Nat.le_of_lt hlt), List.getElem_append_left hlt]
    exact h i hlt
  · have hi' : i = l.length := by omega
    subst hi'
    simpa using hx

omit [DecidableEq D] in
theorem StatusOk.single (x : Version D) (hx : 0 < x.documentVersion → x.status = .active) :
    StatusOk [x] := by
  intro i hi
  simp only [List.length_singleton] at hi
  have : i = 0 := by omega
  subst this
  simp only [List.take_zero, List.getElem_singleton, StatusStep, docCount, headStatus,
    List.getLast?_nil, Option.map_none, Option.getD_none]
  exact ⟨hx, fun _ h => by cases h⟩

/-- The branch point of the head of a history, if any. -/
def headParent (l : List (Version D)) : Option (Parent D) := l.getLast?.bind (·.parent)

/-- The references of the head of a history, none before any version. -/
def headRefs (l : List (Version D)) : List (Ref D) := (l.getLast?.map (·.refs)).getD []

/-- A description-only version (section 4.2) of the history `l`: a new
description of the content of `v`, with the status, the branch point and the
references of the head. -/
def Version.describe (l : List (Version D)) (v : Version D)
    (description depositor message : String) : Version D :=
  { v with status := headStatus l, parent := headParent l, refs := headRefs l,
           description := description, depositor := depositor, message := message }

/-- A withdrawal (section 13.1): the same content, with status `withdrawn`. -/
def Version.withdraw (last : Version D) (depositor message : String) : Version D :=
  { last with status := .withdrawn, depositor, message }

/-- A new document version of the history `l`: new content, active (it
reinstates a withdrawn line, section 13.1), with the branch point and the
references of the head. -/
def Version.revise (l : List (Version D)) (files : List (LogicalPath × D))
    (members : Option (Members D)) (description depositor message : String) :
    Version D :=
  { documentVersion := docCount l + 1, files, members, description, refs := headRefs l,
    parent := headParent l, status := .active, depositor, message }

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
    (hnew : ∀ v ∈ l, v.documentVersion = docCount l →
      sameContent v (Version.revise l fs ms d a m) = false) :
    Extends l (Version.revise l fs ms d a m) :=
  Or.inr ⟨hnew, rfl⟩

omit [DecidableEq D] in
theorem describe_statusStep {l : List (Version D)} {v : Version D} (hv : v ∈ l) (d a m : String) :
    StatusStep l (Version.describe l v d a m) :=
  ⟨fun h => absurd (le_docCount hv) (by simp only [Version.describe] at h; omega), fun _ h => h⟩

omit [DecidableEq D] in
theorem withdraw_statusStep {l : List (Version D)} {v : Version D} (hv : v ∈ l) (a m : String) :
    StatusStep l (v.withdraw a m) :=
  ⟨fun h => absurd (le_docCount hv) (by simp only [Version.withdraw] at h; omega), fun _ _ => rfl⟩

omit [DecidableEq D] in
theorem revise_statusStep (l : List (Version D)) (fs : List (LogicalPath × D))
    (ms : Option (Members D)) (d a m : String) :
    StatusStep l (Version.revise l fs ms d a m) :=
  ⟨fun _ => rfl, fun h => by simp only [Version.revise] at h; omega⟩

omit [DecidableEq D] in
/-- A description-only version keeps the document version and the content. -/
theorem describe_keeps (l : List (Version D)) (v : Version D) (d a m : String) :
    (Version.describe l v d a m).documentVersion = v.documentVersion ∧
    (Version.describe l v d a m).files = v.files ∧
    (Version.describe l v d a m).members = v.members :=
  ⟨rfl, rfl, rfl⟩

end DocumentVersions

end OpenSheaf
