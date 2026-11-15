# An object version is a section

An object version, read from its inventory, says what each document
version up to it holds. So it is a section, over the set of named document
versions it holds. This chapter defines that section and proves three
things about it, each a rule of the specification read as a statement about
sections:

- the set it is defined on is open: no gaps in the numbers (section 7.3);
- it is the gluing of its *pieces*, the object versions it lists, each
  saying what one document version holds; the pieces are compatible
  because of the rule of section 7.3, "one number, one content", and a
  history that breaks the rule has pieces that are not;
- a later object version restricts to an earlier one: that versions are
  fixed once deposited (sections 1 and 7.3) is restriction.

## The section of an object version

Object version `n` of an object `o` holds the document versions of the
first `n` object versions: the names of `o` with numbers from 1 to the
highest of them. Its value at a document version is the content of the
first object version that holds it. With the rule of section 7.3 any of
them would do, as the next sections prove; the definition makes no
assumption.

    -- in Sheaf/Object.lean:
    import Sheaf.Base

    namespace OpenSheaf.Sheaf

    variable {D : Type}

    /-- No files, no member list. -/
    def Content.empty : Content D := ⟨fun _ => False, none⟩

    /-- The content a history gives to document version `k`: that of the first
    object version holding it. -/
    def docContent (l : List (Version D)) (k : Nat) : Content D :=
      match l.find? (fun v => v.documentVersion == k) with
      | some v => v.content
      | none => Content.empty

    /-- The named document versions held by object version `n` of `o`. -/
    def Held (o : Obj D) (n : Nat) (x : Name) : Prop :=
      x.archive = o.archive ∧ x.object = o.id ∧ 1 ≤ x.doc ∧
        x.doc ≤ docCount (o.versions.take n)

    instance (o : Obj D) (n : Nat) (x : Name) : Decidable (Held o n x) := by
      unfold Held; infer_instance

    /-- The section of object version `n`. -/
    def objSec (o : Obj D) (n : Nat) : Sec (Held o n) (Content D) :=
      fun x _ => docContent (o.versions.take n) x.doc

The pieces of object version `n` are the object versions up to `n`, each
over the one named document version it holds, with its own content. Two
pieces overlap when they hold the same document version: a description-only
version and the version it describes, for instance.

    /-- The pieces of object version `n`: each object version up to `n`, over
    the named document version it holds. -/
    def piece (o : Obj D) (n : Nat) (i : {v // v ∈ o.versions.take n}) (x : Name) : Prop :=
      x = o.name i.1

    def pieces (o : Obj D) (n : Nat) : ∀ i, Sec (piece o n i) (Content D) :=
      fun i _ _ => i.1.content

## Open sets and immutability

The set held by an object version is closed downwards in the order of
history, whatever the object: it is defined by an upper bound.

    theorem held_open (o : Obj D) (n : Nat) : deposit.IsOpen (Held o n) := by
      intro x y ⟨h1, h2, h3, h4⟩ ⟨k1, k2, k3, k4⟩
      refine ⟨h1.trans k1, h2.trans k2, ?_, Nat.le_trans h3 k4⟩
      cases hy : y.doc with
      | zero => have := h4 hy; omega
      | succ _ => omega

A later object version holds at least what an earlier one holds, since its
history extends the earlier one.

    theorem take_prefix (l : List (Version D)) (n : Nat) : ∃ t, l = l.take n ++ t :=
      ⟨l.drop n, (List.take_append_drop n l).symm⟩

    theorem held_mono {o : Obj D} {m n : Nat} (hmn : m ≤ n) : Sub (Held o m) (Held o n) := by
      rintro x ⟨h1, h2, h3, h4⟩
      refine ⟨h1, h2, h3, Nat.le_trans h4 ?_⟩
      have : o.versions.take m = (o.versions.take n).take m := by
        rw [List.take_take, Nat.min_eq_left hmn]
      rw [this]
      obtain ⟨t, ht⟩ := take_prefix (o.versions.take n) m
      conv => rhs; rw [ht]
      generalize (o.versions.take n).take m = l
      induction l with
      | nil => exact Nat.zero_le _
      | cons v l ih =>
        simp only [docCount, List.cons_append]
        exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans ih (Nat.le_max_right _ _)⟩

## The value is that of any piece

In a history that is well formed, and in any of its prefixes, the value at
a document version is the content of every object version that holds it.
The proof finds an object version holding it (no gaps), then compares it
with the others (one number, one content).

    variable [DecidableEq D]

    theorem docContent_eq {L l t : List (Version D)} (hL : WellFormed L) (hl : L = l ++ t)
        {k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ docCount l) {u : Version D} (hu : u ∈ L)
        (huk : u.documentVersion = k) : docContent l k = u.content := by
      have hwl : WellFormed l := by subst hl; exact hL.prefix
      obtain ⟨v, hv, hvk⟩ := no_gaps hwl hk1 hk
      unfold docContent
      cases hf : l.find? (fun v => v.documentVersion == k) with
      | none =>
        have := List.find?_eq_none.mp hf v hv
        simp [hvk] at this
      | some v' =>
        have hp := List.find?_some hf
        have hm := List.mem_of_find?_eq_some hf
        simp only [beq_iff_eq] at hp
        have hmL : v' ∈ L := by rw [hl]; exact List.mem_append_left _ hm
        exact content_eq_iff.mpr (one_number_one_content hL hmL hu (hp.trans huk.symm))

    /-- The section of an object version restricts to each of its pieces. -/
    theorem objSec_piece {o : Obj D} (hwf : WellFormed o.versions) {n : Nat} {v : Version D}
        (hv : v ∈ o.versions.take n) (hx : Held o n (o.name v)) :
        objSec o n (o.name v) hx = v.content := by
      obtain ⟨t, ht⟩ := take_prefix o.versions n
      exact docContent_eq hwf ht hx.2.2.1 hx.2.2.2 (List.mem_of_mem_take hv) rfl

The set held by an object version is exactly the set of its pieces' names.
One inclusion is that no number is skipped; the other, that the numbers
start at 1.

    /-- The named document versions held by an object version are those of its
    pieces: the numbers from 1 to the last, without gaps. -/
    theorem held_iff {o : Obj D} (hwf : WellFormed o.versions) (n : Nat) (x : Name) :
        Held o n x ↔ ∃ v ∈ o.versions.take n, x = o.name v := by
      obtain ⟨t, ht⟩ := take_prefix o.versions n
      have hw : WellFormed (o.versions.take n) := by rw [ht] at hwf; exact hwf.prefix
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        obtain ⟨v, hv, hvk⟩ := no_gaps hw h3 h4
        refine ⟨v, hv, ?_⟩
        cases x
        simp only [Obj.name] at *
        rw [h1, h2, hvk]
      · rintro ⟨v, hv, rfl⟩
        exact ⟨rfl, rfl, doc_pos hw hv, le_docCount hv⟩

## The pieces glue

The pieces of a well-formed object version are compatible: two object
versions that hold the same document version have the same content. This
is the first half of the rule of section 7.3, which the verifier checks
(section 14: "object versions with the same document version have the same
sources, renditions and change note"). The section of the object version
glues them. So the check of section 14 is the check that an object's own
pieces glue. The chapter [A story](60-story.md) gives a history that breaks
the rule, and whose pieces do not glue.

    /-- **The pieces of a well-formed object version are compatible.** -/
    theorem pieces_compatible {o : Obj D} (hwf : WellFormed o.versions) (n : Nat) :
        Compatible (pieces o n) := by
      intro i j x hi hj
      simp only [pieces]
      have hd : i.1.documentVersion = j.1.documentVersion := by
        have := hi.symm.trans hj
        simp only [Obj.name, Name.mk.injEq] at this
        exact this.2.2
      exact content_eq_iff.mpr (one_number_one_content hwf
        (List.mem_of_mem_take i.2) (List.mem_of_mem_take j.2) hd)

    theorem union_pieces {o : Obj D} (hwf : WellFormed o.versions) (n : Nat) :
        Sub (Union (piece o n)) (Held o n) := by
      rintro x ⟨i, rfl⟩
      exact (held_iff hwf n _).mpr ⟨i.1, i.2, rfl⟩

    /-- **The section of an object version glues its pieces.** -/
    theorem objSec_glues {o : Obj D} (hwf : WellFormed o.versions) (n : Nat) :
        Glues (pieces o n) ((objSec o n).restrict (union_pieces hwf n)) := by
      intro i
      funext x hx
      cases hx
      exact objSec_piece hwf i.2 (union_pieces hwf n _ ⟨i, rfl⟩)

## Immutability is restriction

The section of a later object version, restricted to what an earlier one
holds, is the section of the earlier one. Both take their values from the
pieces, and a later object version only adds pieces. This is how the sheaf
sees immutability: a presheaf whose restriction maps send each object
version to the ones before it.

    /-- **Immutability is restriction.** The section of a later object version
    restricts to that of an earlier one. -/
    theorem objSec_restrict {o : Obj D} (hwf : WellFormed o.versions) {m n : Nat}
        (hmn : m ≤ n) : (objSec o n).restrict (held_mono hmn) = objSec o m := by
      funext x hx
      obtain ⟨v, hv, rfl⟩ := (held_iff hwf m x).mp hx
      have hvn : v ∈ o.versions.take n := by
        have : o.versions.take m = (o.versions.take n).take m := by
          rw [List.take_take, Nat.min_eq_left hmn]
        rw [this] at hv
        exact List.mem_of_mem_take hv
      exact (objSec_piece hwf hvn _).trans (objSec_piece hwf hv _).symm

    end OpenSheaf.Sheaf
