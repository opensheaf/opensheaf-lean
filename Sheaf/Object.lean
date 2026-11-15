-- Generated from literate-sheaf/30-object.md by opensheaf-literate: edit the document, not this file.
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
def Covers (o : Obj D) (n : Nat) (x : Name) : Prop :=
  x.archive = o.archive ∧ x.object = o.id ∧ 1 ≤ x.doc ∧
    x.doc ≤ docCount (o.versions.take n)

instance (o : Obj D) (n : Nat) (x : Name) : Decidable (Covers o n x) := by
  unfold Covers; infer_instance

/-- The section of object version `n`. -/
def objSec (o : Obj D) (n : Nat) : Sec (Covers o n) (Content D) :=
  fun x _ => docContent (o.versions.take n) x.doc

/-- The pieces of object version `n`: each object version up to `n`, over
the named document version it holds. -/
def piece (o : Obj D) (n : Nat) (i : {v // v ∈ o.versions.take n}) (x : Name) : Prop :=
  x = o.name i.1

def pieces (o : Obj D) (n : Nat) : ∀ i, Sec (piece o n i) (Content D) :=
  fun i _ _ => i.1.content

theorem covers_open (o : Obj D) (n : Nat) : deposit.IsOpen (Covers o n) := by
  intro x y ⟨h1, h2, h3, h4⟩ ⟨k1, k2, k3, k4⟩
  refine ⟨h1.trans k1, h2.trans k2, ?_, Nat.le_trans h3 k4⟩
  cases hy : y.doc with
  | zero => have := h4 hy; omega
  | succ _ => omega

theorem take_prefix (l : List (Version D)) (n : Nat) : ∃ t, l = l.take n ++ t :=
  ⟨l.drop n, (List.take_append_drop n l).symm⟩

theorem docCount_take_mono (l : List (Version D)) {m n : Nat} (hmn : m ≤ n) :
    docCount (l.take m) ≤ docCount (l.take n) := by
  have : l.take m = (l.take n).take m := by
    rw [List.take_take, Nat.min_eq_left hmn]
  rw [this]
  obtain ⟨t, ht⟩ := take_prefix (l.take n) m
  conv => rhs; rw [ht]
  generalize (l.take n).take m = l'
  induction l' with
  | nil => exact Nat.zero_le _
  | cons v l' ih =>
    simp only [docCount, List.cons_append]
    exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans ih (Nat.le_max_right _ _)⟩

theorem covers_mono {o : Obj D} {m n : Nat} (hmn : m ≤ n) : Sub (Covers o m) (Covers o n) := by
  rintro x ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, Nat.le_trans h4 (docCount_take_mono o.versions hmn)⟩

/-- The highest named document version deposited up to object version `n`. -/
def top (o : Obj D) (n : Nat) : Name := ⟨o.archive, o.id, docCount (o.versions.take n)⟩

/-- **The open set of an object version is principal**, below its top. -/
theorem covers_principal (o : Obj D) (n : Nat) (h : 1 ≤ docCount (o.versions.take n))
    (x : Name) : Covers o n x ↔ deposit.le x (top o n) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h4, fun h0 => absurd h0 (by omega)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, ?_, h3⟩
    cases hx : x.doc with
    | zero => have := h4 hx; simp only [top] at this; omega
    | succ _ => omega

theorem top_mono (o : Obj D) {m n : Nat} (hmn : m ≤ n) (h : 1 ≤ docCount (o.versions.take m)) :
    deposit.le (top o m) (top o n) := by
  have := docCount_take_mono o.versions hmn
  exact ⟨rfl, rfl, this, fun h0 => absurd h0 (by simp only [top]; omega)⟩

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
    (hv : v ∈ o.versions.take n) (hx : Covers o n (o.name v)) :
    objSec o n (o.name v) hx = v.content := by
  obtain ⟨t, ht⟩ := take_prefix o.versions n
  exact docContent_eq hwf ht hx.2.2.1 hx.2.2.2 (List.mem_of_mem_take hv) rfl

/-- The named document versions held by an object version are those of its
pieces: the numbers from 1 to the last, without gaps. -/
theorem covers_iff {o : Obj D} (hwf : WellFormed o.versions) (n : Nat) (x : Name) :
    Covers o n x ↔ ∃ v ∈ o.versions.take n, x = o.name v := by
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
    Sub (Union (piece o n)) (Covers o n) := by
  rintro x ⟨i, rfl⟩
  exact (covers_iff hwf n _).mpr ⟨i.1, i.2, rfl⟩

/-- **The section of an object version glues its pieces.** -/
theorem objSec_glues {o : Obj D} (hwf : WellFormed o.versions) (n : Nat) :
    Glues (pieces o n) ((objSec o n).restrict (union_pieces hwf n)) := by
  intro i
  funext x hx
  cases hx
  exact objSec_piece hwf i.2 (union_pieces hwf n _ ⟨i, rfl⟩)

/-- **A later object version restricts to an earlier one** of the same
history. -/
theorem objSec_restrict {o : Obj D} (hwf : WellFormed o.versions) {m n : Nat}
    (hmn : m ≤ n) : (objSec o n).restrict (covers_mono hmn) = objSec o m := by
  funext x hx
  obtain ⟨v, hv, rfl⟩ := (covers_iff hwf m x).mp hx
  have hvn : v ∈ o.versions.take n := by
    have : o.versions.take m = (o.versions.take n).take m := by
      rw [List.take_take, Nat.min_eq_left hmn]
    rw [this] at hv
    exact List.mem_of_mem_take hv
  exact (objSec_piece hwf hvn _).trans (objSec_piece hwf hv _).symm

end OpenSheaf.Sheaf
