-- Generated from literate-sheaf/10-order.md by opensheaf-literate: edit the document, not this file.
namespace OpenSheaf.Sheaf

/-- A preorder on a set of points. -/
structure Order (P : Type) where
  le : P → P → Prop
  refl : ∀ x, le x x
  trans : ∀ {x y z}, le x y → le y z → le x z

variable {P : Type} {V : Type}

/-- An open set of the Alexandrov topology: a set closed downwards. -/
def Order.IsOpen (O : Order P) (U : P → Prop) : Prop :=
  ∀ {x y}, O.le y x → U x → U y

/-- A section over `U`: a value at each point of `U`. -/
def Sec (U : P → Prop) (V : Type) : Type := ∀ x, U x → V

/-- `U'` is contained in `U`. -/
def Sub (U' U : P → Prop) : Prop := ∀ x, U' x → U x

/-- Restriction of a section to a smaller set. -/
def Sec.restrict {U U' : P → Prop} (s : Sec U V) (h : Sub U' U) : Sec U' V :=
  fun x hx => s x (h x hx)

theorem Sec.restrict_id {U : P → Prop} (s : Sec U V) : s.restrict (fun _ h => h) = s := rfl

theorem Sec.restrict_restrict {U U' U'' : P → Prop} (s : Sec U V) (h : Sub U' U)
    (h' : Sub U'' U') : (s.restrict h).restrict h' = s.restrict (fun x hx => h x (h' x hx)) :=
  rfl

/-- The union of a family of sets. -/
def Union {ι : Type} (U : ι → P → Prop) : P → Prop := fun x => ∃ i, U i x

theorem sub_union {ι : Type} (U : ι → P → Prop) (i : ι) : Sub (U i) (Union U) :=
  fun _ h => ⟨i, h⟩

theorem Order.union_open (O : Order P) {ι : Type} {U : ι → P → Prop}
    (h : ∀ i, O.IsOpen (U i)) : O.IsOpen (Union U) :=
  fun hle ⟨i, hx⟩ => ⟨i, h i hle hx⟩

/-- A compatible family: sections that agree wherever two of them are defined. -/
def Compatible {ι : Type} {U : ι → P → Prop} (s : ∀ i, Sec (U i) V) : Prop :=
  ∀ i j x (hi : U i x) (hj : U j x), s i x hi = s j x hj

/-- `g` glues the family `s`: it restricts to each of them. -/
def Glues {ι : Type} {U : ι → P → Prop} (s : ∀ i, Sec (U i) V) (g : Sec (Union U) V) :
    Prop :=
  ∀ i, g.restrict (sub_union U i) = s i

/-- **Locality.** Two sections over a union that agree on every member of the
cover are equal. -/
theorem locality {ι : Type} {U : ι → P → Prop} {g g' : Sec (Union U) V}
    (h : ∀ i, g.restrict (sub_union U i) = g'.restrict (sub_union U i)) : g = g' := by
  funext x ⟨i, hx⟩
  exact congrFun (congrFun (h i) x) hx

/-- **Gluing.** A compatible family glues into a section over the union. -/
theorem gluing {ι : Type} {U : ι → P → Prop} {s : ∀ i, Sec (U i) V}
    (hc : Compatible s) : ∃ g, Glues s g := by
  refine ⟨fun x hx => s (Classical.choose hx) x (Classical.choose_spec hx), ?_⟩
  intro i
  funext x hx
  exact hc _ i x _ hx

/-- **The sheaf condition.** A compatible family glues into exactly one section. -/
theorem sheaf {ι : Type} {U : ι → P → Prop} {s : ∀ i, Sec (U i) V}
    (hc : Compatible s) : ∃ g, Glues s g ∧ ∀ g', Glues s g' → g' = g := by
  obtain ⟨g, hg⟩ := gluing hc
  exact ⟨g, hg, fun g' hg' => locality fun i => (hg' i).trans (hg i).symm⟩

/-- Only a compatible family glues. -/
theorem compatible_of_glues {ι : Type} {U : ι → P → Prop} {s : ∀ i, Sec (U i) V}
    {g : Sec (Union U) V} (hg : Glues s g) : Compatible s := by
  intro i j x hi hj
  rw [← hg i, ← hg j]
  rfl

/-- A condition on the values below a point. -/
def LocalCond (O : Order P) (V : Type) : Type := ∀ x, (∀ y, O.le y x → V) → Prop

/-- A section over an open set satisfies a local condition at every point. -/
def Sec.Satisfies (O : Order P) {U : P → Prop} (hU : O.IsOpen U) (C : LocalCond O V)
    (s : Sec U V) : Prop :=
  ∀ x (hx : U x), C x (fun y hy => s y (hU hy hx))

/-- **Local conditions glue.** A section over a union of open sets satisfies a
local condition if each member of a compatible family it glues does. -/
theorem glue_satisfies (O : Order P) {ι : Type} {U : ι → P → Prop}
    (hU : ∀ i, O.IsOpen (U i)) {s : ∀ i, Sec (U i) V} {g : Sec (Union U) V}
    (hg : Glues s g) (C : LocalCond O V) (hs : ∀ i, (s i).Satisfies O (hU i) C) :
    g.Satisfies O (O.union_open hU) C := by
  intro x ⟨i, hx⟩
  have key : (fun y (hy : O.le y x) => g y (O.union_open hU hy ⟨i, hx⟩)) =
      fun y hy => s i y (hU i hy hx) := by
    funext y hy
    exact congrFun (congrFun (hg i) y) (hU i hy hx)
  rw [key]
  exact hs i x hx

/-- Local conditions restrict: a section satisfying one satisfies it on every
smaller open set. -/
theorem restrict_satisfies (O : Order P) {U U' : P → Prop} (hU : O.IsOpen U)
    (hU' : O.IsOpen U') (h : Sub U' U) (C : LocalCond O V) {s : Sec U V}
    (hs : s.Satisfies O hU C) : (s.restrict h).Satisfies O hU' C :=
  fun x hx => hs x (h x hx)

end OpenSheaf.Sheaf
