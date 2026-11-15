-- Generated from literate-sheaf/72-lifting.md by opensheaf-literate: edit the document, not this file.
import Sheaf.Eternal

namespace OpenSheaf.Sheaf

variable {D : Type}

/-- An object version, named: its archive, its object, and its number. -/
structure VSite where
  archive : ArchiveId
  object : ObjectId
  version : Nat
  deriving DecidableEq, Repr

/-- The order of object versions: earlier versions of the same object. -/
def versions : Order VSite where
  le x y := x.archive = y.archive ∧ x.object = y.object ∧ x.version ≤ y.version ∧
    (x.version = 0 → y.version = 0)
  refl _ := ⟨rfl, rfl, Nat.le_refl _, id⟩
  trans := fun ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩ =>
    ⟨h1.trans h1', h2.trans h2', Nat.le_trans h3 h3', fun h => h4' (h4 h)⟩

/-- The object versions a copy holds. -/
def SiteHeld (c : Obj D) (s : VSite) : Prop :=
  s.archive = c.archive ∧ s.object = c.id ∧ 1 ≤ s.version ∧ s.version ≤ c.versions.length

theorem siteHeld_open (c : Obj D) : versions.IsOpen (SiteHeld c) := by
  intro x y ⟨h1, h2, h3, h4⟩ ⟨k1, k2, k3, k4⟩
  refine ⟨h1.trans k1, h2.trans k2, ?_, Nat.le_trans h3 k4⟩
  cases hy : y.version with
  | zero => have := h4 hy; omega
  | succ _ => omega

/-- The section of a copy: the inventory of each object version it holds. -/
def invSec (c : Obj D) : Sec (SiteHeld c) (Inventory D) := fun s _ => c.inventory s.version

/-- A live copy of a world. -/
structure Copy (w : World D) where
  archive : ArchiveId
  id : ObjectId
  obj : Obj D
  live : lookup w archive id = some (.live obj)

abbrev siteCover (w : World D) (i : Copy w) : VSite → Prop := SiteHeld i.obj
abbrev invSections (w : World D) (i : Copy w) : Sec (siteCover w i) (Inventory D) := invSec i.obj

/-- The object versions held anywhere in a world. -/
def SitesIn (w : World D) : VSite → Prop := Union (siteCover w)

theorem take_comparable {α : Type} {l l' : List α} (h : Comparable l l') {n : Nat}
    (hn : n ≤ l.length) (hn' : n ≤ l'.length) : l.take n = l'.take n := by
  rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [List.take_append_of_le_length hn]
  · rw [List.take_append_of_le_length hn']

/-- **The inventories of a world are compatible**, wherever copies agree. -/
theorem inv_compatible {w : World D} (hca : CopiesAgree w) : Compatible (invSections w) := by
  intro i j s ⟨a1, o1, _, n1⟩ ⟨a2, o2, _, n2⟩
  have hc := hca _ _ _ _ _ _ i.live j.live (a1.symm.trans a2) (o1.symm.trans o2)
  simp only [invSections, invSec, Obj.inventory]
  rw [← a1, ← o1, a2, o2, take_comparable hc n1 n2]

variable [DecidableEq D] (hash : Hash D)

/-- **The inventory sheaf of a world built by events.** -/
theorem inventory_glues {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) :
    ∃ G, Glues (invSections w) G ∧ ∀ G', Glues (invSections w) G' → G' = G :=
  sheaf (inv_compatible (Events.copiesAgree hash hs))

omit [DecidableEq D] in
/-- The digest morphism: a section of inventories gives a section of digests. -/
def digests {U : VSite → Prop} (s : Sec U (Inventory D)) : Sec U D := fun x hx => hash (s x hx)

omit [DecidableEq D] in
/-- It commutes with restriction: it is a morphism of presheaves. -/
theorem digests_restrict {U U' : VSite → Prop} (s : Sec U (Inventory D)) (h : Sub U' U) :
    digests hash (s.restrict h) = (digests hash s).restrict h := rfl

omit [DecidableEq D] in
/-- **Without collisions, it is injective.** -/
theorem digests_injective {U : VSite → Prop} {s s' : Sec U (Inventory D)}
    (hcol : ∀ x hx, NoCollision hash (s x hx) (s' x hx))
    (h : digests hash s = digests hash s') : s = s' := by
  funext x hx
  exact hcol x hx (congrFun (congrFun h x) hx)

/-- The verdict a verifier reaches on a pin from an inventory of its object
version. -/
def verdictOf (i : Inventory D) (p : Pin D) : Resolution D :=
  match i.versions[p.version - 1]? with
  | none => .unavailable
  | some v => if hash i = p.digest then .ok v else .mismatch

/-- Resolving a pin through a copy is reading the verdict off its inventory. -/
theorem resolveEntry_verdict (c : Obj D) (p : Pin D) :
    resolveEntry hash (some (.live c)) p = verdictOf hash (c.inventory p.version) p := by
  unfold resolveEntry verdictOf Obj.versionAt Obj.inventory
  by_cases h0 : p.version = 0
  · simp [h0]
  · have : (c.versions.take p.version)[p.version - 1]? = c.versions[p.version - 1]? := by
      rw [List.getElem?_take]; simp; omega
    simp only [h0, ite_false, this]
    cases c.versions[p.version - 1]? <;> rfl

/-- The site a pin names. -/
def pinSite (p : Pin D) : VSite := ⟨p.archive, p.object, p.version⟩

/-- **Every copy gives the same verdict.** In a world built by events, two
copies that hold the object version a pin names resolve it alike. -/
theorem copies_same_verdict {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) (i j : Copy w) {p : Pin D}
    (hi : SiteHeld i.obj (pinSite p)) (hj : SiteHeld j.obj (pinSite p)) :
    resolveEntry hash (some (.live i.obj)) p = resolveEntry hash (some (.live j.obj)) p := by
  rw [resolveEntry_verdict, resolveEntry_verdict]
  have := inv_compatible (Events.copiesAgree hash hs) i j (pinSite p) hi hj
  simp only [invSections, invSec, pinSite] at this
  rw [this]

/-- **The verdict is the glued section's.** -/
theorem verdict_glue {w : World D} {G : Sec (SitesIn w) (Inventory D)}
    (hG : Glues (invSections w) G) (i : Copy w) {p : Pin D} (hi : SiteHeld i.obj (pinSite p)) :
    resolveEntry hash (some (.live i.obj)) p = verdictOf hash (G (pinSite p) ⟨i, hi⟩) p := by
  rw [resolveEntry_verdict]
  have : G (pinSite p) ⟨i, hi⟩ = i.obj.inventory p.version :=
    congrFun (congrFun (hG i) (pinSite p)) hi
  rw [this]

/-- **A pin lifts exactly when it resolves.** At an object version held in the
world, the verdict is a version exactly when the glued inventory has the
pin's digest: verification is lifting the pin, a point of the digest sheaf,
to the inventory sheaf. -/
theorem lifts_iff {w : World D} {G : Sec (SitesIn w) (Inventory D)}
    (hG : Glues (invSections w) G) (i : Copy w) {p : Pin D} (hi : SiteHeld i.obj (pinSite p)) :
    (∃ u, verdictOf hash (G (pinSite p) ⟨i, hi⟩) p = .ok u) ↔
      digests hash G (pinSite p) ⟨i, hi⟩ = p.digest := by
  have hG' : G (pinSite p) ⟨i, hi⟩ = i.obj.inventory p.version :=
    congrFun (congrFun (hG i) (pinSite p)) hi
  simp only [digests]
  rw [hG']
  obtain ⟨_, _, h1, h2⟩ := hi
  have h1' : 1 ≤ p.version := h1
  have h2' : p.version ≤ i.obj.versions.length := h2
  have hv : ∃ v, (i.obj.inventory p.version).versions[p.version - 1]? = some v := by
    simp only [Obj.inventory]
    rw [List.getElem?_take]
    simp only [show p.version - 1 < p.version by omega, ite_true]
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨v, hv⟩ := hv
  unfold verdictOf
  rw [hv]
  constructor
  · rintro ⟨u, hu⟩
    by_cases hd : hash (i.obj.inventory p.version) = p.digest
    · exact hd
    · simp [hd] at hu
  · intro hd
    exact ⟨v, by simp [hd]⟩

omit [DecidableEq D] in
/-- **The lift is unique.** An inventory with the pin's digest, found anywhere,
is the glued one, unless the two collide. -/
theorem lift_unique {w : World D} {G : Sec (SitesIn w) (Inventory D)} {p : Pin D}
    (hx : SitesIn w (pinSite p)) {inv : Inventory D}
    (hcol : NoCollision hash inv (G (pinSite p) hx)) (h : hash inv = p.digest)
    (hG : digests hash G (pinSite p) hx = p.digest) : inv = G (pinSite p) hx :=
  hcol (h.trans hG.symm)

end OpenSheaf.Sheaf
