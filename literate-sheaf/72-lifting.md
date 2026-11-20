# Verification is lifting

A pin does not name a document version. It names an object version, with
the digest of its inventory. This chapter reads pins and their verification
on a second base, the object versions, with two sheaves on it:

- the **inventories**: at each object version, its inventory (the object,
  and its versions up to that one);
- the **digests**: at each object version, a digest.

Hashing every inventory is a morphism from the first to the second. A pin
is a point of the second: an object version, and a digest. To verify a pin
is to *lift* it: to find, in the world, the inventory at that object
version, and to check that it hashes to the pin's digest. The chapter
proves:

- the inventories of every copy in a world built by events glue into one
  section of the inventory sheaf, when owners are honest and the copies of
  a line share their genesis record (`inventory_glues`);
- the digest morphism is injective wherever the inventories it compares do
  not collide, so a lift is unique when it exists (`digests_injective`,
  `lift_unique`); the model does not assume the digest function injective,
  so this is a statement about given sections, not a monomorphism of
  sheaves;
- **every copy gives the same verdict**: two copies holding the object
  version a pin names resolve it alike, whether to a version or to a
  mismatch (`copies_same_verdict`); the verdict is read off the glued
  section (`verdict_glue`);
- a pin resolves exactly when it lifts (`lifts_iff`).

Section 8.5 of the specification says that "any copy whose bytes match the
pin will do". The theorems here add that, in a world built by events, the
copies that hold the object version a pin names cannot disagree on it, when
owners are honest: a mismatch through one of them is a mismatch through all
of them. A copy that does not hold that version yet, a mirror lagging
behind, reports it unavailable.

The inventory at an object version is computed from the history, as in the
model. In version 0.1 of the specification the bytes of earlier inventory
files were not fixed by a later pin, and the theorems rested on that
abstraction; version 0.2 fixes them by the inventory chain, `previous`
(section 4.3, #46), so the abstraction is now exact.

An inventory also holds the genesis record (section 4.1). Two copies of a
line agree on their histories when the owner signs one history; that they
hold the same genesis record is another matter. A line's name is a digest
of its genesis record (section 5.2), and the model checks it when a copy is
written (`IdentityOk`) and keeps it as an invariant, so two copies of one
line with different genesis records need two records with a name in
common: a collision. In a world built by events, the copies of a line hold
one genesis record unless the names of two records collide
(`Events.genesis_agree_of_names`, in the model, under a hypothesis on the
names of the two records). Honest owners give it with no hypothesis on
names: a copy that does not collide with its owner's history holds the
genesis record of that history (the model's `Events.genesis_history`),
whence `Events.genesisAgree_of_honest` below. The general lemmas below take
it as `GenesisAgree`, and the theorems about worlds built by events derive
it.

    -- in Sheaf/Lifting.lean:
    import Sheaf.Eternal

    namespace OpenSheaf.Sheaf

    variable {D : Type}

## The base and the inventory sheaf

An object version is named by its object, a line, and its number, as a pin
names it, wherever it is kept. The order is that of the versions of one
object, with number 0 kept apart as for named document versions.

    /-- An object version, named: its object and its number. -/
    structure VSite where
      object : ObjectId
      version : Nat
      deriving DecidableEq, Repr

    /-- The order of object versions: earlier versions of the same object. -/
    def objOrder : Order VSite where
      le x y := x.object = y.object ∧ x.version ≤ y.version ∧ (x.version = 0 → y.version = 0)
      refl _ := ⟨rfl, Nat.le_refl _, id⟩
      trans := fun ⟨h2, h3, h4⟩ ⟨h2', h3', h4'⟩ =>
        ⟨h2.trans h2', Nat.le_trans h3 h3', fun h => h4' (h4 h)⟩

A copy holds its object versions, from 1 to its last, and gives each the
inventory of that version. The sets held are open.

    /-- The object versions a copy holds. -/
    def SiteHeld (c : Obj D) (s : VSite) : Prop :=
      s.object = c.id ∧ 1 ≤ s.version ∧ s.version ≤ c.versions.length

    theorem siteHeld_open (c : Obj D) : objOrder.IsOpen (SiteHeld c) := by
      intro x y ⟨h2, h3, h4⟩ ⟨k2, k3, k4⟩
      refine ⟨h2.trans k2, ?_, Nat.le_trans h3 k4⟩
      cases hy : y.version with
      | zero => have := h4 hy; omega
      | succ _ => omega

    /-- The section of a copy: the inventory of each object version it holds. -/
    def invSec (c : Obj D) : Sec (SiteHeld c) (Inventory D) := fun s _ => c.inventory s.version

The live copies of lines of a world, key logs apart, give a family of
sections of the inventory sheaf.

    /-- A live copy of a line of a world, not a key log. -/
    structure Copy (w : World D) where
      archive : ArchiveId
      line : LineId
      obj : Obj D
      live : lookup w archive (.line line) = some (.live obj)
      kind : obj.kind ≠ .owner

    /-- The object versions a copy of a world holds. -/
    abbrev siteCover (w : World D) (i : Copy w) : VSite → Prop := SiteHeld i.obj

    /-- The section of inventories a copy of a world gives (sections 4.1 and 4.3). -/
    abbrev invSections (w : World D) (i : Copy w) : Sec (siteCover w i) (Inventory D) := invSec i.obj

    /-- The object versions held anywhere in a world. -/
    def SitesIn (w : World D) : VSite → Prop := Union (siteCover w)

Two copies of the same line, with comparable histories and the same genesis
record, have the same inventory at every object version both hold: the
inventory of version `n` lists versions 1 to `n`, which the two histories
share.

    theorem take_comparable {α : Type} {l l' : List α} (h : Comparable l l') {n : Nat}
        (hn : n ≤ l.length) (hn' : n ≤ l'.length) : l.take n = l'.take n := by
      rcases h with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · rw [List.take_append_of_le_length hn]
      · rw [List.take_append_of_le_length hn']

    variable [DecidableEq D] (E : Env D)

    /-- The copies of each line, key logs apart, hold the same genesis record. -/
    def GenesisAgree (w : World D) : Prop :=
      ∀ b b' l o o', lookup w b (.line l) = some (.live o) → lookup w b' (.line l) = some (.live o') →
        o.kind ≠ .owner → o'.kind ≠ .owner → o.genesis = o'.genesis

    /-- In a world built by events with honest owners, copies of a line hold one
    genesis record. -/
    theorem Events.genesisAgree_of_honest {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {H : Histories D}
        (hh : Honest E H w) : GenesisAgree w :=
      fun _ _ l _ _ hl hl' hk hk' =>
        (Events.genesis_history E hs (hh.1 l) (hh.2 l) hl hk).trans
          (Events.genesis_history E hs (hh.1 l) (hh.2 l) hl' hk').symm

    /-- **The inventories of a world are compatible**, wherever copies agree. -/
    theorem inv_compatible {w : World D} (hwf : WFObjects w) (hca : ∀ l, CopiesAgree w l)
        (hg : GenesisAgree w) : Compatible (invSections w) := by
      intro i j s ⟨o1, _, n1⟩ ⟨o2, _, n2⟩
      have hl : i.line = j.line := by
        have h1 := (hwf _ _ _ i.live).1
        have h2 := (hwf _ _ _ j.live).1
        exact ObjectId.line.inj (h1.symm.trans (o1.symm.trans (o2.trans h2)))
      have hjl := j.live
      rw [← hl] at hjl
      have hc := hca i.line _ _ _ _ i.live hjl i.kind j.kind
      have hge := hg _ _ _ _ _ i.live hjl i.kind j.kind
      simp only [invSections, invSec, Obj.inventory]
      rw [← o1, o2, hge, take_comparable hc n1 n2]

In a world built by events, copies agree when owners are honest (the
model's `Events.copiesAgree`), so the inventories glue.

    /-- **The inventory sheaf of a world built by events.** -/
    theorem inventory_glues {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {H : Histories D}
        (hh : Honest E H w) :
        ∃ G, Glues (invSections w) G ∧ ∀ G', Glues (invSections w) G' → G' = G :=
      sheaf (inv_compatible (SoundWorld.wfObjects E (Events.sound E hs))
        (fun l => Events.copiesAgree E hs (hh.one E l)) (Events.genesisAgree_of_honest E hs hh))

## The digest morphism

Hashing each inventory turns a section of inventories into a section of
digests, and commutes with restriction: it is a morphism of presheaves.
Where the inventories do not collide it is injective: two sections of
inventories with the same digests, and no collision between them, are
equal. This, like `lift_unique` below, restates the hypothesis; it is
recorded to name the step.

    /-- The digest morphism: a section of inventories gives a section of digests. -/
    def digests {U : VSite → Prop} (s : Sec U (Inventory D)) : Sec U D := fun x hx => E.hash (s x hx)

    omit [DecidableEq D] in
    /-- It commutes with restriction: it is a morphism of presheaves. -/
    theorem digests_restrict {U U' : VSite → Prop} (s : Sec U (Inventory D)) (h : Sub U' U) :
        digests E (s.restrict h) = (digests E s).restrict h := rfl

    omit [DecidableEq D] in
    /-- **Without collisions, it is injective.** -/
    theorem digests_injective {U : VSite → Prop} {s s' : Sec U (Inventory D)}
        (hcol : ∀ x hx, NoCollision E (s x hx) (s' x hx))
        (h : digests E s = digests E s') : s = s' := by
      funext x hx
      exact hcol x hx (congrFun (congrFun h x) hx)

## The verdict

A verifier reads its verdict on a pin off an inventory of the object
version the pin names: the version, if the inventory has it and its digest
is the pin's; a mismatch if the digests differ; unavailable if the
inventory has no such version. There is no version 0 (OCFL numbers
versions from `v1`), so a pin of version 0 is unavailable, whatever the
inventory. Resolving a pin through a copy is exactly this, applied to the
copy's inventory.

    /-- The verdict a verifier reaches on a pin from an inventory of its object
    version. -/
    def verdictOf (i : Inventory D) (p : Pin D) : Resolution D :=
      if p.version = 0 then .unavailable
      else match i.versions[p.version - 1]? with
        | none => .unavailable
        | some v => if E.hash i = p.digest then .ok v else .mismatch

    /-- Resolving a pin through a copy is reading the verdict off its inventory. -/
    theorem resolveEntry_verdict (c : Obj D) (p : Pin D) :
        resolveEntry E.hash (some (.live c)) p = verdictOf E (c.inventory p.version) p := by
      unfold resolveEntry verdictOf Obj.versionAt Obj.inventory
      by_cases h0 : p.version = 0
      · simp [h0]
      · have : (c.versions.take p.version)[p.version - 1]? = c.versions[p.version - 1]? := by
          rw [List.getElem?_take]; simp; omega
        simp only [h0, ite_false, this]
        cases c.versions[p.version - 1]? <;> rfl

Two copies that hold the object version a pin names give the same
verdict, because their inventories there are the same: the verdict is a
function of the glued section, not of the copy it is read from.

    /-- The site a pin names. -/
    def pinSite (p : Pin D) : VSite := ⟨.line p.line, p.version⟩

    /-- **Every copy gives the same verdict.** In a world built by events, two
    copies that hold the object version a pin names resolve it alike. -/
    theorem copies_same_verdict {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {H : Histories D}
        (hh : Honest E H w) (i j : Copy w) {p : Pin D}
        (hi : SiteHeld i.obj (pinSite p)) (hj : SiteHeld j.obj (pinSite p)) :
        resolveEntry E.hash (some (.live i.obj)) p = resolveEntry E.hash (some (.live j.obj)) p := by
      rw [resolveEntry_verdict, resolveEntry_verdict]
      have := inv_compatible (SoundWorld.wfObjects E (Events.sound E hs))
        (fun l => Events.copiesAgree E hs (hh.one E l)) (Events.genesisAgree_of_honest E hs hh) i j (pinSite p) hi hj
      simp only [invSections, invSec, pinSite] at this
      rw [this]

    /-- **The verdict is the glued section's.** -/
    theorem verdict_glue {w : World D} {G : Sec (SitesIn w) (Inventory D)}
        (hG : Glues (invSections w) G) (i : Copy w) {p : Pin D} (hi : SiteHeld i.obj (pinSite p)) :
        resolveEntry E.hash (some (.live i.obj)) p = verdictOf E (G (pinSite p) ⟨i, hi⟩) p := by
      rw [resolveEntry_verdict]
      have : G (pinSite p) ⟨i, hi⟩ = i.obj.inventory p.version :=
        congrFun (congrFun (hG i) (pinSite p)) hi
      rw [this]

## Lifting

At an object version held in the world, a pin resolves exactly when the
digest of the glued inventory is the pin's: the pin lifts along the digest
morphism. Without collisions the lift is unique: any inventory with the
pin's digest, found anywhere, is the glued one.

    /-- **A pin lifts exactly when it resolves.** At an object version held in the
    world, the verdict is a version exactly when the glued inventory has the
    pin's digest: verification is lifting the pin, a point of the digest sheaf,
    to the inventory sheaf. -/
    theorem lifts_iff {w : World D} {G : Sec (SitesIn w) (Inventory D)}
        (hG : Glues (invSections w) G) (i : Copy w) {p : Pin D} (hi : SiteHeld i.obj (pinSite p)) :
        (∃ u, verdictOf E (G (pinSite p) ⟨i, hi⟩) p = .ok u) ↔
          digests E G (pinSite p) ⟨i, hi⟩ = p.digest := by
      have hG' : G (pinSite p) ⟨i, hi⟩ = i.obj.inventory p.version :=
        congrFun (congrFun (hG i) (pinSite p)) hi
      simp only [digests]
      rw [hG']
      obtain ⟨_, h1, h2⟩ := hi
      have h1' : 1 ≤ p.version := h1
      have h2' : p.version ≤ i.obj.versions.length := h2
      have hv : ∃ v, (i.obj.inventory p.version).versions[p.version - 1]? = some v := by
        simp only [Obj.inventory]
        rw [List.getElem?_take]
        simp only [show p.version - 1 < p.version by omega, ite_true]
        exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨v, hv⟩ := hv
      unfold verdictOf
      rw [if_no (by omega), hv]
      constructor
      · rintro ⟨u, hu⟩
        by_cases hd : E.hash (i.obj.inventory p.version) = p.digest
        · exact hd
        · simp [hd] at hu
      · intro hd
        exact ⟨v, by simp [hd]⟩

    omit [DecidableEq D] in
    /-- **The lift is unique.** An inventory with the pin's digest, found anywhere,
    is the glued one, unless the two collide. -/
    theorem lift_unique {w : World D} {G : Sec (SitesIn w) (Inventory D)} {p : Pin D}
        (hx : SitesIn w (pinSite p)) {inv : Inventory D}
        (hcol : NoCollision E inv (G (pinSite p) hx)) (h : E.hash inv = p.digest)
        (hG : digests E G (pinSite p) hx = p.digest) : inv = G (pinSite p) hx :=
      hcol (h.trans hG.symm)

    end OpenSheaf.Sheaf
