# Descriptions are the fibres

The program has two bases: the object versions (chapter
[Verification is lifting](72-lifting.md)) and the named document versions
(the rest). Two maps go from the first to the second, and each shows
something about descriptions.

- **The document version a version holds** (`proj`). Its fibres are
  exactly the contents: two object versions go to the same named document
  version when they are versions of the same object with the same content
  (`proj_fibre`), and its image is what the world holds (`proj_image`). The
  content at the image of an object version is the content of that version
  (`content_factors`). But the map is **not monotone**: a description-only
  version that describes an earlier document version goes below the
  version before it. In the story, object versions 2 and 3 of the paper
  hold document versions 2 and 1. So it is not a continuous map of the two
  Alexandrov spaces, there is no pushforward of sheaves along it, and the
  identity it gives is a factorisation, not more.
- **The highest document version deposited so far** (`top`, chapter
  [An object version is a section](30-object.md)). It is monotone
  (`top_mono`), and the open set of an object version is the principal open
  below its top (`covers_principal`). Its fibres are runs: a version that
  deposits a document version, then the description-only versions that
  follow it, until the next deposit (`top_step_iff`).

Descriptions vary along both: a description-only version describes, with a
new description, content already held. And **descriptions do not glue**:
two object versions of the story's paper describe its first document
version differently (in the chapter on the story). The specification
settles the description by choosing a point in each fibre of `proj`: the
last object version holding the document version, which `history` records
(section 4.2). That is a choice made by the owner's latest version, not
something forced by agreement. The content, constant on each fibre of
`proj`, needs no choice: it glues.

    -- in Sheaf/Fibres.lean:
    import Sheaf.Lifting

    namespace OpenSheaf.Sheaf

## The map

An inventory at an object version ends with that version, which holds a
document version. The map reads it off the glued inventories of the world,
so it does not depend on the copy.

    variable {D : Type}

    /-- The version an inventory ends with. -/
    def lastV (i : Inventory D) : Option (Version D) := i.versions.getLast?

    /-- The named document version held by the last version of an inventory at
    an object version. -/
    def docOf (s : VSite) (i : Inventory D) : Name :=
      ⟨s.object, ((lastV i).map (·.documentVersion)).getD 0⟩

    /-- The map from the object versions held in a world to named document
    versions, read off the glued inventories. -/
    def proj {w : World D} (G : Sec (SitesIn w) (Inventory D)) : Sec (SitesIn w) Name :=
      fun s hs => docOf s (G s hs)

At an object version held by a copy, the map gives the named document
version that the copy's version there holds.

    theorem lastV_inventory {c : Obj D} {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ c.versions.length) :
        ∃ v, lastV (c.inventory n) = some v ∧ v ∈ c.versions ∧ c.versions[n - 1]? = some v := by
      have hlt : n - 1 < c.versions.length := by omega
      have hva : c.versionAt n = some c.versions[n - 1] := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rw [Obj.versionAt_succ]; simp
      exact ⟨c.versions[n - 1], getLast?_take hva, List.getElem_mem hlt,
        List.getElem?_eq_getElem hlt⟩

    /-- At an object version held by a copy, the map gives the named document
    version that the copy's version there holds. -/
    theorem proj_eq {w : World D} {G : Sec (SitesIn w) (Inventory D)} (hG : Glues (invSections w) G)
        {s : VSite} (hs : SitesIn w s) :
        ∃ (i : Copy w) (v : Version D), v ∈ i.obj.versions ∧ lastV (G s hs) = some v ∧
          proj G s hs = i.obj.name v := by
      obtain ⟨i, hi⟩ := hs
      have hGi : G s ⟨i, hi⟩ = i.obj.inventory s.version := congrFun (congrFun (hG i) s) hi
      obtain ⟨ho, h1, h2⟩ := hi
      obtain ⟨v, hl, hv, _⟩ := lastV_inventory h1 h2
      refine ⟨i, v, hv, by rw [hGi]; exact hl, ?_⟩
      simp only [proj, docOf, hGi, hl, Option.map_some, Option.getD_some, Obj.name, ho]

## Image and content

Every named document version the world holds is the image of the object
version that holds it, and every image is held.

    variable [DecidableEq D] (E : Env D)

    /-- **The image is what the world holds.** -/
    theorem proj_image {w : World D} (hk : Kept E w) {G : Sec (SitesIn w) (Inventory D)}
        (hG : Glues (invSections w) G) (x : Name) :
        HeldIn w x ↔ ∃ s hs, proj G s hs = x := by
      constructor
      · intro hx
        obtain ⟨v, b, i, c, hl, hkc, hv, rfl⟩ := (heldIn_iff E hk.1 x).mp hx
        obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.mp hv
        let s : VSite := ⟨c.id, k + 1⟩
        have hi : SiteHeld c s := ⟨rfl, by simp [s], by simp [s]; omega⟩
        refine ⟨s, ⟨⟨b, i, c, hl, hkc⟩, hi⟩, ?_⟩
        obtain ⟨j, v', hv', hlast, hp⟩ := proj_eq hG ⟨⟨b, i, c, hl, hkc⟩, hi⟩
        have hGi : G s ⟨⟨b, i, c, hl, hkc⟩, hi⟩ = c.inventory (k + 1) :=
          congrFun (congrFun (hG ⟨b, i, c, hl, hkc⟩) s) hi
        obtain ⟨u, hu, _, hk2⟩ := lastV_inventory (c := c) (n := k + 1) (by omega) (by omega)
        rw [hGi, hu] at hlast; cases hlast
        simp only [Nat.add_sub_cancel] at hk2
        rw [List.getElem?_eq_getElem hk'] at hk2; cases hk2
        simp only [proj, docOf, hGi, hu, Option.map_some, Option.getD_some, Obj.name, s]
      · rintro ⟨s, hs, rfl⟩
        obtain ⟨i, v, hv, _, hp⟩ := proj_eq hG hs
        rw [hp]
        exact heldIn_of_live E hk.1 i.live i.kind hv

The content sheaf, at the image of an object version, is the content of
that version: the glued section composed with the map is the content of the
glued inventories' last versions. This is a factorisation of two sections
through the map, not a pushforward of sheaves: the map is not monotone.

    /-- **Content factors through the map.** The content sheaf at the image of an
    object version is the content of that object version. -/
    theorem content_factors {w : World D} (hk : Kept E w)
        {G : Sec (SitesIn w) (Inventory D)} (hG : Glues (invSections w) G)
        {g : Sec (HeldIn w) (Content D)} (hg : Glues (sections w) g) {s : VSite} (hs : SitesIn w s)
        (hx : HeldIn w (proj G s hs)) :
        ∃ v, lastV (G s hs) = some v ∧ g (proj G s hs) hx = v.content := by
      obtain ⟨i, v, hv, hl, hp⟩ := proj_eq hG hs
      refine ⟨v, hl, ?_⟩
      have hh : Holds w (proj G s hs) v := ⟨i.archive, i.line, i.obj, i.live, i.kind, hv, hp.symm⟩
      exact glue_value E hk.1 hg hh hx

## The fibres

Two object versions go to the same named document version exactly when they
have the same content: one direction is that a number has one content
(`one_number_one_content`), the other that a content has one number
(`one_content_one_number`), both proved in the model, with the copies'
agreement to compare versions kept in different places.

    /-- **The fibres are the contents.** Two object versions held in a world go to
    the same named document version exactly when they are versions of the same
    object with the same content. -/
    theorem proj_fibre {w : World D} (hk : Kept E w) {G : Sec (SitesIn w) (Inventory D)}
        (hG : Glues (invSections w) G) {s s' : VSite} (hs : SitesIn w s) (hs' : SitesIn w s')
        {v v' : Version D} (hv : lastV (G s hs) = some v) (hv' : lastV (G s' hs') = some v') :
        proj G s hs = proj G s' hs' ↔ s.object = s'.object ∧ sameContent v v' = true := by
      obtain ⟨i, u, hu, hl, hp⟩ := proj_eq hG hs
      obtain ⟨i', u', hu', hl', hp'⟩ := proj_eq hG hs'
      rw [hv] at hl; cases hl
      rw [hv'] at hl'; cases hl'
      constructor
      · intro h
        have e : proj G s hs = proj G s' hs' := h
        simp only [proj, docOf, Name.mk.injEq] at e
        refine ⟨e.1, ?_⟩
        exact holds_agree E hk.1 hk.2 ⟨i.archive, i.line, i.obj, i.live, i.kind, hu, hp.symm⟩
          ⟨i'.archive, i'.line, i'.obj, i'.live, i'.kind, hu', (h.trans hp').symm⟩
      · rintro ⟨ho, hc⟩
        rw [hp, hp']
        have hio : i.obj.id = i'.obj.id := by
          have e1 : (proj G s hs).object = i.obj.id := by rw [hp]; rfl
          have e2 : (proj G s' hs').object = i'.obj.id := by rw [hp']; rfl
          simp only [proj, docOf] at e1 e2
          rw [← e1, ← e2, ho]
        have hll : i.line = i'.line := by
          have h1 := (hk.1.1 _ _ _ i.live).id
          have h2 := (hk.1.1 _ _ _ i'.live).id
          exact ObjectId.line.inj (h1.symm.trans (hio.trans h2))
        have hjl := i'.live
        rw [← hll] at hjl
        have hd : v.documentVersion = v'.documentVersion := by
          rcases hk.2 i.line _ _ _ _ i.live hjl i.kind i'.kind with ⟨t, ht⟩ | ⟨t, ht⟩
          · exact one_content_one_number ((hk.1.1 _ _ _ i'.live).history i'.kind)
              (by rw [ht]; exact List.mem_append_left _ hu) hu' hc
          · exact one_content_one_number ((hk.1.1 _ _ _ i.live).history i.kind)
              hu (by rw [ht]; exact List.mem_append_left _ hu') hc
        simp only [Obj.name, hio, hd]

## The runs of the top

Within one history, the top stays where it is exactly at the
description-only versions: a version leaves the highest document version
unchanged exactly when it holds content deposited before it. So the fibres
of the top are runs: a deposit, then the description-only versions that
follow it.

    /-- **The fibres of the top are runs.** In a well-formed history, version
    `k + 1` has the same top as version `k` exactly when it holds content
    deposited before it. -/
    theorem top_step_iff {l : List (Version D)} (h : WellFormed l) {k : Nat}
        (hk : k < l.length) :
        docCount (l.take (k + 1)) = docCount (l.take k) ↔
          ∃ v ∈ l.take k, sameContent v l[k] = true := by
      have hsplit : l.take (k + 1) = l.take k ++ [l[k]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
      have hwf : WellFormed (l.take (k + 1)) := by
        have := List.take_append_drop (k + 1) l
        rw [← this] at h; exact h.prefix
      rw [hsplit] at hwf ⊢
      obtain ⟨_, hx⟩ := hwf.init
      rw [docCount_append]
      constructor
      · intro heq
        rcases hx with ⟨z, hz, hzx, _⟩ | ⟨_, hn⟩
        · exact ⟨z, hz, hzx⟩
        · rw [hn] at heq; omega
      · rintro ⟨v, hv, hc⟩
        rcases hx with ⟨z, hz, _, hxz⟩ | ⟨hnew, _⟩
        · have := le_docCount hz; rw [hxz]; omega
        · rw [hnew v hv] at hc; cases hc

## Descriptions do not glue

The description of a document version, as an object version gives it, is
that of the last object version up to it that holds the document version.
These descriptions form a family of sections like the contents, but not a
compatible one.

    /-- The description a history gives to document version `k`: that of the last
    object version holding it, as `history` records (section 4.2). -/
    def docDescription (l : List (Version D)) (k : Nat) : String :=
      (((l.filter (·.documentVersion == k)).getLast?).map (·.description)).getD ""

    /-- The descriptions an object version gives. -/
    def descSec (o : Obj D) (n : Nat) : Sec (Covers o n) String :=
      fun x _ => docDescription (o.versions.take n) x.doc

    /-- The section of descriptions a source of a world gives (section 4.2). -/
    abbrev descSections (w : World D) (i : Source w) : Sec (cover w i) String :=
      descSec i.obj i.version

In the story of the model, the author's paper has object versions that
describe its first document version differently; read as a sheaf, the
descriptions there have no glued section while the contents do. That
computation belongs with the story, in the chapter
[A story, as a sheaf](60-story.md).

    end OpenSheaf.Sheaf
