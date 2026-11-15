# Descriptions are the fibres

The program has two bases: the object versions (chapter
[Verification is lifting](72-lifting.md)) and the named document versions
(the rest). They are related by a map: each object version goes to the
named document version it holds. Several object versions go to the same
named document version: the one that deposited it, the description-only
versions that describe it later, and their copies in mirrors. This chapter
studies the map, and proves:

- **its image is what the world holds** (`proj_image`);
- **content is pushed forward**: the content sheaf at the image of an
  object version is the content of that version (`content_pushforward`);
  so the content sheaf is the image of the inventory sheaf under the map
  that forgets descriptions;
- **the fibres are the contents**: two object versions go to the same point
  exactly when they are versions of the same object with the same content
  (`proj_fibre`);
- **description-only versions are the later points of the fibres**: in a
  well-formed history, a version holds content deposited before it exactly
  when an earlier version holds its document version (`descOnly_iff`);
- **descriptions do not glue**: two object versions of the story's paper
  describe its first document version differently
  (`descriptions_incompatible`).

So what the map forgets, the description, is exactly what varies along a
fibre. The specification settles it by choosing a point in each fibre: the
description of a document version is that of the last object version
holding it, which `history` records (section 7.3). That is a choice of one
point per fibre, made by the owner's latest version, not something forced by
agreement. The content, constant on each fibre, needs no choice: it glues.

    -- in Sheaf/Fibres.lean:
    import Sheaf.Lifting
    import Sheaf.Story

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
      ⟨s.archive, s.object, ((lastV i).map (·.documentVersion)).getD 0⟩

    /-- The map from the object versions held in a world to named document
    versions, read off the glued inventories. -/
    def proj {w : World D} (G : Sec (SitesIn w) (Inventory D)) : Sec (SitesIn w) Name :=
      fun s hs => docOf s (G s hs)

At an object version held by a copy, the map gives the named document
version that the copy's version there holds.

    theorem lastV_inventory {c : Obj D} {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ c.versions.length) :
        ∃ v, lastV (c.inventory n) = some v ∧ v ∈ c.versions ∧ c.versions[n - 1]? = some v := by
      have hlt : n - 1 < c.versions.length := by omega
      refine ⟨c.versions[n - 1], ?_, List.getElem_mem hlt, List.getElem?_eq_getElem hlt⟩
      unfold lastV Obj.inventory
      rw [List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left h2, List.getElem?_take]
      simp only [show n - 1 < n by omega, ite_true]
      exact List.getElem?_eq_getElem hlt

    /-- At an object version held by a copy, the map gives the named document
    version that the copy's version there holds. -/
    theorem proj_eq {w : World D} {G : Sec (SitesIn w) (Inventory D)} (hG : Glues (invSections w) G)
        {s : VSite} (hs : SitesIn w s) :
        ∃ (i : Copy w) (v : Version D), v ∈ i.obj.versions ∧ lastV (G s hs) = some v ∧
          proj G s hs = i.obj.name v := by
      obtain ⟨i, hi⟩ := hs
      have hGi : G s ⟨i, hi⟩ = i.obj.inventory s.version := congrFun (congrFun (hG i) s) hi
      obtain ⟨ha, ho, h1, h2⟩ := hi
      obtain ⟨v, hl, hv, _⟩ := lastV_inventory h1 h2
      refine ⟨i, v, hv, by rw [hGi]; exact hl, ?_⟩
      simp only [proj, docOf, hGi, hl, Option.map_some, Option.getD_some, Obj.name, ha, ho]

## Image and pushforward

Every named document version the world holds is the image of the object
version that holds it, and every image is held.

    variable [DecidableEq D] (hash : Hash D)

    /-- **The image is what the world holds.** -/
    theorem proj_image {w : World D} (hk : Kept hash w) {G : Sec (SitesIn w) (Inventory D)}
        (hG : Glues (invSections w) G) (x : Name) :
        HeldIn w x ↔ ∃ s hs, proj G s hs = x := by
      constructor
      · intro hx
        obtain ⟨v, b, i, c, hl, hv, rfl⟩ := (heldIn_iff hash hk.1 x).mp hx
        obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.mp hv
        let s : VSite := ⟨c.archive, c.id, k + 1⟩
        have hi : SiteHeld c s := ⟨rfl, rfl, by simp [s], by simp [s]; omega⟩
        refine ⟨s, ⟨⟨b, i, c, hl⟩, hi⟩, ?_⟩
        obtain ⟨j, v', hv', hlast, hp⟩ := proj_eq hG ⟨⟨b, i, c, hl⟩, hi⟩
        have hGi : G s ⟨⟨b, i, c, hl⟩, hi⟩ = c.inventory (k + 1) :=
          congrFun (congrFun (hG ⟨b, i, c, hl⟩) s) hi
        obtain ⟨u, hu, _, hk2⟩ := lastV_inventory (c := c) (n := k + 1) (by omega) (by omega)
        rw [hGi, hu] at hlast; cases hlast
        simp only [Nat.add_sub_cancel] at hk2
        rw [List.getElem?_eq_getElem hk'] at hk2; cases hk2
        simp only [proj, docOf, hGi, hu, Option.map_some, Option.getD_some, Obj.name, s]
      · rintro ⟨s, hs, rfl⟩
        obtain ⟨i, v, hv, _, hp⟩ := proj_eq hG hs
        rw [hp]
        exact heldIn_of_live hash hk.1 i.live hv

The content sheaf, at the image of an object version, is the content of
that version: the content sheaf is the pushforward of the inventories,
followed by forgetting the description.

    /-- **Content is pushed forward.** The content sheaf at the image of an object
    version is the content of that object version. -/
    theorem content_pushforward {w : World D} (hk : Kept hash w)
        {G : Sec (SitesIn w) (Inventory D)} (hG : Glues (invSections w) G)
        {g : Sec (HeldIn w) (Content D)} (hg : Glues (sections w) g) {s : VSite} (hs : SitesIn w s)
        (hx : HeldIn w (proj G s hs)) :
        ∃ v, lastV (G s hs) = some v ∧ g (proj G s hs) hx = v.content := by
      obtain ⟨i, v, hv, hl, hp⟩ := proj_eq hG hs
      refine ⟨v, hl, ?_⟩
      have hh : Holds w (proj G s hs) v := ⟨i.archive, i.id, i.obj, i.live, hv, hp.symm⟩
      exact glue_value hash hk.1 hg hh hx

## The fibres

Two object versions go to the same named document version exactly when they
have the same content: one direction is that a number has one content
(`one_number_one_content`), the other that a content has one number
(`one_content_one_number`), both proved in the model, with the copies'
agreement to compare versions kept in different places.

    /-- **The fibres are the contents.** Two object versions held in a world go to
    the same named document version exactly when they are versions of the same
    object with the same content. -/
    theorem proj_fibre {w : World D} (hk : Kept hash w) {G : Sec (SitesIn w) (Inventory D)}
        (hG : Glues (invSections w) G) {s s' : VSite} (hs : SitesIn w s) (hs' : SitesIn w s')
        {v v' : Version D} (hv : lastV (G s hs) = some v) (hv' : lastV (G s' hs') = some v') :
        proj G s hs = proj G s' hs' ↔
          s.archive = s'.archive ∧ s.object = s'.object ∧ sameContent v v' = true := by
      obtain ⟨i, u, hu, hl, hp⟩ := proj_eq hG hs
      obtain ⟨i', u', hu', hl', hp'⟩ := proj_eq hG hs'
      rw [hv] at hl; cases hl
      rw [hv'] at hl'; cases hl'
      constructor
      · intro h
        have e : proj G s hs = proj G s' hs' := h
        simp only [proj, docOf, Name.mk.injEq] at e
        refine ⟨e.1, e.2.1, ?_⟩
        exact holds_agree hash hk ⟨i.archive, i.id, i.obj, i.live, hu, hp.symm⟩
          ⟨i'.archive, i'.id, i'.obj, i'.live, hu', (h.trans hp').symm⟩
      · rintro ⟨ha, ho, hc⟩
        rw [hp, hp']
        have hia : i.obj.archive = i'.obj.archive := by
          have e1 : (proj G s hs).archive = i.obj.archive := by rw [hp]; rfl
          have e2 : (proj G s' hs').archive = i'.obj.archive := by rw [hp']; rfl
          simp only [proj, docOf] at e1 e2
          rw [← e1, ← e2, ha]
        have hio : i.obj.id = i'.obj.id := by
          have e1 : (proj G s hs).object = i.obj.id := by rw [hp]; rfl
          have e2 : (proj G s' hs').object = i'.obj.id := by rw [hp']; rfl
          simp only [proj, docOf] at e1 e2
          rw [← e1, ← e2, ho]
        have hd : v.documentVersion = v'.documentVersion := by
          rcases hk.2.2 _ _ _ _ _ _ i.live i'.live hia hio with ⟨t, ht⟩ | ⟨t, ht⟩
          · exact one_content_one_number (hk.1.1 _ _ _ i'.live).history
              (by rw [ht]; exact List.mem_append_left _ hu) hu' hc
          · exact one_content_one_number (hk.1.1 _ _ _ i.live).history
              hu (by rw [ht]; exact List.mem_append_left _ hu') hc
        simp only [Obj.name, hia, hio, hd]

Within one history, the first point of a fibre deposits the document
version, and the later points are description-only versions: they hold
content deposited before them.

    /-- **Description-only versions are the later points of the fibres.** In a
    well-formed history, a version holds content deposited before it exactly
    when an earlier version holds the same document version. -/
    theorem descOnly_iff {l : List (Version D)} (h : WellFormed l) {k : Nat} (hk : k < l.length) :
        (∃ j, ∃ hj : j < k, sameContent l[j] l[k] = true) ↔
          (∃ j, ∃ hj : j < k, l[j].documentVersion = l[k].documentVersion) := by
      constructor
      · rintro ⟨j, hj, hc⟩
        exact ⟨j, hj, one_content_one_number h (List.getElem_mem _) (List.getElem_mem _) hc⟩
      · rintro ⟨j, hj, hd⟩
        exact ⟨j, hj, one_number_one_content h (List.getElem_mem _) (List.getElem_mem _) hd⟩

## Descriptions do not glue

The description of a document version, as an object version gives it, is
that of the last object version up to it that holds the document version.
These descriptions form a family of sections like the contents, but not a
compatible one.

    omit [DecidableEq D] in
    /-- The description a history gives to document version `k`: that of the last
    object version holding it, as `history` records (section 7.3). -/
    def docDescription (l : List (Version D)) (k : Nat) : String :=
      (((l.filter (·.documentVersion == k)).getLast?).map (·.description)).getD ""

    omit [DecidableEq D] in
    /-- The descriptions an object version gives. -/
    def descSec (o : Obj D) (n : Nat) : Sec (Held o n) String :=
      fun x _ => docDescription (o.versions.take n) x.doc

    omit [DecidableEq D] in
    abbrev descSections (w : World D) (i : Source w) : Sec (cover w i) String :=
      descSec i.obj i.version

In the story, the author's paper has three object versions; the third is
a description-only version that retitles document version 1. Object version
1 and object version 3 of the same copy describe document version 1
differently, so the descriptions have no glued section, while the contents
do (chapter [A story, as a sheaf](60-story.md)).

    namespace Story

    open OpenSheaf.Story

    def authorFirst : Source w14 := ⟨"author", "paper", paper3, rfl, 1⟩

    /-- **Descriptions do not glue.** In the story, the author's object versions
    1 and 3 describe document version 1 differently. -/
    theorem descriptions_incompatible : ¬ Compatible (descSections w14) := by
      intro h
      have h3 : cover w14 authorPaper first := by decide
      have h1 : cover w14 authorFirst first := by decide
      have := h authorPaper authorFirst first h3 h1
      change docDescription (paper3.versions.take 3) 1 = docDescription (paper3.versions.take 1) 1
        at this
      revert this
      decide

    end Story

    end OpenSheaf.Sheaf
