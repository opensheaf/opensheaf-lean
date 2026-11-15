# A world is a sheaf

A world of the model holds objects in archives, and the same object may be
held in several places: in its own archive, and in the archives that mirror
it (section 10.4). Each copy, and each object version of each copy, gives a
section over the named document versions it holds. This chapter proves the
main theorem: in every world built from nothing by the events the
specification allows (valid steps and takedowns), these sections are
compatible, so they glue, into exactly one section over every named
document version held anywhere. Whichever copy and whichever object version
a reader takes a document version from, they read the same content.

The sheaf condition itself holds for general reasons (chapter 1); the
content of the theorem is that the sections of a world are compatible.
Nothing in the sections themselves forces this. A name carries no digest,
so two copies could hold different content under the same name; the
chapter [A story](60-story.md) builds such a world, which has no glued
section. That the sections of a valid world agree is a property of the
protocol, proved in two steps:

1. **Copies agree.** Any two copies of an object, wherever they are kept,
   have histories of which one is a prefix of the other: the git notion of
   a fast-forward. The model proves it for every world built by events,
   takedowns included (`Events.copiesAgree`, in its chapter "Mirrors and
   accepted copies"). It is stronger than `MirrorsOk`, which relates a
   mirror to its original only while the original is live.
2. **Prefixes agree.** Two prefixes of a well-formed history give the same
   value to every document version they both hold, by the previous chapter.

    -- in Sheaf/World.lean:
    import Sheaf.Object

    namespace OpenSheaf.Sheaf

    variable {D : Type}

## The cover of a world

The sources of a world are its live copies, kept anywhere, each with one of
its object versions. Each gives a section, over the open set it holds. The
union of these sets is every named document version held anywhere in the
world; being a union of open sets, it is open.

    /-- A source of sections: a live object kept somewhere, and one of its object
    versions. -/
    structure Source (w : World D) where
      archive : ArchiveId
      id : ObjectId
      obj : Obj D
      live : lookup w archive id = some (.live obj)
      version : Nat

    /-- The named document versions a source holds. -/
    abbrev cover (w : World D) (i : Source w) : Name → Prop := Held i.obj i.version

    /-- The section of a source. -/
    abbrev sections (w : World D) (i : Source w) : Sec (cover w i) (Content D) :=
      objSec i.obj i.version

    /-- The named document versions held anywhere in a world. -/
    def HeldIn (w : World D) : Name → Prop := Union (cover w)

    theorem heldIn_open (w : World D) : deposit.IsOpen (HeldIn w) :=
      deposit.union_open fun i => held_open i.obj i.version

## The sections glue

    variable [DecidableEq D] (hash : Hash D)

Two prefixes of one well-formed history give the same value to a document
version they both hold: both give the content of every object version
holding it.

    omit [DecidableEq D] in
    theorem take_drop_append (l t : List (Version D)) (n : Nat) :
        l ++ t = l.take n ++ (l.drop n ++ t) := by
      rw [← List.append_assoc, List.take_append_drop]

    theorem docContent_agree {L l1 l2 t1 t2 : List (Version D)} (hL : WellFormed L)
        (h1 : L = l1 ++ t1) (h2 : L = l2 ++ t2) {k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ docCount l1)
        (hk' : k ≤ docCount l2) : docContent l1 k = docContent l2 k := by
      have hw1 : WellFormed l1 := by subst h1; exact hL.prefix
      obtain ⟨u, hu, huk⟩ := no_gaps hw1 hk1 hk
      have huL : u ∈ L := by rw [h1]; exact List.mem_append_left _ hu
      rw [docContent_eq hL h1 hk1 hk huL huk, docContent_eq hL h2 hk1 hk' huL huk]

Two sources that hold the same named document version are copies of the
same object. When their histories are comparable, both object versions are
prefixes of the longer history, which is well formed, so they give the same
value. This argument needs only two facts about a world: its live objects
are well formed, and its copies agree. It is stated for any world with
these two facts, so that the chapter
[Separate worlds](76-federation.md) can use it for worlds that are not built by
events.

    /-- Copies that agree, and well-formed histories, give compatible sections. -/
    theorem compatible_of_agree {w : World D}
        (hwf : ∀ b i c, lookup w b i = some (.live c) → WellFormed c.versions)
        (hca : CopiesAgree w) : Compatible (sections w) := by
      intro i j x ⟨a1, o1, k1, d1⟩ ⟨a2, o2, _, d2⟩
      have hc := hca _ _ _ _ _ _ i.live j.live (a1.symm.trans a2) (o1.symm.trans o2)
      simp only [sections, objSec]
      rcases hc with ⟨t, ht⟩ | ⟨t, ht⟩
      · have hi : j.obj.versions = i.obj.versions.take i.version ++
            (i.obj.versions.drop i.version ++ t) := by rw [ht]; exact take_drop_append _ _ _
        exact docContent_agree (hwf _ _ _ j.live) hi (List.take_append_drop _ _).symm k1 d1 d2
      · have hj : i.obj.versions = j.obj.versions.take j.version ++
            (j.obj.versions.drop j.version ++ t) := by rw [ht]; exact take_drop_append _ _ _
        exact docContent_agree (hwf _ _ _ i.live) (List.take_append_drop _ _).symm hj k1 d1 d2

A world built by events has both facts: its objects are well formed
(`Events.sound`, in the model) and its copies agree (`Events.copiesAgree`).

    /-- **The sections of a world are compatible.** -/
    theorem world_compatible {w : World D}
        (hs : Events hash (fun _ => (none : Option (Archive D))) w) :
        Compatible (sections w) :=
      compatible_of_agree (fun _ _ _ hl => ((Events.sound hash hs).1 _ _ _ hl).history)
        (Events.copiesAgree hash hs)

The main theorem follows from the sheaf condition of the first chapter.

    /-- **A world built by events is a sheaf.** Its sections glue into exactly one
    section over the named document versions it holds: one content for each,
    whichever copy it is read from. -/
    theorem world_sheaf {w : World D}
        (hs : Events hash (fun _ => (none : Option (Archive D))) w) :
        ∃ g, Glues (sections w) g ∧ ∀ g', Glues (sections w) g' → g' = g :=
      sheaf (world_compatible hash hs)

The theorem holds after takedowns too. A takedown removes the sections of
the copy taken down, and the remaining ones still glue; the named document
versions it held stay held if a mirror keeps them.

## A check made piece by piece

The second half of the rule of section 7.3 is a local condition: below a
named document version, no earlier document version of the same object has
the same content. It looks only at the history below a point, so it can be
checked one object version at a time. Each object version satisfies it,
since its history is well formed. The glued section satisfies it, by the
theorem on local conditions of the first chapter. So the condition holds of
the world as a whole, whichever copies the values are read from.

    /-- A new number is new content: below a point, no earlier document version of
    the same object has the same content. -/
    def NewContent : LocalCond deposit (Content D) :=
      fun x f => ∀ y (hy : deposit.le y x), y.doc ≠ x.doc → f y hy ≠ f x (deposit.refl x)

    /-- Each object version satisfies it (section 7.3). -/
    theorem objSec_newContent {o : Obj D} (hwf : WellFormed o.versions) (n : Nat) :
        (objSec o n).Satisfies deposit (held_open o n) NewContent := by
      intro x hx y hy hne heq
      have hyx := held_open o n hy hx
      obtain ⟨v, hv, rfl⟩ := (held_iff hwf n x).mp hx
      obtain ⟨u, hu, rfl⟩ := (held_iff hwf n y).mp hyx
      have heq' : objSec o n (o.name u) hyx = objSec o n (o.name v) hx := heq
      rw [objSec_piece hwf hu, objSec_piece hwf hv] at heq'
      exact hne (one_content_one_number hwf (List.mem_of_mem_take hu)
        (List.mem_of_mem_take hv) (content_eq_iff.mp heq'))

    /-- **So does the glued section**, which takes its values from many copies. -/
    theorem world_newContent {w : World D}
        (hs : Events hash (fun _ => (none : Option (Archive D))) w) {g : Sec (HeldIn w) (Content D)}
        (hg : Glues (sections w) g) : g.Satisfies deposit (heldIn_open w) NewContent :=
      glue_satisfies deposit (fun i => held_open i.obj i.version) hg NewContent
        fun i => objSec_newContent ((Events.sound hash hs).1 _ _ _ i.live).history i.version

    end OpenSheaf.Sheaf
