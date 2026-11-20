# The sections of a world glue

A world of the model holds lines in archives, and the same line may be held
in several places: wherever its owner writes, and in the archives that keep
copies of it (section 11). Each copy, and each object version of each
copy, gives a section over the named document versions it holds. This
chapter proves the main theorem: in every world built from nothing by the
model's events (valid steps and takedowns), these sections are compatible,
so they glue, into exactly one section over every named document version
held anywhere, **as long as the owners of the lines sign one history
each**. Whichever copy and whichever object version a reader takes a
document version from, they read the same content. And when the sections
do not glue, a fork is the reason: two copies of a line, neither extending
the other, each end in a version signed with a current key of the owner's
key log as the world holds it (`no_glue_fork`).

The sheaf condition itself holds for general reasons (chapter 1); the
content of the theorem is that the sections of a world are compatible.
Nothing in the sections themselves forces this. A name carries no digest,
so two copies could hold different content under the same name. In version
0.1 of the specification an object had one home archive and its mirrors
copied it, and every world built by events glued. In version 0.2 "a line
is its signed versions, wherever they are stored" (section 7): its owner
may write in several archives, and an owner whose keys sign two versions
of one number makes a **fork of the line**, "reported with the status of
each side, and never recorded" (section 7.4). That the sections of a valid world agree is then a property
of the protocol together with the owners' keys, proved in two steps:

1. **Copies agree.** Any two copies of a line, wherever they are kept, have
   histories of which one is a prefix of the other, when the owner signs
   one history (`Events.copiesAgree`, in the model's chapter "Copies,
   mirrors and branches"). The hypothesis, `OneHistory`, also says that no
   copy the world holds collides with that history: signatures name
   digests.
2. **Prefixes agree.** Two prefixes of a well-formed history give the same
   value to every document version they both hold, by the previous chapter.

    -- in Sheaf/World.lean:
    import Sheaf.Object

    namespace OpenSheaf.Sheaf

    variable {D : Type}

## The cover of a world

The sources of a world are its live copies of lines that are not key logs,
kept anywhere, each with one of its object versions. Each gives a section,
over the open set it holds. Drafts give none: a draft's identifier is
chosen by its archive (section 10.1), so two archives may keep different
drafts under one identifier, and nothing relies on a draft. Key logs give
none: they have no document versions (section 4.1). The union of these
sets is every named document version held anywhere in the world; being a
union of open sets, it is open.

    /-- A source of sections: a live copy of a line, not a key log, kept
    somewhere, and one of its object versions. -/
    structure Source (w : World D) where
      archive : ArchiveId
      line : LineId
      obj : Obj D
      live : lookup w archive (.line line) = some (.live obj)
      kind : obj.kind ≠ .owner
      version : Nat

    /-- The named document versions a source holds. -/
    abbrev cover (w : World D) (i : Source w) : Name → Prop := Covers i.obj i.version

    /-- The section of a source. -/
    abbrev sections (w : World D) (i : Source w) : Sec (cover w i) (Content D) :=
      objSec i.obj i.version

    /-- The named document versions held anywhere in a world. -/
    def HeldIn (w : World D) : Name → Prop := Union (cover w)

    theorem heldIn_open (w : World D) : deposit.IsOpen (HeldIn w) :=
      deposit.union_open fun i => covers_open i.obj i.version

## The sections glue

    variable [DecidableEq D] (E : Env D)

Every owner signs one history, and no copy held collides with it: the
hypothesis of the main theorem, the model's `OneHistory` for every line.
Theorems that compare two worlds need the same histories in both, so the
hypothesis names them: `H` gives, for each line, the genesis record and
the history its owner signs (the model's `SignsHistory`), and the world
holds no copy that collides with them (`NoCollisionWith`). Only pairs of
inventories are assumed not to collide, never the digest to be injective.
The hypothesis asks a history of every line, key logs and lines the world
does not hold included, though the theorems use it only for the lines whose
copies are documents or collections: it counts only the signatures made
with current keys of the owner, which a key log's own versions do not
have, and holds of a line nobody signed with the empty history. The
model's freedom from cycles asks it only of lines that are not key logs;
here it is left for every line, since restricting it would need, for each
use, that the copies at hand are not at the line of a key log, which holds
only in worlds whose names do not collide.

    /-- For each line, a genesis record and the history its owner signs. -/
    abbrev Histories (D : Type) := LineId → Option (Genesis D) × List (Version D)

    /-- Owners sign the histories `H`, and no copy held in `w` collides with them. -/
    def Honest (H : Histories D) (w : World D) : Prop :=
      (∀ l, SignsHistory E w l (H l).1 (H l).2) ∧ ∀ l, NoCollisionWith E w l (H l).1 (H l).2

    omit [DecidableEq D] in
    theorem Honest.one {H : Histories D} {w : World D} (h : Honest E H w) (l : LineId) :
        OneHistory E w l :=
      ⟨_, _, h.1 l, h.2 l⟩

    omit [DecidableEq D] in
    theorem Honest.back {H : Histories D} {w w' : World D} (hs : Steps w w')
        (h : Honest E H w') : Honest E H w :=
      ⟨fun l => (h.1 l).back E hs, fun l => (h.2 l).back E hs⟩

In two worlds built by events with the same honest histories, the copies
of a line are prefixes of one history, so of one another.

    theorem honest_comparable {H : Histories D} {w w' : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w)
        (hs' : Events E (fun _ => (none : Option (Archive D))) w')
        (hh : Honest E H w) (hh' : Honest E H w') {b b' : ArchiveId} {l : LineId} {o o' : Obj D}
        (hl : lookup w b (.line l) = some (.live o)) (hl' : lookup w' b' (.line l) = some (.live o'))
        (hk : o.kind ≠ .owner) (hk' : o'.kind ≠ .owner) : Comparable o.versions o'.versions := by
      obtain ⟨_, h⟩ := Events.prefix_history E hs (hh.1 l) (hh.2 l) hl hk
      obtain ⟨_, h'⟩ := Events.prefix_history E hs' (hh'.1 l) (hh'.2 l) hl' hk'
      have e1 := List.take_append_drop o.versions.length (H l).2
      have e2 := List.take_append_drop o'.versions.length (H l).2
      rw [← h] at e1; rw [← h'] at e2
      exact comparable_of_prefixes e1.symm e2.symm

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
same line: a source's object records its line as its identifier, in a
world whose objects are well formed. When their histories are comparable,
both object versions are prefixes of the longer history, which is well
formed, so they give the same value. This argument needs only two facts
about a world: its live objects are well formed, and the copies of each
line agree. It is stated for any world with these two facts, so that the
chapter [Separate worlds](76-federation.md) can use it for worlds that are
not built by events.

    /-- Live objects, stored under their identifiers, with well-formed histories
    unless they are key logs. -/
    def WFObjects (w : World D) : Prop :=
      ∀ b i c, lookup w b i = some (.live c) → c.id = i ∧ (c.kind ≠ .owner → WellFormed c.versions)

    /-- Copies that agree, and well-formed histories, give compatible sections. -/
    theorem compatible_of_agree {w : World D} (hwf : WFObjects w)
        (hca : ∀ l, CopiesAgree w l) : Compatible (sections w) := by
      intro i j x ⟨o1, k1, d1⟩ ⟨o2, _, d2⟩
      have hl : i.line = j.line := by
        have h1 := (hwf _ _ _ i.live).1
        have h2 := (hwf _ _ _ j.live).1
        exact ObjectId.line.inj (h1.symm.trans (o1.symm.trans (o2.trans h2)))
      have hjl := j.live
      rw [← hl] at hjl
      have hc := hca i.line _ _ _ _ i.live hjl i.kind j.kind
      simp only [sections, objSec]
      rcases hc with ⟨t, ht⟩ | ⟨t, ht⟩
      · have hi : j.obj.versions = i.obj.versions.take i.version ++
            (i.obj.versions.drop i.version ++ t) := by rw [ht]; exact take_drop_append _ _ _
        exact docContent_agree ((hwf _ _ _ j.live).2 j.kind) hi (List.take_append_drop _ _).symm k1 d1 d2
      · have hj : i.obj.versions = j.obj.versions.take j.version ++
            (j.obj.versions.drop j.version ++ t) := by rw [ht]; exact take_drop_append _ _ _
        exact docContent_agree ((hwf _ _ _ i.live).2 i.kind) (List.take_append_drop _ _).symm hj k1 d1 d2

A world built by events has both facts when its owners are honest: its
objects are well formed (`Events.sound`, in the model) and the copies of
each line agree (`Events.copiesAgree`).

    theorem SoundWorld.wfObjects {w : World D} (hw : SoundWorld E w) : WFObjects w :=
      fun _ _ _ hl => ⟨(hw.1 _ _ _ hl).id, (hw.1 _ _ _ hl).history⟩

    /-- **The sections of a world are compatible**, when its owners are honest. -/
    theorem world_compatible {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {H : Histories D} (hh : Honest E H w) :
        Compatible (sections w) :=
      compatible_of_agree (SoundWorld.wfObjects E (Events.sound E hs)) fun l => Events.copiesAgree E hs (hh.one E l)

The main theorem follows from the sheaf condition of the first chapter.

    /-- **The sections of a world built by events glue** into exactly one
    section over the named document versions it holds, when its owners are
    honest: one content for each, whichever copy it is read from. -/
    theorem world_glues {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {H : Histories D} (hh : Honest E H w) :
        ∃ g, Glues (sections w) g ∧ ∀ g', Glues (sections w) g' → g' = g :=
      sheaf (world_compatible E hs hh)

The theorem holds after takedowns too. A takedown removes the sections of
the copy taken down, and the remaining ones still glue.

## When the sections do not glue

Without honest owners the sections may fail to glue, and then a fork is the
reason: two copies of one line whose histories are not prefixes of one
another, each ending in a version signed with a current key of a version
of its owner's key log that the world holds (`Events.fork_signed`, in the
model): the owner's keys, or keys that whoever held its rotation keys put
there. This is the reading of version 0.2:
a world whose sections do not glue shows a fork of a line, "attributable to
whoever holds" the keys (section 7.4), never a failure of the archives that
hold the copies.

    /-- **Only a fork stops the sections from gluing.** If the sections of a world
    built by events are not compatible, two copies of some line, neither of which
    extends the other, both end in versions signed with current keys of the
    owner's key log as the world holds it. -/
    theorem no_glue_fork {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) (hnc : ¬ Compatible (sections w)) :
        ∃ l b b' o o', lookup w b (.line l) = some (.live o) ∧
          lookup w b' (.line l) = some (.live o') ∧ ¬ Comparable o.versions o'.versions ∧
          HeadSigned E w l o ∧ HeadSigned E w l o' := by
      apply Classical.byContradiction
      intro hno
      apply hnc
      apply compatible_of_agree (SoundWorld.wfObjects E (Events.sound E hs))
      intro l b b' o o' hl hl' hk hk'
      apply Classical.byContradiction
      intro hfork
      obtain ⟨h1, h2, _⟩ := Events.fork_signed E hs hl hl' hk hk' hfork
      exact hno ⟨l, b, b', o, o', hl, hl', hfork, h1, h2⟩

## Holding

A live copy of a line, not a key log, kept anywhere, *holds* a named
document version with an object version. A world holds a named document
version exactly when some version of some copy holds it, and every version
of a live copy holds a named document version of the world. The
invariants of the model used by the later chapters are gathered as `Kept`:
a sound world whose copies agree.

    /-- A live copy of a line, not a key log, kept anywhere, holds the named
    document version `x` with the object version `v`. -/
    def Holds (w : World D) (x : Name) (v : Version D) : Prop :=
      ∃ b l c, lookup w b (.line l) = some (.live c) ∧ c.kind ≠ .owner ∧ v ∈ c.versions ∧
        c.name v = x

    /-- What the later chapters need of a world: a sound world, whose copies of
    each line agree. -/
    abbrev Kept (w : World D) : Prop := SoundWorld E w ∧ ∀ l, CopiesAgree w l

    theorem Events.kept {w : World D} (hs : Events E (fun _ => (none : Option (Archive D))) w)
        {H : Histories D} (hh : Honest E H w) : Kept E w :=
      ⟨Events.sound E hs, fun l => Events.copiesAgree E hs (hh.one E l)⟩

    theorem heldIn_of_live {w : World D} (hw : SoundWorld E w) {b : ArchiveId} {l : LineId}
        {c : Obj D} (hl : lookup w b (.line l) = some (.live c)) (hk : c.kind ≠ .owner)
        {v : Version D} (hv : v ∈ c.versions) : HeldIn w (c.name v) :=
      ⟨⟨b, l, c, hl, hk, c.versions.length⟩,
        (covers_iff ((hw.1 _ _ _ hl).history hk) _ _).mpr
          ⟨v, by rw [List.take_length]; exact hv, rfl⟩⟩

    theorem heldIn_iff {w : World D} (hw : SoundWorld E w) (x : Name) :
        HeldIn w x ↔ ∃ v, Holds w x v := by
      constructor
      · rintro ⟨⟨b, l, c, hl, hk, n⟩, hx⟩
        obtain ⟨v, hv, rfl⟩ := (covers_iff ((hw.1 _ _ _ hl).history hk) n _).mp hx
        exact ⟨v, b, l, c, hl, hk, List.mem_of_mem_take hv, rfl⟩
      · rintro ⟨v, b, l, c, hl, hk, hv, rfl⟩
        exact heldIn_of_live E hw hl hk hv

Two versions holding the same named document version have the same
content, in a world whose objects are well formed and whose copies agree:
their copies are prefixes of one another, and a number has one content.

    /-- Two versions holding the same named document version have the same
    content. -/
    theorem holds_agree {w : World D} (hw : SoundWorld E w) (hca : ∀ l, CopiesAgree w l)
        {x : Name} {v v' : Version D} (h : Holds w x v) (h' : Holds w x v') :
        sameContent v v' = true := by
      obtain ⟨b, l, c, hl, hk, hv, rfl⟩ := h
      obtain ⟨b', l', c', hl', hk', hv', hn⟩ := h'
      simp only [Obj.name, Name.mk.injEq] at hn
      obtain ⟨hi, hd⟩ := hn
      have hll : l' = l := by
        have h1 := (hw.1 _ _ _ hl).id
        have h2 := (hw.1 _ _ _ hl').id
        exact ObjectId.line.inj (h2.symm.trans (hi.trans h1))
      subst hll
      rcases hca l' _ _ _ _ hl' hl hk' hk with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact one_number_one_content ((hw.1 _ _ _ hl).history hk)
          (hv) (by rw [ht]; exact List.mem_append_left _ hv') hd.symm
      · exact one_number_one_content ((hw.1 _ _ _ hl').history hk')
          (by rw [ht]; exact List.mem_append_left _ hv) hv' hd.symm

The value of a glued section at a point is the content of any version
holding it.

    /-- The value of a glued section is the content of any version holding the
    point. -/
    theorem glue_value {w : World D} (hw : SoundWorld E w) {g : Sec (HeldIn w) (Content D)}
        (hg : Glues (sections w) g) {x : Name} {v : Version D} (h : Holds w x v)
        (hx : HeldIn w x) : g x hx = v.content := by
      obtain ⟨b, l, c, hl, hk, hv, rfl⟩ := h
      have hwf := (hw.1 _ _ _ hl).history hk
      have hc : Covers c c.versions.length (c.name v) :=
        (covers_iff hwf _ _).mpr ⟨v, by rw [List.take_length]; exact hv, rfl⟩
      have := congrFun (congrFun (hg ⟨b, l, c, hl, hk, c.versions.length⟩) (c.name v)) hc
      exact this.trans (objSec_piece hwf (by rw [List.take_length]; exact hv) hc)

## A check made piece by piece

The second half of the rule of section 4.2 is a local condition: below a
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

    /-- Each object version satisfies it (section 4.2). -/
    theorem objSec_newContent {o : Obj D} (hwf : WellFormed o.versions) (n : Nat) :
        (objSec o n).Satisfies deposit (covers_open o n) NewContent := by
      intro x hx y hy hne heq
      have hyx := covers_open o n hy hx
      obtain ⟨v, hv, rfl⟩ := (covers_iff hwf n x).mp hx
      obtain ⟨u, hu, rfl⟩ := (covers_iff hwf n y).mp hyx
      have heq' : objSec o n (o.name u) hyx = objSec o n (o.name v) hx := heq
      rw [objSec_piece hwf hu, objSec_piece hwf hv] at heq'
      exact hne (one_content_one_number hwf (List.mem_of_mem_take hu)
        (List.mem_of_mem_take hv) (content_eq_iff.mp heq'))

    /-- **So does the glued section**, which takes its values from many copies. -/
    theorem world_newContent {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {g : Sec (HeldIn w) (Content D)}
        (hg : Glues (sections w) g) : g.Satisfies deposit (heldIn_open w) NewContent :=
      glue_satisfies deposit (fun i => covers_open i.obj i.version) hg NewContent
        fun i => objSec_newContent (((Events.sound E hs).1 _ _ _ i.live).history i.kind) i.version

    end OpenSheaf.Sheaf
