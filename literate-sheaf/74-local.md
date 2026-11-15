# Verification is local

The home page of OpenSheaf says that archives are kept and verified
separately, "while every piece stays checkable on its own". This chapter
makes the claim precise in two ways.

- **Restricting the world restricts the sheaf.** Keep only some of the
  entries of a world, and drop the others. The glued section of the whole
  world, restricted to what the part holds, glues the part
  (`restrict_glue`). So the parts of a world are the restrictions of its
  sheaf: a part never says anything the whole does not.
- **Verification is local.** The verdicts on a collection version, and on
  every collection version below it in the order with pins, are the same
  in the *support* of the collection as in the whole world
  (`verify_local`). The support is the copies that hold something below
  the collection, and the tombstones that its member lists pin, which stand
  for the objects taken down. Nothing else in the world, however large, can change what a
  verifier of the collection finds.

    -- in Sheaf/Local.lean:
    import Sheaf.Lifting
    import OpenSheaf.Patterns

    namespace OpenSheaf.Sheaf

    open OpenSheaf.Patterns

    variable {D : Type}

## Parts of a world

A part of a world keeps the entries at the places of a set `S`, and drops
the others; the archives stay.

    /-- The part of a world at the places of `S`: every other entry is dropped. -/
    def restrictW (S : ArchiveId → ObjectId → Prop) [∀ a i, Decidable (S a i)] (w : World D) :
        World D :=
      fun a => (w a).map fun ar => { ar with entries := fun i => if S a i then ar.entries i else none }

    theorem lookup_restrict (S : ArchiveId → ObjectId → Prop) [∀ a i, Decidable (S a i)]
        (w : World D) (a : ArchiveId) (i : ObjectId) :
        lookup (restrictW S w) a i = if S a i then lookup w a i else none := by
      unfold lookup restrictW
      cases w a <;> by_cases h : S a i <;> simp [h]

    theorem restrict_live {S : ArchiveId → ObjectId → Prop} [∀ a i, Decidable (S a i)]
        {w : World D} {a : ArchiveId} {i : ObjectId} {c : Obj D}
        (h : lookup (restrictW S w) a i = some (.live c)) : lookup w a i = some (.live c) := by
      rw [lookup_restrict] at h
      split at h
      · exact h
      · cases h

A source of a part is a source of the world, and what a part holds the
world holds.

    /-- A source of the part is a source of the world. -/
    def Source.lift {S : ArchiveId → ObjectId → Prop} [∀ a i, Decidable (S a i)] {w : World D}
        (i : Source (restrictW S w)) : Source w :=
      ⟨i.archive, i.id, i.obj, restrict_live i.live, i.version⟩

    theorem heldIn_restrict (S : ArchiveId → ObjectId → Prop) [∀ a i, Decidable (S a i)]
        (w : World D) : Sub (HeldIn (restrictW S w)) (HeldIn w) :=
      fun _ ⟨i, hx⟩ => ⟨i.lift, hx⟩

So the glued section of the world restricts to a section that glues the
part: the presheaf restriction, realised by dropping entries.

    /-- **Restricting the world restricts the sheaf.** The glued section of a
    world, restricted to what a part of it holds, glues the part. -/
    theorem restrict_glue (S : ArchiveId → ObjectId → Prop) [∀ a i, Decidable (S a i)]
        {w : World D} {g : Sec (HeldIn w) (Content D)} (hg : Glues (sections w) g) :
        Glues (sections (restrictW S w)) (g.restrict (heldIn_restrict S w)) := by
      intro i
      funext x hx
      exact congrFun (congrFun (hg i.lift) x) hx

## The support of a collection

The support of a named document version `x` is the places a verifier needs
to check `x` and everything below it: the copies that hold a named document
version below `x`, and the tombstones its member lists pin.

    variable [DecidableEq D] (hash : Hash D)

    /-- The places of a world that a verifier of `x` and everything below it
    needs: the copies that hold a named document version below `x`, and the
    tombstones that a member list below `x` pins. -/
    def Support (w : World D) (x : Name) (a : ArchiveId) (i : ObjectId) : Prop :=
      (∃ c, lookup w a i = some (.live c) ∧ ∃ v ∈ c.versions, (byPins hash w).le (c.name v) x) ∨
        ((∃ n d, lookup w a i = some (.tomb n d)) ∧
          ∃ b j c v p, lookup w b j = some (.live c) ∧ v ∈ c.versions ∧
            (byPins hash w).le (c.name v) x ∧ p ∈ v.memberPins ∧ p.archive = a ∧ p.object = i)

In a world built by events, every pin of a member list held below `x`
resolves to a version below `x`, or reports `removed`
([Collections and what they pin](55-collections.md)). In both cases the
place it names is in the support, which therefore resolves it as the whole
world does.

    /-- **Verification is local.** In a world built by events, every member list
    held below `x` verifies in the support of `x` exactly as in the whole world. -/
    theorem verify_local {w : World D}
        (hs : Events hash (fun _ => (none : Option (Archive D))) w) {x : Name}
        [∀ a i, Decidable (Support hash w x a i)] {b : ArchiveId} {i : ObjectId} {c : Obj D}
        {v : Version D} {ms : Members D} (hl : lookup w b i = some (.live c))
        (hv : v ∈ c.versions) (hm : v.members = some ms) (hle : (byPins hash w).le (c.name v) x) :
        verify hash (restrictW (Support hash w x) w) ms = verify hash w ms := by
      unfold verify
      apply List.map_congr_left
      intro p hp
      have hpm : p ∈ v.memberPins := by unfold Version.memberPins; rw [hm]; exact hp
      have hS : Support hash w x p.archive p.object := by
        rcases members_below hash hs hl hv hpm with ⟨o, u, ho, hr, hle'⟩ | hr
        · have hre : resolveEntry hash (some (.live o)) p = .ok u := by
            unfold resolve at hr; rw [ho] at hr; exact hr
          exact Or.inl ⟨o, ho, u, versionAt_mem (resolveEntry_live_ok hash hre).1,
            (byPins hash w).trans hle' hle⟩
        · exact Or.inr ⟨(resolve_removed_iff hash).mp hr, b, i, c, v, p, hl, hv, hle, hpm, rfl, rfl⟩
      unfold resolve
      rw [lookup_restrict, if_yes hS]

    end OpenSheaf.Sheaf
