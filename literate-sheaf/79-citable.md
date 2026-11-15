# The citable section

A citation by name refers to a named document version at some time; the
reader resolves it later. This chapter puts all the times together. It
takes a *run*, worlds over time from nothing, each the result of one event
on the one before (or the same world again, so that a finite history is a
run that stops changing), and proves:

- **the citable section**: the glued sections of all the worlds of a run glue,
  over time, into exactly one section over everything ever held
  (`citable_glues`); the world at each time is its restriction to what that
  world holds;
- **each name is held during one interval of time**: held at two times, it
  is held at every time between (`held_interval`);
- **after its interval, a name is reported removed**: every pin into its
  object, in its own archive, reports `removed` (`gone_removed`).

So there are two objects: what a citation means, a section fixed for all
time over everything ever held, and what is available now, a smaller open
set of it. A takedown shrinks the second and never changes the first.

    -- in Sheaf/Citable.lean:
    import Sheaf.Eternal

    namespace OpenSheaf.Sheaf

## Runs

    variable {D : Type} [DecidableEq D] (hash : Hash D)

    /-- A run: worlds over time, from nothing, each the result of one event on
    the one before, or the same world again. -/
    structure Run where
      world : Nat → World D
      start : world 0 = fun _ => none
      step : ∀ n, Event hash (world n) (world (n + 1)) ∨ world (n + 1) = world n

    variable {hash} (r : Run hash)

A run gives events between any two of its times, and from nothing to any
time.

    theorem Run.events {m n : Nat} (h : m ≤ n) : Events hash (r.world m) (r.world n) := by
      induction h with
      | refl => exact .refl _
      | step _ ih =>
        rcases r.step _ with he | he
        · exact .tail ih he
        · rw [he]; exact ih

    theorem Run.from_empty (n : Nat) :
        Events hash (fun _ => (none : Option (Archive D))) (r.world n) := by
      have := r.events (Nat.zero_le n)
      rw [r.start] at this
      exact this

## The citable section

At each time the world has one glued section. Everything ever
held is the union, over time, of what each world holds; it is open.

    /-- The glued section of the world at time `n`. -/
    noncomputable def Run.glued (n : Nat) : Sec (HeldIn (r.world n)) (Content D) :=
      Classical.choose (world_glues hash (r.from_empty n))

    theorem Run.glued_spec (n : Nat) : Glues (sections (r.world n)) (r.glued n) :=
      (Classical.choose_spec (world_glues hash (r.from_empty n))).1

    /-- The named document versions held at some time of the run: everything a
    citation by name can ever refer to. -/
    def Ever : Name → Prop := Union fun n => HeldIn (r.world n)

    theorem ever_open : deposit.IsOpen (Ever r) :=
      deposit.union_open fun n => heldIn_open (r.world n)

The glued sections of two times agree wherever both are defined, since
names are eternal (chapter [Names are eternal](70-eternal.md)). So they form
a compatible family, indexed by time, and glue.

    /-- The glued sections of all times are compatible. -/
    theorem time_compatible : Compatible (fun n => r.glued n) := by
      intro m n x hm hn
      rcases Nat.le_total m n with h | h
      · exact glue_eternal hash (r.from_empty m) (r.events h) (r.glued_spec m) (r.glued_spec n) hm hn
      · exact (glue_eternal hash (r.from_empty n) (r.events h) (r.glued_spec n)
          (r.glued_spec m) hn hm).symm

    /-- **The citable section.** The worlds of a run glue, over time, into exactly
    one section over everything ever held, and the world at each time is its
    restriction to what that world holds. -/
    theorem citable_glues :
        ∃ C : Sec (Ever r) (Content D), Glues (fun n => r.glued n) C ∧
          ∀ C', Glues (fun n => r.glued n) C' → C' = C :=
      sheaf (time_compatible r)

## Intervals and removal

A name held at two times is held between them: otherwise it would be held
again after being held nowhere, which cannot happen (`no_resurrection`).

    /-- **Each name is held during one interval of time.** Held at two times, it
    is held at every time between. -/
    theorem held_interval {x : Name} {m k n : Nat} (hmk : m ≤ k) (hkn : k ≤ n)
        (hm : HeldIn (r.world m) x) (hn : HeldIn (r.world n) x) : HeldIn (r.world k) x := by
      apply Classical.byContradiction
      intro hk
      have hs0 := r.from_empty m
      obtain ⟨v, hv⟩ := (heldIn_iff hash (Events.sound hash hs0) x).mp hm
      have hgone : ∀ v', ¬ Holds (r.world k) x v' := fun v' hv' =>
        hk ((heldIn_iff hash (Events.sound hash (r.from_empty k)) x).mpr ⟨v', hv'⟩)
      obtain ⟨v'', hv''⟩ := (heldIn_iff hash (Events.sound hash (r.from_empty n)) x).mp hn
      exact no_resurrection hash hs0 (r.events hmk) (r.events hkn) hv hgone v'' hv''

After its interval, a name's object has been taken down in its own
archive, so a pin into it there reports `removed`, as section 11.3 asks:
the citation keeps its meaning, and the reader is told why it cannot be
followed.

    /-- **After its interval, a name is reported removed.** Once a name held
    earlier is held nowhere, every pin into its object, in its own archive,
    reports `removed`. -/
    theorem gone_removed {x : Name} {m n : Nat} (hmn : m ≤ n) (hm : HeldIn (r.world m) x)
        (hn : ¬ HeldIn (r.world n) x) {p : Pin D} (hp : p.archive = x.archive ∧ p.object = x.object) :
        resolve hash (r.world n) p = .removed := by
      have hs0 := r.from_empty m
      obtain ⟨v, hv⟩ := (heldIn_iff hash (Events.sound hash hs0) x).mp hm
      rcases ((Events.eternal hash hs0 (r.events hmn)).2 x v hv).2 with ⟨v', hv'⟩ | ⟨k, d, ht⟩
      · exact absurd ((heldIn_iff hash (Events.sound hash (r.from_empty n)) x).mpr ⟨v', hv'⟩) hn
      · exact (resolve_removed_iff hash).mpr ⟨k, d, by rw [hp.1, hp.2]; exact ht⟩

    end OpenSheaf.Sheaf
