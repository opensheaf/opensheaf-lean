# The citable section

A citation by name refers to a named document version at some time; the
reader resolves it later. This chapter puts all the times together. It
takes a *run*, worlds over time from nothing, each the result of one event
on the one before (or the same world again, so that a finite history is a
run that stops changing), and proves, when owners are honest:

- **the citable section**: the glued sections of all the worlds of a run
  glue, over time, into exactly one section over everything ever held
  (`citable_glues`); the world at each time is its restriction to what that
  world holds.

So there are two objects: what a citation means, a section fixed for all
time over everything ever held, and what is available now, a smaller open
set of it. A takedown shrinks the second and never changes the first.

Version 0.1 of this program also proved that each name is held during one
interval of time, after which every pin into its object, in its own
archive, reports `removed`. Both rested on the fact that a name held
nowhere is never held again, which version 0.2 gives up: a line taken down
everywhere may come back, from a copy or deposited again by its owner
(sections 6.5 and 13.2), and its names are then held again, with the same
content (chapter [Names are eternal](70-eternal.md)). In version 0.2 a name
may be held during several intervals, and there is no own archive whose
tombstone would report it removed; the citable section does not change.

    -- in Sheaf/Citable.lean:
    import Sheaf.Eternal

    namespace OpenSheaf.Sheaf

## Runs

    variable {D : Type} [DecidableEq D] (E : Env D)

    /-- A run: worlds over time, from nothing, each the result of one event on
    the one before, or the same world again. -/
    structure Run where
      world : Nat → World D
      start : world 0 = fun _ => none
      step : ∀ n, Event E (world n) (world (n + 1)) ∨ world (n + 1) = world n

    variable {E} (r : Run E) {H : Histories D} (hh : ∀ n, Honest E H (r.world n))

A run gives events between any two of its times, and from nothing to any
time.

    theorem Run.events {m n : Nat} (h : m ≤ n) : Events E (r.world m) (r.world n) := by
      induction h with
      | refl => exact .refl _
      | step _ ih =>
        rcases r.step _ with he | he
        · exact .tail ih he
        · rw [he]; exact ih

    theorem Run.from_empty (n : Nat) :
        Events E (fun _ => (none : Option (Archive D))) (r.world n) := by
      have := r.events (Nat.zero_le n)
      rw [r.start] at this
      exact this

## The citable section

At each time the world has one glued section, when owners are honest.
Everything ever held is the union, over time, of what each world holds; it
is open.

    /-- The glued section of the world at time `n`. -/
    noncomputable def Run.glued (n : Nat) : Sec (HeldIn (r.world n)) (Content D) :=
      Classical.choose (world_glues E (r.from_empty n) (hh n))

    theorem Run.glued_spec (n : Nat) : Glues (sections (r.world n)) (r.glued hh n) :=
      (Classical.choose_spec (world_glues E (r.from_empty n) (hh n))).1

    /-- The named document versions held at some time of the run: everything a
    citation by name can ever refer to. -/
    def Ever : Name → Prop := Union fun n => HeldIn (r.world n)

    theorem ever_open : deposit.IsOpen (Ever r) :=
      deposit.union_open fun n => heldIn_open (r.world n)

The glued sections of two times agree wherever both are defined, since
names are eternal (chapter [Names are eternal](70-eternal.md)). So they form
a compatible family, indexed by time, and glue.

    /-- The glued sections of all times are compatible. -/
    theorem time_compatible : Compatible (fun n => r.glued hh n) := by
      intro m n x hm hn
      exact glue_eternal E (r.from_empty m) (r.from_empty n) (hh m) (hh n) (r.glued_spec hh m)
        (r.glued_spec hh n) hm hn

    /-- **The citable section.** The worlds of a run glue, over time, into exactly
    one section over everything ever held, when owners are honest; the world at
    each time is its restriction to what that world holds. -/
    theorem citable_glues :
        ∃ C : Sec (Ever r) (Content D), Glues (fun n => r.glued hh n) C ∧
          ∀ C', Glues (fun n => r.glued hh n) C' → C' = C :=
      sheaf (time_compatible r hh)

    end OpenSheaf.Sheaf
