-- Generated from literate-sheaf/79-citable.md by opensheaf-literate: edit the document, not this file.
import Sheaf.Eternal

namespace OpenSheaf.Sheaf

variable {D : Type} [DecidableEq D] (hash : Hash D)

/-- A run: worlds over time, from nothing, each the result of one event on
the one before, or the same world again. -/
structure Run where
  world : Nat → World D
  start : world 0 = fun _ => none
  step : ∀ n, Event hash (world n) (world (n + 1)) ∨ world (n + 1) = world n

variable {hash} (r : Run hash)

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

/-- The glued section of the world at time `n`. -/
noncomputable def Run.glued (n : Nat) : Sec (HeldIn (r.world n)) (Content D) :=
  Classical.choose (world_sheaf hash (r.from_empty n))

theorem Run.glued_spec (n : Nat) : Glues (sections (r.world n)) (r.glued n) :=
  (Classical.choose_spec (world_sheaf hash (r.from_empty n))).1

/-- The named document versions held at some time of the run: everything a
citation by name can ever refer to. -/
def Ever : Name → Prop := Union fun n => HeldIn (r.world n)

theorem ever_open : deposit.IsOpen (Ever r) :=
  deposit.union_open fun n => heldIn_open (r.world n)

/-- The glued sections of all times are compatible. -/
theorem time_compatible : Compatible (fun n => r.glued n) := by
  intro m n x hm hn
  rcases Nat.le_total m n with h | h
  · exact glue_eternal hash (r.from_empty m) (r.events h) (r.glued_spec m) (r.glued_spec n) hm hn
  · exact (glue_eternal hash (r.from_empty n) (r.events h) (r.glued_spec n)
      (r.glued_spec m) hn hm).symm

/-- **The citable sheaf.** The worlds of a run glue, over time, into exactly
one section over everything ever held, and the world at each time is its
restriction to what that world holds. -/
theorem citable_sheaf :
    ∃ C : Sec (Ever r) (Content D), Glues (fun n => r.glued n) C ∧
      ∀ C', Glues (fun n => r.glued n) C' → C' = C :=
  sheaf (time_compatible r)

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
