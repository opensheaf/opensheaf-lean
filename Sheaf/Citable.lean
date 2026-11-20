-- Generated from literate-sheaf/79-citable.md by opensheaf-literate: edit the document, not this file.
import Sheaf.Eternal

namespace OpenSheaf.Sheaf

variable {D : Type} [DecidableEq D] (E : Env D)

/-- A run: worlds over time, from nothing, each the result of one event on
the one before, or the same world again. -/
structure Run where
  world : Nat → World D
  start : world 0 = fun _ => none
  step : ∀ n, Event E (world n) (world (n + 1)) ∨ world (n + 1) = world n

variable {E} (r : Run E) {H : Histories D} (hh : ∀ n, Honest E H (r.world n))

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
