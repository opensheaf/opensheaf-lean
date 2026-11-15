-- Generated from literate-sheaf/60-story.md by opensheaf-literate: edit the document, not this file.
import Sheaf.Collections
import OpenSheaf.Story

namespace OpenSheaf.Sheaf.Story

open OpenSheaf OpenSheaf.Story OpenSheaf.Sheaf

theorem events : Events toy (fun _ => (none : Option (Archive Nat))) w14 :=
  ValidSteps.toEvents toy story

theorem story_sheaf :
    ∃ g, Glues (sections w14) g ∧ ∀ g', Glues (sections w14) g' → g' = g :=
  world_glues toy events

def authorPaper : Source w14 := ⟨"author", "paper", paper3, rfl, 3⟩
def coauthorPaper : Source w14 := ⟨"coauthor", "paper", paper3, rfl, 1⟩
def acceptedPaper : Source w14 := ⟨"journal", "paper-accepted", copy, rfl, 1⟩

def first : Name := ⟨"author", "paper", 1⟩
def second : Name := ⟨"author", "paper", 2⟩

theorem first_author : cover w14 authorPaper first := by decide
theorem first_coauthor : cover w14 coauthorPaper first := by decide
theorem second_author : cover w14 authorPaper second := by decide
example : ¬ cover w14 coauthorPaper second := by decide

example : sections w14 authorPaper first first_author =
    sections w14 coauthorPaper first first_coauthor :=
  world_compatible toy events _ _ _ _ _

example : sections w14 authorPaper first first_author = v3.content :=
  objSec_piece (o := paper3) (n := 3) (v := v3) (by decide) (by decide) first_author

example : sections w14 authorPaper first first_author ≠
    sections w14 authorPaper second second_author := by
  intro h
  have := content_eq_iff.mp
    ((objSec_piece (o := paper3) (n := 3) (v := v1) (by decide) (by decide) first_author).symm.trans
      (h.trans (objSec_piece (o := paper3) (n := 3) (v := v2) (by decide) (by decide) second_author)))
  revert this; decide

def accepted : Name := ⟨"journal", "paper-accepted", 1⟩

theorem accepted_held : cover w14 acceptedPaper accepted := by decide

example : sections w14 acceptedPaper accepted accepted_held =
    sections w14 authorPaper first first_author := by
  show objSec copy 1 accepted accepted_held = objSec paper3 3 first first_author
  rw [show objSec copy 1 accepted accepted_held = v1.content from
      acceptedCopy_value _ _ _ _ _ _ _ rfl accepted_held]
  exact (objSec_piece (o := paper3) (n := 3) (v := v1) (by decide) (by decide) first_author).symm

def issue1 : Name := ⟨"journal", "issue-7", 1⟩

theorem paper_below_issue : (byPins toy w14).le first issue1 :=
  Star.tail (Star.refl _)
    (Or.inr ⟨"journal", "issue-7", issue, i1, pinV1, paper3, v1, rfl, by decide, rfl,
      by decide, rfl, by decide, rfl⟩)

example {g : Sec (HeldIn w14) (Content Nat)} (hg : Glues (sections w14) g)
    (hy : HeldIn w14 first) : g first hy = v1.content :=
  glue_at_member toy events hg (p := pinV1) (o := paper3) (u := v1) rfl (by decide) hy

def v1' : Version Nat := { v1 with files := [("paper.tm", 666), ("paper.pdf", 102)] }
def forged : Obj Nat := { paper with versions := [v1'] }
def wForged : World Nat := setEntry w14 "coauthor" "paper" (.live forged)

example : WellFormed forged.versions := by decide

def authorPaper' : Source wForged := ⟨"author", "paper", paper3, rfl, 3⟩
def forgedPaper : Source wForged := ⟨"coauthor", "paper", forged, rfl, 1⟩

theorem forged_incompatible : ¬ Compatible (sections wForged) := by
  intro h
  have h1 : cover wForged authorPaper' first := by decide
  have h2 : cover wForged forgedPaper first := by decide
  have heq := h authorPaper' forgedPaper first h1 h2
  have e1 : sections wForged authorPaper' first h1 = v1.content :=
    objSec_piece (o := paper3) (n := 3) (v := v1) (by decide) (by decide) h1
  have e2 : sections wForged forgedPaper first h2 = v1'.content :=
    objSec_piece (o := forged) (n := 1) (v := v1') (by decide) (by decide) h2
  have := content_eq_iff.mp (e1.symm.trans (heq.trans e2))
  revert this; decide

example (hash : Hash Nat) : ¬ Events hash (fun _ => (none : Option (Archive Nat))) wForged :=
  fun hs => forged_incompatible (world_compatible hash hs)

def bad : Obj Nat := { paper with versions := [v1, v1'] }

example : ¬ WellFormed bad.versions := by decide

example : ¬ Compatible (pieces bad 2) := by
  intro h
  have := content_eq_iff.mp (h ⟨v1, by decide⟩ ⟨v1', by decide⟩ (bad.name v1) rfl rfl)
  revert this; decide

end OpenSheaf.Sheaf.Story
