-- Generated from literate/70-story.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Patterns

namespace OpenSheaf.Story

open OpenSheaf OpenSheaf.Patterns

/-- A toy digest of an inventory. -/
def toy : Hash Nat := fun l =>
  l.foldl (fun h v => 31 * h + v.description.length + 7 * v.documentVersion
    + v.files.length) l.length

def v1 : Version Nat :=
  { documentVersion := 1, files := [("paper.tm", 101), ("paper.pdf", 102)],
    description := "On sheaves of documents", depositor := "author",
    message := "first version" }

def paper : Obj Nat := { id := "paper", kind := .document, versions := [v1] }

def pinV1 : Pin Nat := ⟨"author", "paper", 1, toy [v1]⟩

def issue7 : Members Nat :=
  { type := .selection,
    members := [{ archive := "author", object := "paper", pins := [pinV1] }] }

def pinNotes : Pin Nat := ⟨"coauthor", "notes", 1, 999⟩

def joint : Members Nat :=
  { type := .catalogue,
    members := [{ archive := "author", object := "paper", follow := true, pins := [pinV1] },
                { archive := "coauthor", object := "notes", pins := [pinNotes] }] }

def authorArchive : Archive Nat :=
  { id := "author", entries := fun x => if x = "paper" then some (.live paper) else none }

def w0 : World Nat := fun a => if a = "author" then some authorArchive else none

example : resolve toy w0 pinV1 = .ok v1 := by decide

example : resolve toy w0 ⟨"author", "paper", 1, 0⟩ = .mismatch := by decide

example : resolve toy w0 ⟨"author", "paper", 2, toy [v1]⟩ = .missing := by decide

example : verify toy w0 joint = [(pinV1, .ok v1), (pinNotes, .missing)] := by decide

def v2 : Version Nat :=
  v1.revise [("paper.tm", 201), ("paper.pdf", 202)] none
    "On sheaves of documents" "author" "revised after the referees' comments"

def w1 : World Nat := setEntry w0 "author" "paper" (.live (paper.append v2))

example : v2.documentVersion = 2 := by decide

def v3 : Version Nat := v2.describe "On sheaves of documents (corrected)" "author" "title"

def paper2 : Obj Nat := paper.append v2

def w2 : World Nat := setEntry w1 "author" "paper" (.live (paper2.append v3))

example : v3.documentVersion = 2 := by decide

example : WellFormed [v1, v2, v3] := by
  simp [WellFormed, ChainFrom, Follows, sameContent, v1, v2, v3,
    Version.revise, Version.describe]

example : verify toy w2 issue7 = verify toy w0 issue7 := by decide

example : verify toy w2 issue7 = [(pinV1, .ok v1)] := by decide

example : collect toy w2 issue7 = issue7 := by decide

def pinV3 : Pin Nat := ⟨"author", "paper", 3, toy [v1, v2, v3]⟩

example : collect toy w2 joint =
    { joint with members :=
        [{ archive := "author", object := "paper", follow := true, pins := [pinV3] },
         { archive := "coauthor", object := "notes", pins := [pinNotes] }] } := by decide

example : resolve toy w2 pinV3 = .ok v3 := by decide

example : resolve toy w2 ⟨"author", "paper", 3, toy [v1]⟩ = .mismatch := by decide

def w3 : World Nat := takedown toy w2 "author" "paper" (paper2.append v3)

example : verify toy w3 issue7 = [(pinV1, .removed)] := by decide

example : resolve toy w3 pinV3 = .removed := by decide

example : resolve toy w3 ⟨"author", "paper", 1, 0⟩ = .mismatch := by decide

theorem w0_to_w2 : Steps w0 w2 :=
  .tail (.tail (.refl w0) (Step.append w0 "author" authorArchive "paper" paper v2 rfl rfl))
    (Step.append w1 "author" _ "paper" paper2 v3 rfl rfl)

example : verify toy w2 issue7 = verify toy w0 issue7 ∧ collect toy w2 issue7 = issue7 :=
  selection_stable toy w0_to_w2 rfl (by
    intro p hp
    simp [allPins, issue7] at hp
    subst hp
    exact ⟨v1, by decide⟩)

end OpenSheaf.Story
