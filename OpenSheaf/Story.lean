-- Generated from literate/70-story.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Copies
import OpenSheaf.Patterns

namespace OpenSheaf.Story

open OpenSheaf OpenSheaf.Patterns

/-- A toy digest of an inventory. -/
def toy : Hash Nat := fun l =>
  l.foldl (fun h v => 31 * h + v.description.length + 7 * v.documentVersion
    + v.files.length + v.depositor.length) l.length

/-- The result is a version. -/
def _root_.OpenSheaf.Resolution.isOk {D : Type} : Resolution D → Bool
  | .ok _ => true
  | _ => false

theorem exists_of_isOk {D : Type} {r : Resolution D} (h : r.isOk = true) :
    ∃ t, r = .ok t := by
  cases r <;> simp_all [Resolution.isOk]

def emptyArchive (a : ArchiveId) : Archive Nat := { id := a, entries := fun _ => none }

def w0 : World Nat := fun _ => none
def w1 : World Nat := fun b => if b = "author" then some (emptyArchive "author") else w0 b
def w2 : World Nat := fun b => if b = "journal" then some (emptyArchive "journal") else w1 b
def w3 : World Nat := fun b => if b = "coauthor" then some (emptyArchive "coauthor") else w2 b

theorem s1 : ValidStep toy w0 w1 := .newArchive _ _ _ rfl fun _ => rfl
theorem s2 : ValidStep toy w1 w2 := .newArchive _ _ _ rfl fun _ => rfl
theorem s3 : ValidStep toy w2 w3 := .newArchive _ _ _ rfl fun _ => rfl

def v1 : Version Nat :=
  { documentVersion := 1, files := [("paper.tm", 101), ("paper.pdf", 102)],
    description := "On sheaves of documents", depositor := "author",
    message := "first version" }

def paper : Obj Nat := { id := "paper", kind := .document, versions := [v1] }

def n1 : Version Nat :=
  { documentVersion := 1, files := [("notes.md", 301)], description := "Notes",
    depositor := "coauthor", message := "notes" }

def notes : Obj Nat := { id := "notes", kind := .document, versions := [n1] }

def w4 : World Nat := setEntry w3 "author" "paper" (.live paper)
def w5 : World Nat := setEntry w4 "coauthor" "notes" (.live notes)

theorem s4 : ValidStep toy w3 w4 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide⟩ (by simp [paper, v1, Version.pins])

theorem s5 : ValidStep toy w4 w5 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide⟩ (by simp [notes, n1, Version.pins])

def pinV1 : Pin Nat := ⟨"author", "paper", 1, toy [v1]⟩
def pinNotes : Pin Nat := ⟨"coauthor", "notes", 1, toy [n1]⟩

def issue7 : Members Nat :=
  { type := .selection,
    members := [{ archive := "author", object := "paper", pins := [pinV1] }] }

def i1 : Version Nat :=
  { documentVersion := 1, files := [], members := some issue7, description := "Issue 7",
    depositor := "editor", message := "issue 7: the papers accepted" }

def issue : Obj Nat := { id := "issue-7", kind := .collection, versions := [i1] }

def w6 : World Nat := setEntry w5 "journal" "issue-7" (.live issue)

def joint : Members Nat :=
  { type := .catalogue,
    members := [{ archive := "author", object := "paper", follow := true, pins := [pinV1] },
                { archive := "coauthor", object := "notes", pins := [pinNotes] }] }

def j1 : Version Nat :=
  { documentVersion := 1, files := [], members := some joint, description := "Joint papers",
    depositor := "coauthor", message := "joint papers" }

def jointObj : Obj Nat := { id := "joint", kind := .collection, versions := [j1] }

def w7 : World Nat := setEntry w6 "coauthor" "joint" (.live jointObj)

theorem s6 : ValidStep toy w5 w6 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide⟩
    fun v hv p hp => exists_of_isOk ((by decide :
      ∀ v ∈ issue.versions, ∀ p ∈ v.pins, (resolve toy w5 p).isOk = true) v hv p hp)

theorem s7 : ValidStep toy w6 w7 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide⟩
    fun v hv p hp => exists_of_isOk ((by decide :
      ∀ v ∈ jointObj.versions, ∀ p ∈ v.pins, (resolve toy w6 p).isOk = true) v hv p hp)

def w8 : World Nat := setEntry w7 "coauthor" "paper" (.live paper)

theorem s8 : ValidStep toy w7 w8 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide⟩ (by simp [paper, v1, Version.pins])

def v2 : Version Nat :=
  Version.revise [v1] [("paper.tm", 201), ("paper.pdf", 202)] none
    "On sheaves of documents" "author" "revised after the referees' comments"

def v3 : Version Nat := v1.describe "On sheaves of documents, I" "author" "title of version 1"

def paper2 : Obj Nat := paper.append v2
def paper3 : Obj Nat := paper2.append v3

def w9 : World Nat := setEntry w8 "author" "paper" (.live paper2)
def w10 : World Nat := setEntry w9 "author" "paper" (.live paper3)

theorem s9 : ValidStep toy w8 w9 :=
  .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by simp [v2, Version.revise, Version.pins])

theorem s10 : ValidStep toy w9 w10 :=
  .append _ _ _ _ _ _ rfl rfl (by decide) (by decide)
    (by simp [v3, v1, Version.describe, Version.pins])

example : v2.documentVersion = 2 ∧ v3.documentVersion = 1 := by decide

example : ¬ Follows paper2.versions { v1 with documentVersion := 3 } := by decide

example : Follows paper2.versions { v1 with message := "again" } := by decide

def j2 : Version Nat :=
  Version.revise [j1] [] (some (collect toy w10 joint)) "Joint papers" "coauthor"
    "followed: paper"

def w11 : World Nat := setEntry w10 "coauthor" "joint" (.live (jointObj.append j2))

theorem s11 : ValidStep toy w10 w11 :=
  .append _ _ _ _ _ _ rfl rfl (by decide) (by decide)
    fun p hp => exists_of_isOk ((by decide :
      ∀ p ∈ j2.pins, (resolve toy w10 p).isOk = true) p hp)

def w12 : World Nat := setEntry w11 "coauthor" "paper" (.live paper2)
def w13 : World Nat := setEntry w12 "coauthor" "paper" (.live paper3)

theorem s12 : ValidStep toy w11 w12 :=
  .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by simp [v2, Version.revise, Version.pins])

theorem s13 : ValidStep toy w12 w13 :=
  .append _ _ _ _ _ _ rfl rfl (by decide) (by decide)
    (by simp [v3, v1, Version.describe, Version.pins])

def copy : Obj Nat :=
  acceptedCopy "paper-accepted" v1 "On sheaves of documents (accepted)" "editor"
    "accepted copy of paper v1"

def w14 : World Nat := setEntry w13 "journal" "paper-accepted" (.live copy)

theorem s14 : ValidStep toy w13 w14 :=
  .create _ _ _ _ _ rfl rfl (acceptedCopy_wf _ _ _ _ _) (by simp [copy, acceptedCopy, Version.pins])

def pinCopy : Pin Nat := ⟨"journal", "paper-accepted", 1, toy copy.versions⟩

theorem story : ValidSteps toy w0 w14 :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail
    (.tail (.refl _) s1) s2) s3) s4) s5) s6) s7) s8) s9) s10) s11) s12) s13) s14

theorem story_wf : WFWorld toy w14 := story.wf toy (WFWorld.empty toy)

theorem story_pins : PinsOk toy w14 := story.pins_ok toy

example : verify toy w14 issue7 = [(pinV1, .ok v1)] := by decide

example : verify toy w14 issue7 = verify toy w6 issue7 := by decide

example : collect toy w14 issue7 = issue7 := by decide

def pinV3 : Pin Nat := ⟨"author", "paper", 3, toy [v1, v2, v3]⟩

example : j2.members = some
    { joint with members :=
        [{ archive := "author", object := "paper", follow := true, pins := [pinV3] },
         { archive := "coauthor", object := "notes", pins := [pinNotes] }] } := by decide

example : resolve toy w14 pinV3 = .ok v3 := by decide

example : resolve toy w14 ⟨"author", "paper", 3, toy [v1]⟩ = .mismatch := by decide

example : resolve toy w14 ⟨"author", "paper", 4, toy [v1]⟩ = .missing := by decide

example : resolveAt toy w14 "coauthor" pinV3 = .ok v3 := by decide

example : (copy.versions.map (·.files)) = [v1.files] := by decide

def wGone : World Nat := fun b => if b = "author" then none else w14 b

example : resolve toy wGone pinV3 = .missing := by decide

example : resolveVia toy wGone pinV3 ["coauthor"] = .ok v3 := by decide

example : verify toy wGone issue7 = [(pinV1, .missing)] := by decide

example : resolveVia toy wGone pinV1 ["coauthor"] = .ok v1 := by decide

def wDown : World Nat := takedown toy w14 "author" "paper" paper3

example : verify toy wDown issue7 = [(pinV1, .removed)] := by decide

example : resolve toy wDown ⟨"author", "paper", 1, 0⟩ = .removed := by decide

example : resolve toy wDown pinCopy = resolve toy w14 pinCopy := by decide

example : (resolve toy wDown pinCopy).isOk = true := by decide

example : resolveVia toy wDown pinV1 ["coauthor"] = .ok v1 := by decide

theorem w6_to_w14 : Steps w6 w14 :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.refl _)
    (s7.toStep toy)) (s8.toStep toy)) (s9.toStep toy)) (s10.toStep toy))
    (s11.toStep toy)) (s12.toStep toy)) (s13.toStep toy)) (s14.toStep toy)

example : verify toy w14 issue7 = verify toy w6 issue7 ∧ collect toy w14 issue7 = issue7 :=
  selection_stable toy w6_to_w14 rfl fun p hp => exists_of_isOk ((by decide :
    ∀ p ∈ allPins issue7, (resolve toy w6 p).isOk = true) p hp)

example : resolveVia toy wGone pinV3 ["coauthor"] = .ok v3 :=
  have hgone : resolve toy wGone pinV3 = .missing := by decide
  resolveVia_mirror toy (m := paper3) (fun u h => by rw [hgone] at h; cases h)
    rfl (by decide)

end OpenSheaf.Story
