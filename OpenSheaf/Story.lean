-- Generated from literate/70-story.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Impossible
import OpenSheaf.Patterns
import OpenSheaf.Acts

namespace OpenSheaf.Story

open OpenSheaf OpenSheaf.Patterns

/-- A toy digest of an inventory. -/
def toy : Hash Nat := fun i =>
  i.versions.foldl (fun h v => 31 * h + v.description.length + 7 * v.documentVersion
    + v.files.length + v.depositor.length)
    (i.versions.length + 1000 * i.archive.length + 100 * i.id.length)

/-- The result is a version. -/
def _root_.OpenSheaf.Resolution.isOk {D : Type} : Resolution D → Bool
  | .ok _ => true
  | _ => false

theorem exists_of_isOk {D : Type} {r : Resolution D} (h : r.isOk = true) :
    ∃ t, r = .ok t := by
  cases r <;> simp_all [Resolution.isOk]

def emptyArchive (a : ArchiveId) (writers : List Agent) : Archive Nat :=
  { id := a, entries := fun _ => none, writers }

def w0 : World Nat := fun _ => none
def w1 : World Nat := fun b => if b = "author" then some (emptyArchive "author" ["author"]) else w0 b
def w2 : World Nat := fun b => if b = "journal" then some (emptyArchive "journal" ["editor"]) else w1 b
def w3 : World Nat := fun b => if b = "coauthor" then some (emptyArchive "coauthor" ["coauthor"]) else w2 b

theorem s1 : StepBy toy "author" w0 w1 := .newArchive _ _ _ rfl (fun _ => rfl)
  (by decide)
theorem s2 : StepBy toy "editor" w1 w2 := .newArchive _ _ _ rfl (fun _ => rfl)
  (by decide)
theorem s3 : StepBy toy "coauthor" w2 w3 := .newArchive _ _ _ rfl (fun _ => rfl)
  (by decide)

def v1 : Version Nat :=
  { documentVersion := 1, files := [("paper.tm", 101), ("paper.pdf", 102)],
    description := "On sheaves of documents", depositor := "author",
    message := "first version" }

def paper : Obj Nat := { archive := "author", id := "paper", kind := .document, versions := [v1] }

def n1 : Version Nat :=
  { documentVersion := 1, files := [("notes.md", 301)], description := "Notes",
    depositor := "coauthor", message := "notes" }

def notes : Obj Nat := { archive := "coauthor", id := "notes", kind := .document, versions := [n1] }

def w4 : World Nat := setEntry w3 "author" "paper" (.live paper)
def w5 : World Nat := setEntry w4 "coauthor" "notes" (.live notes)

theorem s4 : StepBy toy "author" w3 w4 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide⟩ (by simp [paper, v1, Version.pins])
    (Or.inl rfl) (by decide)
    (by decide)

theorem s5 : StepBy toy "coauthor" w4 w5 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide⟩ (by simp [notes, n1, Version.pins])
    (Or.inl rfl) (by decide)
    (by decide)

def pinV1 : Pin Nat := ⟨"author", "paper", 1, toy (paper.inventory 1)⟩
def pinNotes : Pin Nat := ⟨"coauthor", "notes", 1, toy (notes.inventory 1)⟩

def issue7 : Members Nat :=
  { type := .selection,
    members := [{ archive := "author", object := "paper", pins := [pinV1] }] }

def i1 : Version Nat :=
  { documentVersion := 1, files := [], members := some issue7, description := "Issue 7",
    depositor := "editor", message := "issue 7: the papers accepted" }

def issue : Obj Nat := { archive := "journal", id := "issue-7", kind := .collection, versions := [i1] }

def w6 : World Nat := setEntry w5 "journal" "issue-7" (.live issue)

def joint : Members Nat :=
  { type := .catalogue,
    members := [{ archive := "author", object := "paper", follow := true, pins := [pinV1] },
                { archive := "coauthor", object := "notes", pins := [pinNotes] }] }

def j1 : Version Nat :=
  { documentVersion := 1, files := [], members := some joint, description := "Joint papers",
    depositor := "coauthor", message := "joint papers" }

def jointObj : Obj Nat := { archive := "coauthor", id := "joint", kind := .collection, versions := [j1] }

def w7 : World Nat := setEntry w6 "coauthor" "joint" (.live jointObj)

theorem s6 : StepBy toy "editor" w5 w6 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide⟩
    (fun v hv p hp => exists_of_isOk ((by decide :
      ∀ v ∈ issue.versions, ∀ p ∈ v.pins, (resolve toy w5 p).isOk = true) v hv p hp))
    (Or.inl rfl) (by decide)
    (by decide)

theorem s7 : StepBy toy "coauthor" w6 w7 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide⟩
    (fun v hv p hp => exists_of_isOk ((by decide :
      ∀ v ∈ jointObj.versions, ∀ p ∈ v.pins, (resolve toy w6 p).isOk = true) v hv p hp))
    (Or.inl rfl) (by decide)
    (by decide)

def w8 : World Nat := setEntry w7 "coauthor" "paper" (.live paper)

theorem s8 : StepBy toy "coauthor" w7 w8 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide⟩ (by simp [paper, v1, Version.pins])
    (Or.inr ⟨paper, rfl, rfl, [], by simp⟩) (by decide)
    (by decide)

def v2 : Version Nat :=
  Version.revise [v1] [("paper.tm", 201), ("paper.pdf", 202)] none
    "On sheaves of documents" "author" "revised after the referees' comments"

def v3 : Version Nat :=
  Version.describe [v1, v2] v1 "On sheaves of documents, I" "author" "title of version 1"

def paper2 : Obj Nat := paper.append v2
def paper3 : Obj Nat := paper2.append v3

def w9 : World Nat := setEntry w8 "author" "paper" (.live paper2)
def w10 : World Nat := setEntry w9 "author" "paper" (.live paper3)

theorem s9 : StepBy toy "author" w8 w9 :=
  .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by simp [v2, Version.revise, Version.pins]) (Or.inl rfl) (by decide)
    (by decide)

theorem s10 : StepBy toy "author" w9 w10 :=
  .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by simp [v3, v1, Version.describe, Version.pins]) (Or.inl rfl) (by decide)
    (by decide)

example : v2.documentVersion = 2 ∧ v3.documentVersion = 1 := by decide

example : ¬ Extends paper2.versions { v1 with documentVersion := 3 } := by decide

example : Extends paper2.versions { v1 with message := "again" } := by decide

def j2 : Version Nat :=
  Version.revise [j1] [] (some (collect toy w10 joint)) "Joint papers" "coauthor"
    "followed: paper"

def w11 : World Nat := setEntry w10 "coauthor" "joint" (.live (jointObj.append j2))

theorem s11 : StepBy toy "coauthor" w10 w11 :=
  .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
    (fun p hp => exists_of_isOk ((by decide :
      ∀ p ∈ j2.pins, (resolve toy w10 p).isOk = true) p hp)) (Or.inl rfl) (by decide)
    (by decide)

def w12 : World Nat := setEntry w11 "coauthor" "paper" (.live paper2)
def w13 : World Nat := setEntry w12 "coauthor" "paper" (.live paper3)

theorem s12 : StepBy toy "coauthor" w11 w12 :=
  .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by simp [v2, Version.revise, Version.pins]) (Or.inr ⟨paper3, rfl, rfl, [v3], rfl⟩) (by decide)
    (by decide)

theorem s13 : StepBy toy "coauthor" w12 w13 :=
  .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by simp [v3, v1, Version.describe, Version.pins]) (Or.inr ⟨paper3, rfl, rfl, [], rfl⟩) (by decide)
    (by decide)

def copy : Obj Nat :=
  acceptedCopy "journal" "paper-accepted" v1 "On sheaves of documents (accepted)" "editor"
    "accepted copy of paper v1"

def w14 : World Nat := setEntry w13 "journal" "paper-accepted" (.live copy)

theorem s14 : StepBy toy "editor" w13 w14 :=
  .create _ _ _ _ _ rfl rfl (acceptedCopy_wf _ _ _ _ _ _)
    (by simp [copy, acceptedCopy, copyVersion, Version.pins, v1]) (Or.inl rfl) (by decide)
    (by decide)

def pinCopy : Pin Nat := ⟨"journal", "paper-accepted", 1, toy (copy.inventory 1)⟩

/-- A step made by some agent. -/
abbrev ByAgent (w w' : World Nat) : Prop := ∃ u, StepBy toy u w w'

theorem upToIssue : Star ByAgent w0 w6 :=
  .tail (.tail (.tail (.tail (.tail (.tail (.refl _)
    ⟨_, s1⟩) ⟨_, s2⟩) ⟨_, s3⟩) ⟨_, s4⟩) ⟨_, s5⟩) ⟨_, s6⟩

theorem afterIssue : Star ByAgent w6 w14 :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.refl _)
    ⟨_, s7⟩) ⟨_, s8⟩) ⟨_, s9⟩) ⟨_, s10⟩) ⟨_, s11⟩) ⟨_, s12⟩) ⟨_, s13⟩) ⟨_, s14⟩

theorem story : ValidSteps toy w0 w14 :=
  (upToIssue.trans afterIssue).mono fun ⟨_, h⟩ => h.toValidStep toy

theorem story_wf : WFWorld toy w14 := story.wf toy (WFWorld.empty toy)

theorem story_pins : PinsOk toy w14 := story.pins_ok toy

theorem story_acts : Acts toy w0 w14 :=
  (upToIssue.trans afterIssue).mono fun ⟨u, h⟩ => ⟨u, .step h⟩

example : ∀ v ∈ issue.versions, v.depositor ∈ ["editor"] :=
  Acts.curated toy story_acts (a := "journal") (oid := "issue-7") rfl rfl rfl

example : ∀ v ∈ paper3.versions, v.depositor = "author" := by decide

theorem journal_writers : writersOf w14 "journal" = some ["editor"] := by decide

example (w' : World Nat) (h : Act toy "author" w14 w') :
    lookup w' "journal" "issue-7" = lookup w14 "journal" "issue-7" :=
  h.outsider toy (fun ar har => by
    have := journal_writers
    rw [writersOf, har] at this
    simp at this
    rw [this]
    decide) _

example : verify toy w14 issue7 = [(pinV1, .ok v1)] := by decide

example : verify toy w14 issue7 = verify toy w6 issue7 := by decide

example : collect toy w14 issue7 = issue7 := by decide

def pinV3 : Pin Nat := ⟨"author", "paper", 3, toy (paper3.inventory 3)⟩

example : j2.members = some
    { joint with members :=
        [{ archive := "author", object := "paper", follow := true, pins := [pinV3] },
         { archive := "coauthor", object := "notes", pins := [pinNotes] }] } := by decide

example : resolve toy w14 pinV3 = .ok v3 := by decide

example : resolve toy w14 ⟨"author", "paper", 3, toy (paper.inventory 1)⟩ = .mismatch := by decide

example : resolve toy w14 ⟨"author", "paper", 4, toy (paper.inventory 1)⟩ = .unavailable := by decide

example : resolveAt toy w14 "coauthor" pinV3 = .ok v3 := by decide

example : (copy.versions.map (·.files)) = [v1.files] := by decide

def wGone : World Nat := fun b => if b = "author" then none else w14 b

example : resolve toy wGone pinV3 = .unavailable := by decide

example : resolveVia toy wGone pinV3 ["coauthor"] = .ok v3 := by decide

example : verify toy wGone issue7 = [(pinV1, .unavailable)] := by decide

example : resolveVia toy wGone pinV1 ["coauthor"] = .ok v1 := by decide

def wDown : World Nat := takedown toy w14 "author" "paper" paper3

example : verify toy wDown issue7 = [(pinV1, .removed)] := by decide

example : resolve toy wDown ⟨"author", "paper", 1, 0⟩ = .removed := by decide

example : resolve toy wDown pinCopy = resolve toy w14 pinCopy := by decide

example : (resolve toy wDown pinCopy).isOk = true := by decide

example : resolveVia toy wDown pinV1 ["coauthor"] = .ok v1 := by decide

def v1' : Version Nat := { v1 with description := "On sheaves of documents, revised quietly" }

def wTamper : World Nat :=
  setEntry w14 "author" "paper" (.live { paper3 with versions := [v1', v2, v3] })

example : verify toy wTamper issue7 = [(pinV1, .mismatch)] := by decide

example : resolve toy wTamper pinV3 = .mismatch := by decide

example : resolveVia toy wTamper pinV1 ["coauthor"] = .ok v1 := by decide

example : (resolve toy w14 ⟨"author", "paper", 4, toy ((paper3.append v3).inventory 4)⟩).isOk = false := by
  decide

def wd : Version Nat := v3.withdraw "author" "retracted"

example : (Version.describe (paper3.versions ++ [wd]) v1 "On sheaves" "author" "again").status =
    .withdrawn := by decide

example : ¬ NoReinstatement (paper3.versions ++ [wd]) { v1 with message := "back" } := by
  decide

def twin : Obj Nat :=
  acceptedCopy "journal" "paper-twin" v1 v1.description v1.depositor v1.message

example : resolveEntry toy (some (.live twin)) pinV1 = .mismatch := by decide

def twoPins : Members Nat :=
  { type := .catalogue,
    members := [{ archive := "author", object := "paper", pins := [pinV1, pinV3] }] }

def followed : Members Nat :=
  { type := .selection,
    members := [{ archive := "author", object := "paper", follow := true, pins := [pinV1] }] }

def unpinned : Members Nat :=
  { type := .selection, members := [{ archive := "author", object := "paper", pins := [] }] }

example : ¬ twoPins.WF ∧ ¬ followed.WF ∧ ¬ unpinned.WF := by decide

example : paper3.versions ≠ paper.versions ++ v3 :: [] ∧
    paper3.versions ≠ paper.versions ++ [v3, v3] := by decide

example (s : Site) : ¬ Chain (PinsTo toy w14) s s := no_cycles toy story s

theorem w6_to_w14 : Steps w6 w14 :=
  ValidSteps.toSteps toy (afterIssue.mono fun ⟨_, h⟩ => h.toValidStep toy)

example : verify toy w14 issue7 = verify toy w6 issue7 ∧ collect toy w14 issue7 = issue7 :=
  selection_stable toy w6_to_w14 rfl fun p hp => exists_of_isOk ((by decide :
    ∀ p ∈ issue7.pins, (resolve toy w6 p).isOk = true) p hp)

theorem story_down : Events toy w0 wDown := .tail story.toEvents (.takedown _ _ _ _ rfl)

example : SoundWorld toy wDown := Events.sound toy story_down

example (s : Site) : ¬ Chain (PinsTo toy wDown) s s := no_cycles_events toy story_down s

example : resolveEntry toy (some (.live paper3)) pinV3 = .ok v3 :=
  Events.mirror_resolves toy story.toEvents (b := "coauthor") (x := "paper") rfl (by decide)
    rfl (by decide) (by decide)

example : resolveVia toy wGone pinV3 ["coauthor"] = .ok v3 :=
  have hgone : resolve toy wGone pinV3 = .unavailable := by decide
  resolveVia_mirror toy (pre := []) (post := []) (m := paper3)
    (fun b' hb' u h => by
      simp only [List.mem_singleton] at hb'
      subst hb'
      exact absurd (hgone ▸ h : Resolution.unavailable = .ok u) (by simp))
    rfl (by decide)

end OpenSheaf.Story
