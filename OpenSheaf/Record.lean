-- Generated from literate/75-record.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Story

namespace OpenSheaf.Record

open OpenSheaf OpenSheaf.Patterns OpenSheaf.Story

def r0 : World Nat := fun _ => none
def r1 : World Nat := fun b => if b = "student" then some (emptyArchive ["student"]) else r0 b
def r2 : World Nat := fun b =>
  if b = "dept" then some (emptyArchive ["registry", "supervisor", "examiner"]) else r1 b

theorem a1 : StepBy toy "student" r0 r1 := .newArchive _ _ _ rfl (fun _ => rfl) (by decide)
theorem a2 : StepBy toy "registry" r1 r2 := .newArchive _ _ _ rfl (fun _ => rfl) (by decide)

def t1 : Version Nat :=
  { documentVersion := 1, files := [("thesis.tm", 11), ("thesis.pdf", 12)],
    description := "A thesis", depositor := "student", message := "submitted for comments" }

def thesis1 : Obj Nat :=
  { archive := "student", id := "thesis", kind := .document, versions := [t1] }

def r3 : World Nat := setEntry r2 "student" "thesis" (.live thesis1)
def r4 : World Nat := setEntry r3 "dept" "thesis" (.live thesis1)

theorem a3 : StepBy toy "student" r2 r3 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
    (by simp [thesis1, t1, Version.pins]) (Or.inl rfl) (by decide) (by decide) (by decide) (sourceOk_all_none toy (by decide))

theorem a4 : StepBy toy "registry" r3 r4 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
    (by simp [thesis1, t1, Version.pins]) (Or.inr ⟨thesis1, rfl, rfl, [], by simp⟩)
    (by decide) (by decide) (by decide) (sourceOk_all_none toy (by decide))

def c1 : Version Nat :=
  { documentVersion := 1, files := [("comments.pdf", 41)],
    description := "Comments on version 1", depositor := "supervisor", message := "comments" }

def comments : Obj Nat :=
  { archive := "dept", id := "comments-1", kind := .document, versions := [c1] }

def r5 : World Nat := setEntry r4 "dept" "comments-1" (.live comments)

theorem a5 : StepBy toy "supervisor" r4 r5 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
    (by simp [comments, c1, Version.pins]) (Or.inl rfl) (by decide) (by decide) (by decide) (sourceOk_all_none toy (by decide))

def pinT1 : Pin Nat := ⟨"student", "thesis", 1, toy (thesis1.inventory 1)⟩
def pinC1 : Pin Nat := ⟨"dept", "comments-1", 1, toy (comments.inventory 1)⟩

def rec1 : Members Nat :=
  { type := .selection,
    members := [{ archive := "student", object := "thesis", pins := [pinT1] },
                { archive := "dept", object := "comments-1", pins := [pinC1] }] }

def g1 : Version Nat :=
  { documentVersion := 1, files := [], members := some rec1, description := "Record",
    depositor := "registry", message := "first submission, with comments" }

def record1 : Obj Nat :=
  { archive := "dept", id := "record", kind := .collection, versions := [g1] }

def r6 : World Nat := setEntry r5 "dept" "record" (.live record1)

theorem a6 : StepBy toy "registry" r5 r6 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
    (fun v hv p hp => pinOk_of_isOk ((by decide :
      ∀ v ∈ record1.versions, ∀ p ∈ v.pins, (resolve toy r5 p).isOk = true) v hv p hp))
    (Or.inl rfl) (by decide) (by decide) (by decide) (sourceOk_all_none toy (by decide))

def t2 : Version Nat :=
  Version.revise [t1] [("thesis.tm", 21), ("thesis.pdf", 22)] none "A thesis" "student"
    "answers the comments"

def thesis2 : Obj Nat := thesis1.append t2

def r7 : World Nat := setEntry r6 "student" "thesis" (.live thesis2)
def r8 : World Nat := setEntry r7 "dept" "thesis" (.live thesis2)

theorem a7 : StepBy toy "student" r6 r7 :=
  .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by simp [t2, Version.revise, Version.pins]) (Or.inl rfl) (by decide) (by decide) (by decide) (sourceOk_none toy rfl)

theorem a8 : StepBy toy "registry" r7 r8 :=
  .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
    (by simp [t2, Version.revise, Version.pins]) (Or.inr ⟨thesis2, rfl, rfl, [], (List.append_nil _).symm⟩)
    (by decide) (by decide) (by decide) (sourceOk_none toy rfl)

def e1 : Version Nat :=
  { documentVersion := 1, files := [("report.pdf", 51)],
    description := "Report on version 2", depositor := "examiner", message := "report" }

def report : Obj Nat :=
  { archive := "dept", id := "report-1", kind := .document, versions := [e1] }

def r9 : World Nat := setEntry r8 "dept" "report-1" (.live report)

theorem a9 : StepBy toy "examiner" r8 r9 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
    (by simp [report, e1, Version.pins]) (Or.inl rfl) (by decide) (by decide) (by decide) (sourceOk_all_none toy (by decide))

def pinT2 : Pin Nat := ⟨"student", "thesis", 2, toy (thesis2.inventory 2)⟩
def pinE1 : Pin Nat := ⟨"dept", "report-1", 1, toy (report.inventory 1)⟩

def rec2 : Members Nat :=
  { type := .selection,
    members := [{ archive := "student", object := "thesis", pins := [pinT1, pinT2] },
                { archive := "dept", object := "comments-1", pins := [pinC1] },
                { archive := "dept", object := "report-1", pins := [pinE1] }] }

def g2 : Version Nat :=
  Version.revise [g1] [] (some rec2) "Record" "registry" "examined: report on version 2"

def record2 : Obj Nat := record1.append g2

def r10 : World Nat := setEntry r9 "dept" "record" (.live record2)

theorem a10 : StepBy toy "registry" r9 r10 :=
  .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
    (fun p hp => pinOk_of_isOk ((by decide :
      ∀ p ∈ g2.pins, (resolve toy r9 p).isOk = true) p hp)) (Or.inl rfl) (by decide)
    (by decide) (by decide) (sourceOk_none toy rfl)

theorem record_acts : Star ByAgent r0 r10 :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.refl _)
    ⟨_, a1⟩) ⟨_, a2⟩) ⟨_, a3⟩) ⟨_, a4⟩) ⟨_, a5⟩) ⟨_, a6⟩) ⟨_, a7⟩) ⟨_, a8⟩) ⟨_, a9⟩)
    ⟨_, a10⟩

theorem valid : ValidSteps toy r0 r10 :=
  record_acts.mono fun ⟨_, h⟩ => h.toValidStep toy

theorem acts : Acts toy r0 r10 :=
  record_acts.mono fun ⟨u, h⟩ => ⟨u, .step h⟩

example : WFWorld toy r10 := valid.wf toy (WFWorld.empty toy)

example : verify toy r10 rec2 =
    [(pinT1, .ok t1), (pinT2, .ok t2), (pinC1, .ok c1), (pinE1, .ok e1)] := by decide

example : resolve toy r10 pinT1 = .ok t1 ∧ headPin toy r10 "student" "thesis" = some pinT2 := by
  decide

def pinG1 : Pin Nat := ⟨"dept", "record", 1, toy (record2.inventory 1)⟩

example : resolve toy r10 pinG1 = .ok g1 := by decide

example : collect toy r10 rec1 = rec1 := by decide

example : ∀ v ∈ record2.versions, v.depositor ∈ ["registry", "supervisor", "examiner"] :=
  (owner_controls toy acts (a := "dept") (oid := "record") rfl rfl rfl).1

example (w' : World Nat) (h : Act toy "student" r10 w') :
    lookup w' "dept" "record" = lookup r10 "dept" "record" :=
  (owner_controls toy acts (a := "dept") (oid := "record") rfl rfl rfl).2 _ _ (by decide) h

example (w' : World Nat) (h : Act toy "registry" r10 w') :
    lookup w' "student" "thesis" = lookup r10 "student" "thesis" :=
  (owner_controls toy acts (a := "student") (oid := "thesis") rfl rfl rfl).2 _ _ (by decide) h

example : thesis2.versionAt 1 = some t1 :=
  mirror_receipt toy (ValidSteps.toEvents toy valid) (b := "dept") (x := "thesis") rfl
    (by decide) rfl (by decide)

def t1' : Version Nat := { t1 with description := "A thesis, much improved" }

def rTamper : World Nat :=
  setEntry r10 "student" "thesis" (.live { thesis2 with versions := [t1', t2] })

example : resolve toy rTamper pinT1 = .mismatch := by decide

example : resolveAt toy rTamper "dept" pinT1 = .ok t1 := by decide

def rDown : World Nat := takedown toy r10 "dept" "record" record2

theorem down : Act toy "registry" r10 rDown := .takedown _ _ _ _ _ rfl rfl (by decide)

def pinG2 : Pin Nat := ⟨"dept", "record", 2, toy (record2.inventory 2)⟩

example : resolve toy rDown pinG1 = .removed ∧ resolve toy rDown pinG2 = .removed := by decide

example : resolve toy rDown pinT2 = .ok t2 := by decide

example (w' : World Nat) (h : Events toy rDown w') : resolve toy w' pinG2 = .removed :=
  (record_retention toy (w := r10) (a := "dept") (oid := "record") (r := record2) rfl).1
    pinG2 ⟨rfl, rfl⟩ w' h

example (w' : World Nat) (h : ValidSteps toy rDown w') : resolve toy w' pinT2 = .ok t2 :=
  (record_retention toy (w := r10) (a := "dept") (oid := "record") (r := record2) rfl).2
    pinT2 (by decide) t2 (by decide) w' h

end OpenSheaf.Record
