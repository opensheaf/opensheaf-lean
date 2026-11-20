-- Generated from literate/75-record.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Story

namespace OpenSheaf.Record

open OpenSheaf OpenSheaf.Patterns OpenSheaf.Story

def keysS : Keys Nat := { keys := ["s1"], threshold := 1, next := [4], nextThreshold := 1 }
def keysD : Keys Nat := { keys := ["d1"], threshold := 1, next := [4], nextThreshold := 1 }

def genS : Genesis Nat := { kind := .owner, nonce := "student", keys := some keysS }
def genD : Genesis Nat := { kind := .owner, nonce := "dept", keys := some keysD }

def logS : Obj Nat := keyLog "student" genS
def logD : Obj Nat := keyLog "dept" genD

def genT : Genesis Nat := { kind := .document, nonce := "thesis", originator := "student" }
def thesisLine : LineId := ⟨"thesis", "student"⟩

def t1 : Version Nat :=
  { documentVersion := 1, files := [("thesis.tm", 11), ("thesis.pdf", 12)],
    description := "A thesis", depositor := "student", message := "submitted for comments" }

def thesis0 : Obj Nat :=
  { id := .line thesisLine, kind := .document, genesis := some genT, versions := [t1] }

def sigT1 : Sig Nat := ⟨thesisLine, 1, toy (thesis0.inventory 1), "s1", logPin "student" logS 1⟩

def thesis1 : Obj Nat := { thesis0 with sigs := [sigT1] }

def pinT1 : Pin Nat := ⟨thesisLine, 1, toy (thesis1.inventory 1), ["student"]⟩

def genC1 : Genesis Nat := { kind := .document, nonce := "comments", originator := "dept" }
def commentsLine : LineId := ⟨"comments", "dept"⟩

def c1 : Version Nat :=
  { documentVersion := 1, files := [("comments.pdf", 41)], refs := [⟨"Reviews", pinT1⟩],
    description := "Comments on version 1", depositor := "supervisor", message := "comments" }

def comments0 : Obj Nat :=
  { id := .line commentsLine, kind := .document, genesis := some genC1, versions := [c1] }

def sigC1 : Sig Nat := ⟨commentsLine, 1, toy (comments0.inventory 1), "d1", logPin "dept" logD 1⟩

def comments : Obj Nat := { comments0 with sigs := [sigC1] }

def pinC1 : Pin Nat := ⟨commentsLine, 1, toy (comments.inventory 1), ["dept"]⟩

def rec1 : Members Nat :=
  { type := .selection,
    members := [{ line := thesisLine, hints := ["student"], pins := [pinT1] },
                { line := commentsLine, hints := ["dept"], pins := [pinC1] }] }

def genR : Genesis Nat := { kind := .collection, nonce := "record", originator := "dept" }
def recordLine : LineId := ⟨"record", "dept"⟩

def g1 : Version Nat :=
  { documentVersion := 1, files := [], members := some rec1, description := "Record",
    depositor := "registry", message := "first submission, with comments" }

def record0 : Obj Nat :=
  { id := .line recordLine, kind := .collection, genesis := some genR, versions := [g1] }

def sigG1 : Sig Nat := ⟨recordLine, 1, toy (record0.inventory 1), "d1", logPin "dept" logD 1⟩

def record1 : Obj Nat := { record0 with sigs := [sigG1] }

def t2 : Version Nat :=
  Version.revise [t1] [("thesis.tm", 21), ("thesis.pdf", 22)] none "A thesis" "student"
    "answers the comments"

def sigT2 : Sig Nat :=
  ⟨thesisLine, 2, toy ((thesis1.append t2).inventory 2), "s1", logPin "student" logS 1⟩

def thesis2 : Obj Nat := thesis1.append t2 [sigT2]

def genE : Genesis Nat := { kind := .document, nonce := "report", originator := "dept" }
def reportLine : LineId := ⟨"report", "dept"⟩

def e1 : Version Nat :=
  { documentVersion := 1, files := [("report.pdf", 51)],
    description := "Report on version 2", depositor := "examiner", message := "report" }

def report0 : Obj Nat :=
  { id := .line reportLine, kind := .document, genesis := some genE, versions := [e1] }

def sigE1 : Sig Nat := ⟨reportLine, 1, toy (report0.inventory 1), "d1", logPin "dept" logD 1⟩

def report : Obj Nat := { report0 with sigs := [sigE1] }

def pinT2 : Pin Nat := ⟨thesisLine, 2, toy (thesis2.inventory 2), ["student"]⟩
def pinE1 : Pin Nat := ⟨reportLine, 1, toy (report.inventory 1), ["dept"]⟩

def rec2 : Members Nat :=
  { type := .selection,
    members := [{ line := thesisLine, hints := ["student"], pins := [pinT1, pinT2] },
                { line := commentsLine, hints := ["dept"], pins := [pinC1] },
                { line := reportLine, hints := ["dept"], pins := [pinE1] }] }

def g2 : Version Nat :=
  Version.revise [g1] [] (some rec2) "Record" "registry" "examined: report on version 2"

def sigG2 : Sig Nat :=
  ⟨recordLine, 2, toy ((record1.append g2).inventory 2), "d1", logPin "dept" logD 1⟩

def record2 : Obj Nat := record1.append g2 [sigG2]

def madeR : List (Sig Nat) := [sigT1, sigC1, sigG1, sigT2, sigE1, sigG2]

def ER : Env Nat :=
  { hash := toy, keyDigest := keyDigest, nameOf := nameOf, verifies := fun s => decide (s ∈ madeR) }

def r0 : World Nat := fun _ => none
def r1 : World Nat := fun b => if b = "student" then some (arch ["student"]) else r0 b
def r2 : World Nat := fun b => if b = "dept" then some (arch ["dept"]) else r1 b
def r3 : World Nat := setEntry r2 "student" (logLine "student") (.live logS)
def r4 : World Nat := setEntry r3 "dept" (logLine "dept") (.live logD)
def r5 : World Nat := setEntry r4 "dept" (logLine "student") (.live logS)
def r6 : World Nat := setEntry r5 "student" (.line thesisLine) (.live thesis1)
def r7 : World Nat := setEntry r6 "dept" (.line thesisLine) (.live thesis1)
def r8 : World Nat := setEntry r7 "dept" (.line commentsLine) (.live comments)
def r9 : World Nat := setEntry r8 "dept" (.line recordLine) (.live record1)
def r10 : World Nat := setEntry r9 "student" (.line thesisLine) (.live thesis2)
def r11 : World Nat := setEntry r10 "dept" (.line thesisLine) (.live thesis2)
def r12 : World Nat := setEntry r11 "dept" (.line reportLine) (.live report)
def r13 : World Nat := setEntry r12 "dept" (.line recordLine) (.live record2)

theorem a1 : ValidStep ER r0 r1 := .newArchive _ _ _ rfl (fun _ => rfl)
theorem a2 : ValidStep ER r1 r2 := .newArchive _ _ _ rfl (fun _ => rfl)

theorem a3 : ValidStep ER r2 r3 := create_keyLog rfl rfl (by decide)
theorem a4 : ValidStep ER r3 r4 := create_keyLog rfl rfl (by decide)
theorem a5 : ValidStep ER r4 r5 := create_keyLog rfl rfl (by decide)

theorem a6 : ValidStep ER r5 r6 := create_hosted rfl rfl rfl (no_pins (by decide)) (by decide)

theorem copy_r6 : CopyOf r6 "dept" thesis1 := ⟨"student", thesis1, by decide, rfl, rfl, [], by simp⟩

theorem a7 : ValidStep ER r6 r7 := create_copy rfl rfl rfl copy_r6 (no_pins (by decide)) (by decide)

theorem a8 : ValidStep ER r7 r8 := create_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)
theorem a9 : ValidStep ER r8 r9 := create_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)

theorem a10 : ValidStep ER r9 r10 :=
  append_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)

theorem copy_r10 : CopyOf r10 "dept" thesis2 := ⟨"student", thesis2, by decide, rfl, rfl, [], by simp⟩

theorem a11 : ValidStep ER r10 r11 :=
  append_copy rfl rfl rfl copy_r10 (pins_resolve (by decide)) (by decide)

theorem a12 : ValidStep ER r11 r12 := create_hosted rfl rfl rfl (no_pins (by decide)) (by decide)

theorem a13 : ValidStep ER r12 r13 :=
  append_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)

theorem valid : ValidSteps ER r0 r13 :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail
    (.refl _) a1) a2) a3) a4) a5) a6) a7) a8) a9) a10) a11) a12) a13

theorem events : Events ER r0 r13 := valid.mono .step

example : WFWorld ER r13 := valid.wf ER (WFWorld.empty ER)

example : verify ER r13 rec2 =
    [(pinT1, .ok t1), (pinT2, .ok t2), (pinC1, .ok c1), (pinE1, .ok e1)] := by decide

example : c1.refs.map (fun r => resolve toy r13 r.pin) = [.ok t1] ∧
    headPin toy r13 ["student"] thesisLine = some pinT2 := by
  decide

def pinG1 : Pin Nat := ⟨recordLine, 1, toy (record2.inventory 1), ["dept"]⟩

example : resolve toy r13 pinG1 = .ok g1 := by decide

example : collect toy r13 rec1 = rec1 := by decide

example : HeadSigned ER r13 recordLine record2 :=
  Events.headsSigned ER events (b := "dept") rfl (by decide)

example : HeadSigned ER r13 thesisLine thesis2 :=
  Events.headsSigned ER events (b := "dept") rfl (by decide)

example : resolveAt toy r13 "dept" pinT1 = .ok t1 ∧ resolveAt toy r13 "dept" pinT2 = .ok t2 := by
  decide

def t1' : Version Nat := { t1 with files := [("thesis.tm", 99), ("thesis.pdf", 12)] }

def rTamper : World Nat :=
  setEntry r13 "student" (.line thesisLine) (.live { thesis2 with versions := [t1', t2] })

example : resolve toy rTamper pinT1 = .mismatch := by decide

example : resolveAt toy rTamper "dept" pinT1 = .ok t1 := by decide

def rDown : World Nat := takedown toy r13 "dept" (.line recordLine) record2

theorem down : Events ER r0 rDown := .tail events (.takedown _ _ _ _ (by decide) rfl)

def pinG2 : Pin Nat := ⟨recordLine, 2, toy (record2.inventory 2), ["dept"]⟩

example : resolve toy rDown pinG1 = .removed ∧ resolve toy rDown pinG2 = .removed := by decide

example : resolve toy rDown pinT2 = .ok t2 := by decide

example (w' : World Nat) (h : Events ER rDown w') : resolveAt toy w' "dept" pinG2 = .removed :=
  (record_retention ER (w := r13) (a := "dept") (oid := .line recordLine) (r := record2) rfl).1
    pinG2 rfl w' h

example (w' : World Nat) (h : ValidSteps ER rDown w') : resolveAt toy w' "student" pinT2 = .ok t2 :=
  (record_retention ER (w := r13) (a := "dept") (oid := .line recordLine) (r := record2) rfl).2
    "student" pinT2 (by decide) t2 (by decide) w' h

end OpenSheaf.Record
