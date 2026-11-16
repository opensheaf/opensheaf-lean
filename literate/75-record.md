# A learning record, checked by computation

A second story, from the use case "A learning record": a student writes a
thesis in an archive of their own, and the department keeps the record of
the work. Like [the first story](70-story.md), it is told in steps made by
agents, from nothing, and each check is proved by `decide`. It exercises
what the first story does not: a mirror kept as a receipt of each
submission, a selection whose revision set grows by the department's acts,
comments that keep pointing to the version they were written about, and the
deletion of the record at the end of its retention period.

    -- in OpenSheaf/Record.lean:
    import OpenSheaf.Story

    namespace OpenSheaf.Record

    open OpenSheaf OpenSheaf.Patterns OpenSheaf.Story

## The cast

Two archives: the student's (`student`), and the department's (`dept`),
whose writers are its registry, a supervisor and an examiner. The digest is
the toy digest of the first story.

    def r0 : World Nat := fun _ => none
    def r1 : World Nat := fun b => if b = "student" then some (emptyArchive ["student"]) else r0 b
    def r2 : World Nat := fun b =>
      if b = "dept" then some (emptyArchive ["registry", "supervisor", "examiner"]) else r1 b

    theorem a1 : StepBy toy "student" r0 r1 := .newArchive _ _ _ rfl (fun _ => rfl) (by decide)
    theorem a2 : StepBy toy "registry" r1 r2 := .newArchive _ _ _ rfl (fun _ => rfl) (by decide)

## The first submission

The student deposits the thesis, version 1, and hands it in. The registry
receives it by mirroring it: the mirror is the receipt.

    def t1 : Version Nat :=
      { documentVersion := 1, files := [("thesis.tm", 11), ("thesis.pdf", 12)],
        description := "A thesis", depositor := "student", message := "submitted for comments" }

    def thesis1 : Obj Nat :=
      { archive := "student", id := "thesis", kind := .document, versions := [t1] }

    def r3 : World Nat := setEntry r2 "student" "thesis" (.live thesis1)
    def r4 : World Nat := setEntry r3 "dept" "thesis" (.live thesis1)

    theorem a3 : StepBy toy "student" r2 r3 :=
      .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
        (by simp [thesis1, t1, Version.pins, Version.memberPins]) (Or.inl rfl) (by decide) (by decide) (by decide) (sourceOk_all_none toy (by decide))

    theorem a4 : StepBy toy "registry" r3 r4 :=
      .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
        (by simp [thesis1, t1, Version.pins, Version.memberPins]) (Or.inr ⟨thesis1, rfl, rfl, [], by simp⟩)
        (by decide) (by decide) (by decide) (sourceOk_all_none toy (by decide))

The supervisor's comments are a document of the department, deposited by
the supervisor. They point to the version commented on by a `Reviews`
reference ([chapter 13](80-references.md)), which pins version 1 of the
thesis; the step checks that the pin resolves. In the specification,
`Reviews` is a DataCite relation that tools do not follow; here it is the
pinned reference proposed in issues #21 and #28.

    def pinT1 : Pin Nat := ⟨"student", "thesis", 1, toy (thesis1.inventory 1)⟩

    def c1 : Version Nat :=
      { documentVersion := 1, files := [("comments.pdf", 41)], refs := [⟨"Reviews", pinT1⟩],
        description := "Comments on version 1", depositor := "supervisor", message := "comments" }

    def comments : Obj Nat :=
      { archive := "dept", id := "comments-1", kind := .document, versions := [c1] }

    def r5 : World Nat := setEntry r4 "dept" "comments-1" (.live comments)

    theorem a5 : StepBy toy "supervisor" r4 r5 :=
      .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
        (fun v hv p hp => pinOk_of_isOk ((by decide :
          ∀ v ∈ comments.versions, ∀ p ∈ v.pins, (resolve toy r4 p).isOk = true) v hv p hp))
        (Or.inl rfl) (by decide) (by decide) (by decide) (sourceOk_all_none toy (by decide))

## The record

The record is a selection of the department, which pins each document of
the process in the version that played its part: here, version 1 of the
thesis and the comments on it. The registry deposits it.

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

## The second submission and the examination

The student revises the thesis in answer to the comments, a new document
version, and hands it in; the registry copies it into the receipt. The
examiner reports on version 2.

    def t2 : Version Nat :=
      Version.revise [t1] [("thesis.tm", 21), ("thesis.pdf", 22)] none "A thesis" "student"
        "answers the comments"

    def thesis2 : Obj Nat := thesis1.append t2

    def r7 : World Nat := setEntry r6 "student" "thesis" (.live thesis2)
    def r8 : World Nat := setEntry r7 "dept" "thesis" (.live thesis2)

    theorem a7 : StepBy toy "student" r6 r7 :=
      .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
        (by simp [t2, Version.revise, Version.pins, Version.memberPins]) (Or.inl rfl) (by decide) (by decide) (by decide) (sourceOk_none toy rfl)

    theorem a8 : StepBy toy "registry" r7 r8 :=
      .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
        (by simp [t2, Version.revise, Version.pins, Version.memberPins]) (Or.inr ⟨thesis2, rfl, rfl, [], (List.append_nil _).symm⟩)
        (by decide) (by decide) (by decide) (sourceOk_none toy rfl)

    def e1 : Version Nat :=
      { documentVersion := 1, files := [("report.pdf", 51)],
        description := "Report on version 2", depositor := "examiner", message := "report" }

    def report : Obj Nat :=
      { archive := "dept", id := "report-1", kind := .document, versions := [e1] }

    def r9 : World Nat := setEntry r8 "dept" "report-1" (.live report)

    theorem a9 : StepBy toy "examiner" r8 r9 :=
      .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
        (by simp [report, e1, Version.pins, Version.memberPins]) (Or.inl rfl) (by decide) (by decide) (by decide) (sourceOk_all_none toy (by decide))

The registry records the examination: a new version of the record, whose
revision set for the thesis grows to versions 1 and 2, and which adds the
report. It is a new document version of the record, since its member list
changed.

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

## The record is valid

The steps, listed once:

    theorem record_acts : Star ByAgent r0 r10 :=
      .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.refl _)
        ⟨_, a1⟩) ⟨_, a2⟩) ⟨_, a3⟩) ⟨_, a4⟩) ⟨_, a5⟩) ⟨_, a6⟩) ⟨_, a7⟩) ⟨_, a8⟩) ⟨_, a9⟩)
        ⟨_, a10⟩

    theorem valid : ValidSteps toy r0 r10 :=
      record_acts.mono fun ⟨_, h⟩ => h.toValidStep toy

    theorem acts : Acts toy r0 r10 :=
      record_acts.mono fun ⟨u, h⟩ => ⟨u, .step h⟩

    example : WFWorld toy r10 := valid.wf toy (WFWorld.empty toy)

## What the record shows

The verifier checks the record: every pin resolves, to the version that
played its part.

    example : verify toy r10 rec2 =
        [(pinT1, .ok t1), (pinT2, .ok t2), (pinC1, .ok c1), (pinE1, .ok e1)] := by decide

The comments still point to version 1, the version they were written about,
although the thesis has moved on: the reference of the comments resolves
to version 1, while the head of the thesis is version 2.

    example : c1.refs.map (fun r => resolve toy r10 r.pin) = [.ok t1] ∧
        headPin toy r10 "student" "thesis" = some pinT2 := by
      decide

The record's first version is kept, as the history of the process: its pin
resolves to the version deposited at the first submission.

    def pinG1 : Pin Nat := ⟨"dept", "record", 1, toy (record2.inventory 1)⟩

    example : resolve toy r10 pinG1 = .ok g1 := by decide

The record is a selection: updating it changes nothing. The new revision of
the thesis entered it by the registry's act, not by the tool.

    example : collect toy r10 rec1 = rec1 := by decide

## Who decides

By `owner_controls` ([chapter 9](60-patterns.md)), every version of the
record was deposited by the department's writers, and the student cannot
change it. The same theorem, applied to the student's archive, says that
the department cannot change the thesis.

    example : ∀ v ∈ record2.versions, v.depositor ∈ ["registry", "supervisor", "examiner"] :=
      (owner_controls toy acts (a := "dept") (oid := "record") rfl rfl rfl).1

    example (w' : World Nat) (h : Act toy "student" r10 w') :
        lookup w' "dept" "record" = lookup r10 "dept" "record" :=
      (owner_controls toy acts (a := "dept") (oid := "record") rfl rfl rfl).2 _ _ (by decide) h

    example (w' : World Nat) (h : Act toy "registry" r10 w') :
        lookup w' "student" "thesis" = lookup r10 "student" "thesis" :=
      (owner_controls toy acts (a := "student") (oid := "thesis") rfl rfl rfl).2 _ _ (by decide) h

## The receipt

By `mirror_receipt`, the versions the department received are the
student's, at the same numbers, in this world and in every later one:

    example : thesis2.versionAt 1 = some t1 :=
      mirror_receipt toy (ValidSteps.toEvents toy valid) (b := "dept") (x := "thesis") rfl
        (by decide) rfl (by decide)

The student rewrites version 1 in place, outside the protocol, to make the
first submission look better. The pin of the first submission no longer
resolves on the student's archive; on the receipt it still does, to what
was handed in. (The rewrite changes the description: the toy digest does
not look at the content of files, so a rewrite of the files alone would
collide with the original, the case that `NoCollision` excludes.)

    def t1' : Version Nat := { t1 with description := "A thesis, much improved" }

    def rTamper : World Nat :=
      setEntry r10 "student" "thesis" (.live { thesis2 with versions := [t1', t2] })

    example : resolve toy rTamper pinT1 = .mismatch := by decide

    example : resolveAt toy rTamper "dept" pinT1 = .ok t1 := by decide

## Retention

At the end of the retention period, the registry takes the record down: an
act of a writer of the department.

    def rDown : World Nat := takedown toy r10 "dept" "record" record2

    theorem down : Act toy "registry" r10 rDown := .takedown _ _ _ _ _ rfl rfl (by decide)

The record's pins report `removed`; the student's thesis, and the pins of
it, are not affected.

    def pinG2 : Pin Nat := ⟨"dept", "record", 2, toy (record2.inventory 2)⟩

    example : resolve toy rDown pinG1 = .removed ∧ resolve toy rDown pinG2 = .removed := by decide

    example : resolve toy rDown pinT2 = .ok t2 := by decide

By `record_retention`, this holds from then on: the record's pins report
`removed` in every later world, and the thesis's pins resolve as before
through any later valid steps.

    example (w' : World Nat) (h : Events toy rDown w') : resolve toy w' pinG2 = .removed :=
      (record_retention toy (w := r10) (a := "dept") (oid := "record") (r := record2) rfl).1
        pinG2 ⟨rfl, rfl⟩ w' h

    example (w' : World Nat) (h : ValidSteps toy rDown w') : resolve toy w' pinT2 = .ok t2 :=
      (record_retention toy (w := r10) (a := "dept") (oid := "record") (r := record2) rfl).2
        pinT2 (by decide) t2 (by decide) w' h

The comments and the report are documents of their own, and stay; deleting
them too is a takedown of each.

    end OpenSheaf.Record
