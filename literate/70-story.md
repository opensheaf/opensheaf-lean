# A story, checked by computation

The theorems of the previous chapters hold for every world. This chapter
follows one world through a small story, built from the use cases, and
checks what a verifier would report at each stage. Each check is an
`example` proved by `decide`: Lean computes both sides and compares them,
so these are tests in the ordinary sense, and a wrong expectation fails the
build.

The story is told in valid steps ([chapter 5](45-worlds.md)), starting
from nothing. Collections are objects of their archives, and every act,
the authors' deposits, the editors' issue, the co-author's catalogue and
mirror, the journal's accepted copy, is a step whose checks Lean verifies.
The general theorems then apply to the story's worlds, and the chapter ends
by comparing proof and computation.

    -- in OpenSheaf/Story.lean:
    import OpenSheaf.Impossible
    import OpenSheaf.Patterns

    namespace OpenSheaf.Story

    open OpenSheaf OpenSheaf.Patterns

## A toy digest

Digests are natural numbers, computed by a toy function of what an
inventory describes: the archive and identifier of the object, and its
versions. It is deliberately weak: the theorems used here assume nothing
of it, and a weak function keeps the computations small.

    /-- A toy digest of an inventory. -/
    def toy : Hash Nat := fun i =>
      i.versions.foldl (fun h v => 31 * h + v.description.length + 7 * v.documentVersion
        + v.files.length + v.depositor.length)
        (i.versions.length + 1000 * i.archive.length + 100 * i.id.length)

Valid steps ask that every pin of a new version resolve. A pin resolving is
an existential statement, which `decide` cannot check; the check that its
result is a version is decidable, and enough.

    /-- The result is a version. -/
    def _root_.OpenSheaf.Resolution.isOk {D : Type} : Resolution D → Bool
      | .ok _ => true
      | _ => false

    theorem exists_of_isOk {D : Type} {r : Resolution D} (h : r.isOk = true) :
        ∃ t, r = .ok t := by
      cases r <;> simp_all [Resolution.isOk]

## The cast

Three archives: a researcher's (`author`), a journal's (`journal`), and a
co-author's (`coauthor`). They start empty.

    def emptyArchive (a : ArchiveId) : Archive Nat := { id := a, entries := fun _ => none }

    def w0 : World Nat := fun _ => none
    def w1 : World Nat := fun b => if b = "author" then some (emptyArchive "author") else w0 b
    def w2 : World Nat := fun b => if b = "journal" then some (emptyArchive "journal") else w1 b
    def w3 : World Nat := fun b => if b = "coauthor" then some (emptyArchive "coauthor") else w2 b

    theorem s1 : ValidStep toy w0 w1 := .newArchive _ _ _ rfl fun _ => rfl
    theorem s2 : ValidStep toy w1 w2 := .newArchive _ _ _ rfl fun _ => rfl
    theorem s3 : ValidStep toy w2 w3 := .newArchive _ _ _ rfl fun _ => rfl

## The paper, and the co-author's note

The researcher deposits a paper; the co-author deposits a note of their own.

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

Each creation is a valid step: the identifier is free, the object is well
formed (`rfl` checks the identifier, `decide` the other four conditions),
its versions hold no pins, and it belongs to the archive that keeps it.

    theorem s4 : ValidStep toy w3 w4 :=
      .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide⟩ (by simp [paper, v1, Version.pins])
        (Or.inl rfl)

    theorem s5 : ValidStep toy w4 w5 :=
      .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide⟩ (by simp [notes, n1, Version.pins])
        (Or.inl rfl)

## The journal's issue, the co-author's catalogue

The pins of version 1 of the paper and of the note:

    def pinV1 : Pin Nat := ⟨"author", "paper", 1, toy (paper.inventory 1)⟩
    def pinNotes : Pin Nat := ⟨"coauthor", "notes", 1, toy (notes.inventory 1)⟩

The journal publishes issue 7, a selection whose member pins version 1 of
the paper, the revision the editors vetted ("An overlay journal").

    def issue7 : Members Nat :=
      { type := .selection,
        members := [{ archive := "author", object := "paper", pins := [pinV1] }] }

    def i1 : Version Nat :=
      { documentVersion := 1, files := [], members := some issue7, description := "Issue 7",
        depositor := "editor", message := "issue 7: the papers accepted" }

    def issue : Obj Nat := { archive := "journal", id := "issue-7", kind := .collection, versions := [i1] }

    def w6 : World Nat := setEntry w5 "journal" "issue-7" (.live issue)

The co-author keeps a catalogue of joint papers, which follows the paper,
and lists the note, pinned and not followed ("Co-authors in different
archives").

    def joint : Members Nat :=
      { type := .catalogue,
        members := [{ archive := "author", object := "paper", follow := true, pins := [pinV1] },
                    { archive := "coauthor", object := "notes", pins := [pinNotes] }] }

    def j1 : Version Nat :=
      { documentVersion := 1, files := [], members := some joint, description := "Joint papers",
        depositor := "coauthor", message := "joint papers" }

    def jointObj : Obj Nat := { archive := "coauthor", id := "joint", kind := .collection, versions := [j1] }

    def w7 : World Nat := setEntry w6 "coauthor" "joint" (.live jointObj)

Creating them is valid only because every pin resolves when they are made:
`decide` resolves each one.

    theorem s6 : ValidStep toy w5 w6 :=
      .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide⟩
        (fun v hv p hp => exists_of_isOk ((by decide :
          ∀ v ∈ issue.versions, ∀ p ∈ v.pins, (resolve toy w5 p).isOk = true) v hv p hp))
        (Or.inl rfl)

    theorem s7 : ValidStep toy w6 w7 :=
      .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide⟩
        (fun v hv p hp => exists_of_isOk ((by decide :
          ∀ v ∈ jointObj.versions, ∀ p ∈ v.pins, (resolve toy w6 p).isOk = true) v hv p hp))
        (Or.inl rfl)

## A mirror

The co-author mirrors the paper: the same object, byte for byte, under the
same identifier, in their archive (section 10.4). The step is valid as a
mirror: the object belongs to another archive, where the original is live
and extends it (here, equals it).

    def w8 : World Nat := setEntry w7 "coauthor" "paper" (.live paper)

    theorem s8 : ValidStep toy w7 w8 :=
      .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide⟩ (by simp [paper, v1, Version.pins])
        (Or.inr ⟨by decide, paper, rfl, rfl, [], by simp⟩)

## The authors revise the paper

After the referees' comments, the authors deposit a revision, with new
files and a new document version; then they correct a typo in the title of
version 1, by a description-only version of that earlier document version
(section 7.3 allows any).

    def v2 : Version Nat :=
      Version.revise [v1] [("paper.tm", 201), ("paper.pdf", 202)] none
        "On sheaves of documents" "author" "revised after the referees' comments"

    def v3 : Version Nat :=
      Version.describe [v1, v2] v1 "On sheaves of documents, I" "author" "title of version 1"

    def paper2 : Obj Nat := paper.append v2
    def paper3 : Obj Nat := paper2.append v3

    def w9 : World Nat := setEntry w8 "author" "paper" (.live paper2)
    def w10 : World Nat := setEntry w9 "author" "paper" (.live paper3)

Both extend the history, as `decide` checks against the rule of section
7.3: `v2` is new content, document version 2; `v3` holds the content of
`v1`, so it is document version 1 again.

    theorem s9 : ValidStep toy w8 w9 :=
      .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
        (by simp [v2, Version.revise, Version.pins]) (Or.inl rfl)

    theorem s10 : ValidStep toy w9 w10 :=
      .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
        (by simp [v3, v1, Version.describe, Version.pins]) (Or.inl rfl)

    example : v2.documentVersion = 2 ∧ v3.documentVersion = 1 := by decide

The rule also rejects what it should. Depositing the files of version 1
again as a new document version 3 does not extend the history; with
document version 1 it does.

    example : ¬ Extends paper2.versions { v1 with documentVersion := 3 } := by decide

    example : Extends paper2.versions { v1 with message := "again" } := by decide

## The co-author's tool updates the catalogue, and the mirror

The co-author's tool updates the catalogue: the followed member moves to the
head, version 3. The new member list is deposited as a new version of the
catalogue, a new document version since its content changed.

    def j2 : Version Nat :=
      Version.revise [j1] [] (some (collect toy w10 joint)) "Joint papers" "coauthor"
        "followed: paper"

    def w11 : World Nat := setEntry w10 "coauthor" "joint" (.live (jointObj.append j2))

    theorem s11 : ValidStep toy w10 w11 :=
      .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
        (fun p hp => exists_of_isOk ((by decide :
          ∀ p ∈ j2.pins, (resolve toy w10 p).isOk = true) p hp)) (Or.inl rfl)

The mirror is brought up to date by copying the two new versions. Each
step is valid because it copies the original's next version.

    def w12 : World Nat := setEntry w11 "coauthor" "paper" (.live paper2)
    def w13 : World Nat := setEntry w12 "coauthor" "paper" (.live paper3)

    theorem s12 : ValidStep toy w11 w12 :=
      .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
        (by simp [v2, Version.revise, Version.pins]) (Or.inr ⟨paper3, rfl, rfl, [v3], rfl⟩)

    theorem s13 : ValidStep toy w12 w13 :=
      .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
        (by simp [v3, v1, Version.describe, Version.pins]) (Or.inr ⟨paper3, rfl, rfl, [], rfl⟩)

## The journal keeps an accepted copy

The journal keeps its own copy of the revision it vetted (section 10.5).

    def copy : Obj Nat :=
      acceptedCopy "journal" "paper-accepted" v1 "On sheaves of documents (accepted)" "editor"
        "accepted copy of paper v1"

    def w14 : World Nat := setEntry w13 "journal" "paper-accepted" (.live copy)

    theorem s14 : ValidStep toy w13 w14 := acceptedCopy_valid toy rfl rfl _ _ _ _

    def pinCopy : Pin Nat := ⟨"journal", "paper-accepted", 1, toy (copy.inventory 1)⟩

## The whole story is valid

    theorem story : ValidSteps toy w0 w14 :=
      .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail
        (.tail (.refl _) s1) s2) s3) s4) s5) s6) s7) s8) s9) s10) s11) s12) s13) s14

so the general theorems apply: the final world is well formed, and nothing
in it dangles, without computing anything.

    theorem story_wf : WFWorld toy w14 := story.wf toy (WFWorld.empty toy)

    theorem story_pins : PinsOk toy w14 := story.pins_ok toy

## What the verifier reports

The issue verifies as it did when it was made, and the editors' update does
nothing.

    example : verify toy w14 issue7 = [(pinV1, .ok v1)] := by decide

    example : verify toy w14 issue7 = verify toy w6 issue7 := by decide

    example : collect toy w14 issue7 = issue7 := by decide

The catalogue's second version pins the head of the paper, version 3, and
keeps the note's pin.

    def pinV3 : Pin Nat := ⟨"author", "paper", 3, toy (paper3.inventory 3)⟩

    example : j2.members = some
        { joint with members :=
            [{ archive := "author", object := "paper", follow := true, pins := [pinV3] },
             { archive := "coauthor", object := "notes", pins := [pinNotes] }] } := by decide

    example : resolve toy w14 pinV3 = .ok v3 := by decide

A pin made by copying the number of version 3 and the digest of version 1
is caught; so is a pin of a version that does not exist.

    example : resolve toy w14 ⟨"author", "paper", 3, toy (paper.inventory 1)⟩ = .mismatch := by decide

    example : resolve toy w14 ⟨"author", "paper", 4, toy (paper.inventory 1)⟩ = .unavailable := by decide

The mirror resolves the paper's pins as the original does, and the accepted
copy holds the files vetted.

    example : resolveAt toy w14 "coauthor" pinV3 = .ok v3 := by decide

    example : (copy.versions.map (·.files)) = [v1.files] := by decide

## The researcher's archive disappears

The author's archive goes offline for good. Its pins resolve to `unavailable`;
through the mirror they resolve as before (section 6.4).

    def wGone : World Nat := fun b => if b = "author" then none else w14 b

    example : resolve toy wGone pinV3 = .unavailable := by decide

    example : resolveVia toy wGone pinV3 ["coauthor"] = .ok v3 := by decide

    example : verify toy wGone issue7 = [(pinV1, .unavailable)] := by decide

    example : resolveVia toy wGone pinV1 ["coauthor"] = .ok v1 := by decide

## The paper is taken down

Instead, a court orders the paper taken down in the author's archive
(section 11.2). Every pin of it reports `removed`, even a pin with a wrong
digest (section 11.3 keeps only the last digest). The accepted copy is not
touched.

    def wDown : World Nat := takedown toy w14 "author" "paper" paper3

    example : verify toy wDown issue7 = [(pinV1, .removed)] := by decide

    example : resolve toy wDown ⟨"author", "paper", 1, 0⟩ = .removed := by decide

    example : resolve toy wDown pinCopy = resolve toy w14 pinCopy := by decide

    example : (resolve toy wDown pinCopy).isOk = true := by decide

But the mirror is not touched either. Nothing in section 11.2 reaches the
co-author's archive, and section 6.4 tells a client to try the mirrors when
the member's archive fails: the paper taken down is still served, through
the mirror, to anyone who asks.

    example : resolveVia toy wDown pinV1 ["coauthor"] = .ok v1 := by decide

This is a gap of the specification, not of the model: a takedown, by law,
must reach the mirrors, and resolution should stop at a tombstone. It is
discussed in [issue #33](https://github.com/opensheaf/opensheaf.github.io/issues/33)
of the specification; when it is settled, this check will change.

## Attempts that fail

[What cannot happen](65-impossible.md) proves that some breaks of the
protocol are impossible. Here are concrete attempts, and how they fail.

**The author rewrites version 1 in place**, outside the protocol, changing
its title. The world is not reachable by steps (`history_not_rewritten`),
and every pin of version 1 or later stops resolving: the journal's
verifier reports a mismatch.

    def v1' : Version Nat := { v1 with description := "On sheaves of documents, revised quietly" }

    def wTamper : World Nat :=
      setEntry w14 "author" "paper" (.live { paper3 with versions := [v1', v2, v3] })

    example : verify toy wTamper issue7 = [(pinV1, .mismatch)] := by decide

    example : resolve toy wTamper pinV3 = .mismatch := by decide

The mirror still holds the original, and resolution through it recovers the
vetted version: integrity comes from the pin, not from the place.

    example : resolveVia toy wTamper pinV1 ["coauthor"] = .ok v1 := by decide

**A collection pins a version that does not exist yet**, for instance a
version 4 of the paper, guessing its digest. The pin does not resolve, so
the step that would deposit it is not valid. This is why pins cannot form
cycles: a version cannot pin itself, since it does not exist when its pins
are checked.

    example : (resolve toy w14 ⟨"author", "paper", 4, toy ((paper3.append v3).inventory 4)⟩).isOk = false := by
      decide

**The authors withdraw the paper, then describe version 1 again as active.**
The description takes the status of the head, so it stays withdrawn; a
version marked active by hand is rejected (the model's choice on issue
#25).

    def wd : Version Nat := v3.withdraw "author" "retracted"

    example : (Version.describe (paper3.versions ++ [wd]) v1 "On sheaves" "author" "again").status =
        .withdrawn := by decide

    example : ¬ NoReinstatement (paper3.versions ++ [wd]) { v1 with message := "back" } := by
      decide

**The journal deposits an accepted copy with the original's description and
depositor**, so that its version is identical to version 1. Its inventory
still names another object, so it does not resolve the original's pin.

    def twin : Obj Nat :=
      acceptedCopy "journal" "paper-twin" v1 v1.description v1.depositor v1.message

    example : resolveEntry toy (some (.live twin)) pinV1 = .mismatch := by decide

**A tool writes a member list that breaks section 10.2**: a catalogue
member with two pins, a selection member with `follow`, a member with no
pin. None is well formed, so none can be deposited by a valid step.

    def twoPins : Members Nat :=
      { type := .catalogue,
        members := [{ archive := "author", object := "paper", pins := [pinV1, pinV3] }] }

    def followed : Members Nat :=
      { type := .selection,
        members := [{ archive := "author", object := "paper", follow := true, pins := [pinV1] }] }

    def unpinned : Members Nat :=
      { type := .selection, members := [{ archive := "author", object := "paper", pins := [] }] }

    example : ¬ twoPins.WF ∧ ¬ followed.WF ∧ ¬ unpinned.WF := by decide

**The co-author changes their mirror**, appending a version the original
does not have. It is not the original's next version: at `w11` the
original's history is `v1, v2, v3`, and the mirror holds `v1`, so the next
version is `v2`, not `v3`.

    example : paper3.versions ≠ paper.versions ++ v3 :: [] ∧
        paper3.versions ≠ paper.versions ++ [v3, v3] := by decide

**The story's world has no cycle of pins**, by the general theorem:

    example (s : Site) : ¬ Chain (PinsTo toy w14) s s := no_cycles toy story s

## Proof and computation agree

The general theorems give, without computing, what the checks above
computed. `selection_stable` gives the issue's report in the final world
from its report when it was made:

    theorem w6_to_w14 : Steps w6 w14 :=
      .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.refl _)
        (s7.toStep toy)) (s8.toStep toy)) (s9.toStep toy)) (s10.toStep toy))
        (s11.toStep toy)) (s12.toStep toy)) (s13.toStep toy)) (s14.toStep toy)

    example : verify toy w14 issue7 = verify toy w6 issue7 ∧ collect toy w14 issue7 = issue7 :=
      selection_stable toy w6_to_w14 rfl fun p hp => exists_of_isOk ((by decide :
        ∀ p ∈ allPins issue7, (resolve toy w6 p).isOk = true) p hp)

The takedown is an event ([chapter 5](45-worlds.md)), so the world after
it is sound: every pin held resolves or reports `removed`, and there is no
cycle.

    theorem story_down : Events toy w0 wDown := .tail story.toEvents (.takedown _ _ _ _ rfl)

    example : SoundWorld toy wDown := Events.sound toy story_down

    example (s : Site) : ¬ Chain (PinsTo toy wDown) s s := no_cycles_events toy story_down s

The mirror kept by the co-author agrees with its original, by the theorem
on mirrors of [chapter 6](48-copies.md):

    example : resolveEntry toy (some (.live paper3)) pinV3 = .ok v3 :=
      Events.mirror_resolves toy story.toEvents (b := "coauthor") (x := "paper") rfl (by decide)
        rfl (by decide) (by decide)

and `resolveVia_mirror` gives the answer of the mirror when the author's
archive is gone:

    example : resolveVia toy wGone pinV3 ["coauthor"] = .ok v3 :=
      have hgone : resolve toy wGone pinV3 = .unavailable := by decide
      resolveVia_mirror toy (pre := []) (post := []) (m := paper3)
        (fun b' hb' u h => by
          simp only [List.mem_singleton] at hb'
          subst hb'
          exact absurd (hgone ▸ h : Resolution.unavailable = .ok u) (by simp))
        rfl (by decide)

    end OpenSheaf.Story
