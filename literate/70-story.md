# A story, checked by computation

The theorems of the [previous chapter](60-patterns.md) hold for every
world. This chapter follows one world through a small story, built from the
use cases, and checks what a verifier would report at each step. Each check
is an `example` proved by `decide`: Lean computes both sides and compares
them, so these are tests in the ordinary sense, and a wrong expectation
fails the build. The story ends by applying the general theorems to the
same worlds, to see that proof and computation agree.

    -- in OpenSheaf/Story.lean:
    import OpenSheaf.Patterns

    namespace OpenSheaf.Story

    open OpenSheaf OpenSheaf.Patterns

## A toy digest

Digests are natural numbers, computed by a toy function of the versions an
inventory describes. It is deliberately weak: none of the theorems needs
more, and a weak function makes it easy to see what the digests do.

    /-- A toy digest of an inventory. -/
    def toy : Hash Nat := fun l =>
      l.foldl (fun h v => 31 * h + v.description.length + 7 * v.documentVersion
        + v.files.length) l.length

## The cast

A researcher keeps an archive, `author`, with one paper. Version 1 is the
author's original.

    def v1 : Version Nat :=
      { documentVersion := 1, files := [("paper.tm", 101), ("paper.pdf", 102)],
        description := "On sheaves of documents", depositor := "author",
        message := "first version" }

    def paper : Obj Nat := { id := "paper", kind := .document, versions := [v1] }

    def pinV1 : Pin Nat := ⟨"author", "paper", 1, toy [v1]⟩

A journal, with an archive of its own, publishes issue 7, a selection whose
member pins version 1 of the paper, the revision the editors vetted
("An overlay journal").

    def issue7 : Members Nat :=
      { type := .selection,
        members := [{ archive := "author", object := "paper", pins := [pinV1] }] }

A co-author keeps a catalogue of joint papers, which follows the paper, and
lists also a note of their own, pinned and not followed ("Co-authors in
different archives").

    def pinNotes : Pin Nat := ⟨"coauthor", "notes", 1, 999⟩

    def joint : Members Nat :=
      { type := .catalogue,
        members := [{ archive := "author", object := "paper", follow := true, pins := [pinV1] },
                    { archive := "coauthor", object := "notes", pins := [pinNotes] }] }

The world at the start: the author's archive with the paper. The journal's
and the co-author's archives hold the collections; only their member lists
matter here, so the model keeps the collections as values rather than as
objects.

    def authorArchive : Archive Nat :=
      { id := "author", entries := fun x => if x = "paper" then some (.live paper) else none }

    def w0 : World Nat := fun a => if a = "author" then some authorArchive else none

## Before anything happens

The vetted pin resolves to version 1; a pin with a wrong digest is a
mismatch; a pin of a version that does not exist is missing.

    example : resolve toy w0 pinV1 = .ok v1 := by decide

    example : resolve toy w0 ⟨"author", "paper", 1, 0⟩ = .mismatch := by decide

    example : resolve toy w0 ⟨"author", "paper", 2, toy [v1]⟩ = .missing := by decide

The co-author's note is in an archive the model does not have: the
verifier reports it missing, which is what a verifier reports for an
archive that does not answer.

    example : verify toy w0 joint = [(pinV1, .ok v1), (pinNotes, .missing)] := by decide

## The authors revise the paper

After the referees' comments, the authors deposit a revision: new files, a
new document version.

    def v2 : Version Nat :=
      v1.revise [("paper.tm", 201), ("paper.pdf", 202)] none
        "On sheaves of documents" "author" "revised after the referees' comments"

    def w1 : World Nat := setEntry w0 "author" "paper" (.live (paper.append v2))

    example : v2.documentVersion = 2 := by decide

Then they correct a typo in the title: a description-only version, which
keeps the document version.

    def v3 : Version Nat := v2.describe "On sheaves of documents (corrected)" "author" "title"

    def paper2 : Obj Nat := paper.append v2

    def w2 : World Nat := setEntry w1 "author" "paper" (.live (paper2.append v3))

    example : v3.documentVersion = 2 := by decide

The history `v1, v2, v3` is well formed: the document versions are 1, 2, 2.

    example : WellFormed [v1, v2, v3] := by
      simp [WellFormed, ChainFrom, Follows, sameContent, v1, v2, v3,
        Version.revise, Version.describe]

## What the journal and the co-author see

The issue is unchanged: verifying it reports exactly what it reported at
the start, and updating it does nothing.

    example : verify toy w2 issue7 = verify toy w0 issue7 := by decide

    example : verify toy w2 issue7 = [(pinV1, .ok v1)] := by decide

    example : collect toy w2 issue7 = issue7 := by decide

The co-author's catalogue moves: updating it pins version 3, the head, which
is document version 2. The note, not followed, keeps its pin.

    def pinV3 : Pin Nat := ⟨"author", "paper", 3, toy [v1, v2, v3]⟩

    example : collect toy w2 joint =
        { joint with members :=
            [{ archive := "author", object := "paper", follow := true, pins := [pinV3] },
             { archive := "coauthor", object := "notes", pins := [pinNotes] }] } := by decide

    example : resolve toy w2 pinV3 = .ok v3 := by decide

A pin made by copying the number of version 3 and the digest of version 1
is caught:

    example : resolve toy w2 ⟨"author", "paper", 3, toy [v1]⟩ = .mismatch := by decide

## The paper is taken down

A court orders the paper taken down. The issue's pin, and the catalogue's
new pin, now resolve to `removed`: the verifier reports what happened,
rather than a broken link.

    def w3 : World Nat := takedown toy w2 "author" "paper" (paper2.append v3)

    example : verify toy w3 issue7 = [(pinV1, .removed)] := by decide

    example : resolve toy w3 pinV3 = .removed := by decide

A pin that never named a version of the paper is still a mismatch, not a
removal: the tombstone recognises exactly the digests of the paper's
inventories.

    example : resolve toy w3 ⟨"author", "paper", 1, 0⟩ = .mismatch := by decide

## Proof and computation agree

The two deposits are steps of [chapter 3](30-archive.md), so the story's
worlds are reachable from `w0`:

    theorem w0_to_w2 : Steps w0 w2 :=
      .tail (.tail (.refl w0) (Step.append w0 "author" authorArchive "paper" paper v2 rfl rfl))
        (Step.append w1 "author" _ "paper" paper2 v3 rfl rfl)

and the general theorem `selection_stable` gives, without computing, what
the checks above computed: the issue verifies in `w2` as in `w0`, and its
update does nothing.

    example : verify toy w2 issue7 = verify toy w0 issue7 ∧ collect toy w2 issue7 = issue7 :=
      selection_stable toy w0_to_w2 rfl (by
        intro p hp
        simp [allPins, issue7] at hp
        subst hp
        exact ⟨v1, by decide⟩)

    end OpenSheaf.Story
