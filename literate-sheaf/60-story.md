# A story, as a sheaf

The model ends with a story: a world built by valid steps from nothing, in
which an author deposits a paper, a journal publishes an issue and keeps an
accepted copy, and a co-author keeps notes, a catalogue and a mirror of the
paper (chapter "A story, checked by computation" of the model). This
chapter reads the final world of the story, `w14`, as a sheaf. The values
are checked by computation, as tests. Two broken worlds follow, whose
sections do not glue.

In `w14` the author's paper has three object versions: `v1` deposits
document version 1, `v2` deposits document version 2, and `v3` is a
description-only version that retitles document version 1. The co-author's
archive keeps a mirror of all three.

    -- in Sheaf/Story.lean:
    import Sheaf.Collections
    import OpenSheaf.Story

    namespace OpenSheaf.Sheaf.Story

    open OpenSheaf OpenSheaf.Story OpenSheaf.Sheaf

The story is a sequence of valid steps, so of events, and the world it
builds gives sections that glue.

    theorem events : Events toy (fun _ => (none : Option (Archive Nat))) w14 :=
      ValidSteps.toEvents toy story

    theorem story_sheaf :
        ∃ g, Glues (sections w14) g ∧ ∀ g', Glues (sections w14) g' → g' = g :=
      world_glues toy events

## Three sources

Three sources of the world: the author's paper at object version 3, the
co-author's mirror at object version 1, and the journal's accepted copy.
Each is a live entry of `w14`, which Lean checks by computation.

    def authorPaper : Source w14 := ⟨"author", "paper", paper3, rfl, 3⟩
    def coauthorPaper : Source w14 := ⟨"coauthor", "paper", paper3, rfl, 1⟩
    def acceptedPaper : Source w14 := ⟨"journal", "paper-accepted", copy, rfl, 1⟩

    def first : Name := ⟨"author", "paper", 1⟩
    def second : Name := ⟨"author", "paper", 2⟩

The author's object version 3 holds both document versions. The mirror's
object version 1 holds only the first, although the mirror is kept in
another archive: the names are those of the author's archive.

    theorem first_author : cover w14 authorPaper first := by decide
    theorem first_coauthor : cover w14 coauthorPaper first := by decide
    theorem second_author : cover w14 authorPaper second := by decide
    example : ¬ cover w14 coauthorPaper second := by decide

The two sources agree on the first document version: the main theorem,
applied. The value there is the content of `v3`, the description-only
version, which is also the content of `v1`. Document version 2 has another
content.

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

The accepted copy holds, at its own name, the value the paper has at
document version 1, which the journal vetted.

    def accepted : Name := ⟨"journal", "paper-accepted", 1⟩

    theorem accepted_held : cover w14 acceptedPaper accepted := by decide

    example : sections w14 acceptedPaper accepted accepted_held =
        sections w14 authorPaper first first_author := by
      show objSec copy 1 accepted accepted_held = objSec paper3 3 first first_author
      rw [show objSec copy 1 accepted accepted_held = v1.content from
          acceptedCopy_value _ _ _ _ _ _ _ rfl accepted_held]
      exact (objSec_piece (o := paper3) (n := 3) (v := v1) (by decide) (by decide) first_author).symm

## The issue and what it vetted

The journal's issue 7 is a selection whose first version pins version 1 of
the paper. In the order with pins (chapter
[Collections and what they pin](55-collections.md)), the paper's first
document version lies below the issue's first; by computation, the pin
resolves to `v1`, and the edge is built by hand.

    def issue1 : Name := ⟨"journal", "issue-7", 1⟩

    theorem paper_below_issue : (byPins toy w14).le first issue1 :=
      Star.tail (Star.refl _)
        (Or.inr ⟨"journal", "issue-7", issue, i1, pinV1, paper3, v1, rfl, by decide, rfl,
          by decide, rfl, by decide, rfl⟩)

Any section that glues the story world gives the paper's first document
version, below the issue, the content of `v1`: what the journal vetted.

    example {g : Sec (HeldIn w14) (Content Nat)} (hg : Glues (sections w14) g)
        (hy : HeldIn w14 first) : g first hy = v1.content :=
      glue_at_member toy events hg (p := pinV1) (o := paper3) (u := v1) rfl (by decide) hy

## A forged copy

Replace the co-author's mirror by an object that claims the author's name,
with the same description but other bytes for the source of document
version 1. The forged object is well formed on its own. But its section and
the author's disagree on the first document version, so the sections of
the world are not compatible, and nothing glues them.

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

By the main theorem, no sequence of events builds this world, whatever the
digest function. The model's valid steps do not let an archive write a copy
of another archive's object that is not a prefix of the original.

    example (hash : Hash Nat) : ¬ Events hash (fun _ => (none : Option (Archive Nat))) wForged :=
      fun hs => forged_incompatible (world_compatible hash hs)

A verifier reading the forged copy through a pin of the author's version 1
would report a mismatch (section 14), with a real digest; the toy digest of
the story counts the files of a version but not their bytes, so it would
not. Through a name alone, no verifier could tell. Names glue because the protocol makes copies agree; pins glue because
of the digest.

## A number reused

A history that gives number 1 to two different contents breaks the rule of
section 7.3, and its pieces do not glue: the two object versions disagree
on the value of document version 1.

    def bad : Obj Nat := { paper with versions := [v1, v1'] }

    example : ¬ WellFormed bad.versions := by decide

    example : ¬ Compatible (pieces bad 2) := by
      intro h
      have := content_eq_iff.mp (h ⟨v1, by decide⟩ ⟨v1', by decide⟩ (bad.name v1) rfl rfl)
      revert this; decide

    end OpenSheaf.Sheaf.Story
