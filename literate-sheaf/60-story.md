# A story, as a sheaf

The model ends with a story: a world built by valid steps from nothing, in
which three owners keep key logs, an author seals and revises a paper, a
journal publishes an issue and keeps an accepted copy, and a co-author
keeps a catalogue and a mirror of the paper (chapter "A story, checked by
computation" of the model). This chapter reads the final world of the
story, `w19`, as a sheaf. The values are checked by computation, as tests.
Two broken worlds follow, whose sections do not glue.

In `w19` the author's paper has three object versions: `v1` seals document
version 1, `v2` deposits document version 2, and `v3` is a description-only
version that retitles document version 1. The co-author's archive keeps a
mirror of all three.

    -- in Sheaf/Story.lean:
    import Sheaf.Fibres
    import OpenSheaf.Story

    namespace OpenSheaf.Sheaf.Story

    open OpenSheaf OpenSheaf.Story OpenSheaf.Sheaf

The story is a sequence of valid steps, so of events. The main theorem
([The sections of a world glue](40-world.md)) says that its sections glue
when its owners are honest: when each signs one history, which no copy the
world holds collides with.

    theorem story_sheaf {H : Histories Nat} (hh : Honest E H w19) :
        ∃ g, Glues (sections w19) g ∧ ∀ g', Glues (sections w19) g' → g' = g :=
      world_glues E story_events hh

The owners of the story are honest in that sense, so its sections glue
with no hypothesis. The histories are, for each line, the versions the
world holds and those signed beyond them: the paper's history includes the
version a thief signed with the author's retired key `a1`, and the key
log's the version signed with its current key `a33`. Honesty counts every
signature that verifies and is made with a key of a key-log version the
world holds, whoever made it: what it excludes is two signed histories of
one line, not a thief. The proof goes through the signatures made, which
the environment lists, and through every copy the world holds.

    /-- The archives of the story. -/
    theorem w19_other {b : ArchiveId} (h1 : b ≠ "author") (h2 : b ≠ "journal")
        (h3 : b ≠ "coauthor") : w19 b = none := by
      simp [w19, w18, w17, w16, w15, w14, w13, w12, w11, w10, w9, w8, w7, w6, w5, w4, w3, w2, w1,
        w0, setEntry, h1, h2, h3]

    theorem logA2_keys : ∀ v ∈ logA2.versions, ∀ k ∈ (v.keys.map (·.keys)).getD [],
        k ∈ ["a1", "a33"] := by
      decide

    /-- The author's keys, as the world holds its key log, are `a1` and `a33`. -/
    theorem authorKeys (s : Sig Nat) (h : OwnerKey E w19 "author" s) : s.key ∈ ["a1", "a33"] := by
      obtain ⟨_, b, kl, hkl, v, hv, _, kv, hkv, _, hkey⟩ := h
      have hvm : v ∈ kl.versions := versionAt_mem hv
      have hk : s.key ∈ (v.keys.map (·.keys)).getD [] := by rw [hkv]; exact hkey
      by_cases h1 : b = "author"
      · subst h1
        have e : lookup w19 "author" (.line (keyLogLine "author")) = some (.live logA2) := rfl
        rw [e] at hkl; cases hkl; exact logA2_keys v hvm _ hk
      by_cases h2 : b = "journal"
      · subst h2
        have e : lookup w19 "journal" (.line (keyLogLine "author")) = none := rfl
        rw [e] at hkl; cases hkl
      by_cases h3 : b = "coauthor"
      · subst h3
        have e : lookup w19 "coauthor" (.line (keyLogLine "author")) = some (.live logA2) := rfl
        rw [e] at hkl; cases hkl; exact logA2_keys v hvm _ hk
      simp [lookup, w19_other h1 h2 h3] at hkl

    /-- The histories the owners of the story sign. -/
    def storyHistories : Histories Nat := fun l =>
      if l = paperLine then (some genP, paper3.versions ++ [v4])
      else if l = issueLine then (some genI, issue.versions ++ [i2])
      else if l = jointLine then (some genJt, joint2.versions)
      else if l = copyLine then (some genP, copy.versions)
      else if l = keyLogLine "author" then (some genA, logA2.versions ++ [k3c])
      else (none, [])

The second half unfolds the world at each of its three archives, finds
every copy it holds, and tries the same tactics on each: the copy is a key
log, or a prefix of the history its owner signs.

    /-- **The owners of the story are honest.** -/
    theorem story_honest : Honest E storyHistories w19 := by
      refine ⟨fun l s hv hl ho => ?_, ?_⟩
      · have hm : s ∈ made := by simpa [E] using hv
        subst hl
        simp only [made, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl
        all_goals first
          | decide
          | exact absurd (authorKeys _ ho) (by decide)
          | exact absurd ho.1 (by decide)
      · intro l b o hl hk n hn hh
        have fin : o.id = .line l → o.genesis = (storyHistories l).1 →
            (∃ t, (storyHistories l).2 = o.versions ++ t) →
            o.inventory n = histInv l (storyHistories l).1 (storyHistories l).2 n := by
          intro hid hg ⟨t, ht⟩
          simp only [Obj.inventory, histInv, hid, hg, ht]
          rw [List.take_append_of_le_length hn]
        apply fin (story_wf.1 _ _ _ hl).id
        all_goals
          have hb : b = "author" ∨ b = "journal" ∨ b = "coauthor" := by
            by_cases h1 : b = "author"; · exact Or.inl h1
            by_cases h2 : b = "journal"; · exact Or.inr (Or.inl h2)
            by_cases h3 : b = "coauthor"; · exact Or.inr (Or.inr h3)
            simp [lookup, w19_other h1 h2 h3] at hl
          rcases hb with rfl | rfl | rfl <;>
          · simp [lookup, w19, w18, w17, w16, w15, w14, w13, w12, w11, w10, w9, w8, w7, w6, w5, w4,
              w3, w2, w1, setEntry, arch, logLine] at hl
            repeat' (split at hl)
            all_goals (try simp only [Option.some.injEq, Entry.live.injEq] at hl)
            all_goals (try (simp at hl; done))
            all_goals (subst hl; rename_i hlx; subst hlx)
            all_goals (first
              | exact absurd rfl hk
              | decide
              | (simp [storyHistories, paperLine, issueLine, jointLine, copyLine]; done)
              | (apply Exists.intro [v4]; simp [storyHistories, paperLine, issueLine, jointLine,
                  copyLine, keyLogLine, paper3, paper2, paper1, paper0, Obj.append]; done)
              | (apply Exists.intro [i2]; simp [storyHistories, paperLine, issueLine, jointLine,
                  copyLine, keyLogLine, issue, issue0]; done)
              | (apply Exists.intro []; simp [storyHistories, paperLine, issueLine, jointLine,
                  copyLine, keyLogLine]; done)
              | (apply Exists.intro [v3, v4]; simp [storyHistories, paperLine, issueLine, jointLine,
                  copyLine, keyLogLine, paper3, paper2, paper1, paper0, Obj.append]; done)
              | (apply Exists.intro [v2, v3, v4]; simp [storyHistories, paperLine, issueLine,
                  jointLine, copyLine, keyLogLine, paper3, paper2, paper1, paper0, Obj.append]; done)
              | (apply Exists.intro [j2]; simp [storyHistories, paperLine, issueLine, jointLine,
                  copyLine, keyLogLine, joint2, jointObj, joint0, Obj.append]; done))

    /-- **The sections of the story glue**, with no hypothesis. -/
    theorem story_glues :
        ∃ g, Glues (sections w19) g ∧ ∀ g', Glues (sections w19) g' → g' = g :=
      story_sheaf story_honest

## Three sources

Three sources of the world: the author's paper at object version 3, the
co-author's mirror at object version 1, and the journal's accepted copy.
Each is a live entry of `w19`, which Lean checks by computation.

    def authorPaper : Source w19 := ⟨"author", paperLine, paper3, rfl, by decide, 3⟩
    def coauthorPaper : Source w19 := ⟨"coauthor", paperLine, paper3, rfl, by decide, 1⟩
    def acceptedPaper : Source w19 := ⟨"journal", copyLine, copy, rfl, by decide, 1⟩

    def first : Name := ⟨.line paperLine, 1⟩
    def second : Name := ⟨.line paperLine, 2⟩

The author's object version 3 holds both document versions. The mirror's
object version 1 holds only the first, although the mirror is kept in
another archive: names are those of the line, not of a place.

    theorem first_author : cover w19 authorPaper first := by decide
    theorem first_coauthor : cover w19 coauthorPaper first := by decide
    theorem second_author : cover w19 authorPaper second := by decide
    example : ¬ cover w19 coauthorPaper second := by decide

The two sources agree on the first document version, by computation. The
value there is the content of `v3`, the description-only version, which is
also the content of `v1`. Document version 2 has another content.

    example : sections w19 authorPaper first first_author =
        sections w19 coauthorPaper first first_coauthor :=
      (objSec_piece (o := paper3) (n := 3) (v := v3) (by decide) (by decide) first_author).trans
        ((content_eq_iff.mpr (by decide)).trans
          (objSec_piece (o := paper3) (n := 1) (v := v1) (by decide) (by decide) first_coauthor).symm)

    example : sections w19 authorPaper first first_author ≠
        sections w19 authorPaper second second_author := by
      intro h
      have := content_eq_iff.mp
        ((objSec_piece (o := paper3) (n := 3) (v := v1) (by decide) (by decide) first_author).symm.trans
          (h.trans (objSec_piece (o := paper3) (n := 3) (v := v2) (by decide) (by decide) second_author)))
      revert this; decide

The accepted copy holds, at its own name, the value the paper has at
document version 1, which the journal vetted.

    def accepted : Name := ⟨.line copyLine, 1⟩

    theorem accepted_held : cover w19 acceptedPaper accepted := by decide

    example : sections w19 acceptedPaper accepted accepted_held =
        sections w19 authorPaper first first_author := by
      show objSec copy 1 accepted accepted_held = objSec paper3 3 first first_author
      rw [show objSec copy 1 accepted accepted_held = v1.content from
          acceptedCopy_value _ _ _ _ _ _ _ _ _ rfl accepted_held]
      exact ((content_eq_iff.mpr (by decide)).trans
        (objSec_piece (o := paper3) (n := 3) (v := v3) (by decide) (by decide) first_author).symm)

## Descriptions do not glue

The paper's object versions hold document versions 1, 2 and 1: the map
`proj` of [Descriptions are the fibres](78-fibres.md) is not monotone. Its
top goes 1, 2, 2: version 3 is a description-only version, the second
point of a run. Object versions 1 and 3 of the same copy describe document
version 1 differently, so the descriptions have no glued section, while
the contents do.

    def authorFirst : Source w19 := ⟨"author", paperLine, paper3, rfl, by decide, 1⟩

    example : paper3.versions.map (·.documentVersion) = [1, 2, 1] := by decide

    example : (List.range 4).map (fun n => docCount (paper3.versions.take n)) = [0, 1, 2, 2] := by
      decide

    /-- **Descriptions do not glue.** In the story, the author's object versions
    1 and 3 describe document version 1 differently. -/
    theorem descriptions_incompatible : ¬ Compatible (descSections w19) := by
      intro h
      have h3 : cover w19 authorPaper first := by decide
      have h1 : cover w19 authorFirst first := by decide
      have := h authorPaper authorFirst first h3 h1
      change docDescription (paper3.versions.take 3) 1 = docDescription (paper3.versions.take 1) 1
        at this
      revert this
      decide

## A forged copy

Replace the co-author's mirror by an object of the author's line, with the
same description but other bytes for the source of document version 1.
The forged object is well formed on its own. But its section and the
author's disagree on the first document version, so the sections of the
world are not compatible, and nothing glues them.

    def v1f : Version Nat := { v1 with files := [("paper.tm", 666), ("paper.pdf", 102)] }
    def forged : Obj Nat := { paper1 with versions := [v1f] }
    def wForged : World Nat := setEntry w19 "coauthor" (.line paperLine) (.live forged)

    example : WellFormed forged.versions := by decide

    def authorPaper' : Source wForged := ⟨"author", paperLine, paper3, rfl, by decide, 3⟩
    def forgedPaper : Source wForged := ⟨"coauthor", paperLine, forged, rfl, by decide, 1⟩

    theorem forged_incompatible : ¬ Compatible (sections wForged) := by
      intro h
      have h1 : cover wForged authorPaper' first := by decide
      have h2 : cover wForged forgedPaper first := by decide
      have heq := h authorPaper' forgedPaper first h1 h2
      have e1 : sections wForged authorPaper' first h1 = v3.content :=
        objSec_piece (o := paper3) (n := 3) (v := v3) (by decide) (by decide) h1
      have e2 : sections wForged forgedPaper first h2 = v1f.content :=
        objSec_piece (o := forged) (n := 1) (v := v1f) (by decide) (by decide) h2
      have := content_eq_iff.mp (e1.symm.trans (heq.trans e2))
      revert this; decide

Version 0.2 reads such a world as a fork of the line (section 7.4): if a
sequence of events built a world whose sections do not glue, two copies of
a line, neither extending the other, each end in a version signed with a
current key of the owner's key log as the world holds it (`no_glue_fork`). This world is not one of them. No event shrinks the
co-author's copy from three versions to one, and the forged object is a
prefix of no other copy, so no step copies it: no sequence of events
builds `wForged`, and the theorem says nothing about it. A forged copy is
written outside the protocol, as a host could write it on its own disk.

A verifier reading the forged copy through a pin of the author's version 1
would report a mismatch (section 8.5), with a real digest. The toy digest
of the story does not see the bytes of files, so it would not; it even
gives the forged inventory the digest that the author signed for version
1. Through a name alone, no verifier could tell. Names glue because owners
sign one history and copies do not collide with it; pins glue because of
the digest.

## A number reused

A history that gives number 1 to two different contents breaks the rule of
section 4.2, and its pieces do not glue: the two object versions disagree
on the value of document version 1.

    def bad : Obj Nat := { paper1 with versions := [v1, v1f] }

    example : ¬ WellFormed bad.versions := by decide

    example : ¬ Compatible (pieces bad 2) := by
      intro h
      have := content_eq_iff.mp (h ⟨v1, by decide⟩ ⟨v1f, by decide⟩ (bad.name v1) rfl rfl)
      revert this; decide

    end OpenSheaf.Sheaf.Story
