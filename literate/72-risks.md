# Residual risks, checked by computation

Section 15.1 of the specification ends with what the format does not
protect: "**Residual risks.** The format leaves these to readers and to
other evidence". This chapter shows four of them in the worlds of the
story ([chapter 14](70-story.md)), each as a counterexample to a promise
the format does not make, checked by `decide` or by the general theorems
of [chapter 13](66-security.md). Each scenario starts from the story's
final world `w19`, or from `wExp`, in which the author has exposed its
retired key `a1`, and is built by valid steps, so that what it shows is
what the protocol allows, not a break of it. The signatures used, beyond
the story's own, are the four listed in the story for this chapter.

Two risks are left out: the old current keys of an owner that ended
honestly, which the story's author does not do, and timestamps, which the
model does not have.

    -- in OpenSheaf/Risks.lean:
    import OpenSheaf.Security
    import OpenSheaf.Story

    namespace OpenSheaf.Risks

    open OpenSheaf OpenSheaf.Story

## Withholding an exposure

"A host can withhold an exposure or a fork record, serving a key log that
stops before it, so that its readers find signed and uncontested what is
contested elsewhere, and an archive it serves does not yet freeze the
owner (sections 6.5 and 7.5)". In `wExp`, the author's archive holds
`logA3`, which exposes `a1`, and refuses the thief's fourth version of the
paper, signed with `a1` alone (the story's last section). The world is
built by events:

    theorem story_exp : Events E w0 wExp := .tail story_events (.step sExp)

Another archive, `old`, hosting the author, has been served the author's
key log only up to version 2, `logA2`, before the exposure: it creates its
copy from the first version and adds the second, then takes a copy of the
paper, as the author's archive held it, and then the thief's version.
Each is a valid step.

    def wOld1 : World Nat := fun b => if b = "old" then some (arch ["author"]) else wExp b
    def wOld2 : World Nat := setEntry wOld1 "old" (logLine "author") (.live logA1)
    def wOld3 : World Nat := setEntry wOld2 "old" (logLine "author") (.live logA2)
    def wOld4 : World Nat := setEntry wOld3 "old" (.line paperLine) (.live paper3)
    def wOld : World Nat := setEntry wOld4 "old" (.line paperLine) (.live paper4)

    theorem r1 : ValidStep E wExp wOld1 := .newArchive _ _ _ rfl (fun _ => rfl)
    theorem r2 : ValidStep E wOld1 wOld2 := create_keyLog rfl rfl (by decide)
    theorem r3 : ValidStep E wOld2 wOld3 := append_keyLog rfl rfl (by decide)
    theorem r4 : ValidStep E wOld3 wOld4 :=
      create_hosted rfl rfl rfl (no_pins (by decide)) (by decide)
    theorem r5 : ValidStep E wOld4 wOld :=
      append_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)

    theorem withheld : Events E w0 wOld :=
      .tail (.tail (.tail (.tail (.tail story_exp (.step r1)) (.step r2)) (.step r3)) (.step r4))
        (.step r5)

In one world, the archive `old` holds the thief's version, while the
author's archive would refuse it; against `old`'s copy of the key log the
version is signed and not contested, against the author's it is
contested. Both archives followed the protocol: what differs is the copy
of the key log each was served.

    example : lookup wOld "old" (.line paperLine) = some (.live paper4) := rfl

    example : ¬ LineOk E wOld "author" (arch ["author"]) paperLine paper4 :=
      not_lineOk (kl := logA3) rfl (by decide)

    example : SignedNotContested E logA2 paperLine paper4 4 ∧
        Contested E logA3 paperLine paper4 4 := by
      decide

The format's answer is the one of section 6.5: "Tools SHOULD fetch the
latest version of the key log they can find before adding" (section 7.5),
and "readers use the longer". A reader of `old` that finds `logA3`
elsewhere reads the thief's version as contested, and, by
`Contested.longer` ([chapter 13](66-security.md)), nothing it finds later
makes it uncontested again.

## Harm without forgery

"A thief gains no forgery by forking a key log, since the fork freezes the
owner and what it signs is contested; but on its side it may expose the
owner's earlier keys, which makes the owner's own versions signed with them
contested unless trusted evidence dates them (sections 6.3 and 7.3): this
harms trust in the owner's past, and never lets a forgery pass".

The thief who kept the author's used rotation key `a222` signs another
second version of the author's key log, `k2e`, which exposes `a1`, the key
with which the author sealed the paper. The co-author's archive, which
holds `logA2`, meets it and appends a fork record carrying it, as section
6.3 asks: a valid step, since the version carried is signed by a rotation
key of version 1 and differs from the version 2 held.

    def carriedE : Carried Nat :=
      { version := 2, digest := toy ((logA1.append k2e).inventory 2), keys := keysE,
        sigs := [sigK2e], depositor := k2e.depositor, message := k2e.message }

    def frE : Version Nat :=
      { documentVersion := 0, files := [], description := "", keys := none, carried := [carriedE],
        depositor := "coauthor", message := "fork record" }

    def logForkE : Obj Nat := logA2.append frE

    def wForkE : World Nat := setEntry w19 "coauthor" (logLine "author") (.live logForkE)

    theorem sForkE : ValidStep E w19 wForkE := append_keyLog rfl rfl (by decide)

    example : "a1" ∈ exposedIn logForkE ∧ Frozen logForkE := by decide

At the co-author's archive, every version of the paper is now contested:
version 1 needs `a1`, which the carried version exposes, and versions 2
and 3 name version 2 of the key log, the fork point. After the fork the
story already showed (`logFork`, which exposes nothing), version 1 was
still signed and not contested; and at the author's archive, which knows
of no fork, it still is: the second residual risk, "archives that see one
side of a fork and not yet the other show different views of the owner
until a copy holding both reaches them (section 6.3)".

    example : Contested E logForkE paperLine paper3 1 ∧
        SignedNotContested E logFork paperLine paper3 1 := by
      decide

    example : Contested E logForkE paperLine paper3 3 ∧
        SignedNotContested E logA2 paperLine paper3 1 := by
      decide

The thief gains nothing by it: the co-author's archive is frozen, and,
by `Events.fork_freezes_forever`, after any events its copy of the paper
has the versions it had, `paper3`'s, or has been taken down. No version,
the thief's or the owner's, is ever added there.

    theorem forkedE : Events E w0 wForkE := .tail story_events (.step sForkE)

    example {w' : World Nat} (hs : Events E wForkE w') {o' : Obj Nat}
        (h : lookup w' "coauthor" (.line paperLine) = some (.live o')) :
        o'.versions = paper3.versions := by
      obtain ⟨_, hl⟩ := Events.fork_freezes_forever E hs (a := "coauthor") (X := "author")
        (kl := logForkE) rfl (by decide)
      obtain ⟨o, ho, hv⟩ := hl paperLine rfl (by decide) o' h
      have : lookup wForkE "coauthor" (.line paperLine) = some (.live paper3) := rfl
      rw [this] at ho; cases ho; exact hv

## A retired key never exposed

"A retired key never exposed still makes good, uncontested signatures
naming the versions that list it (section 6.2); an owner unsure that a
retired key is destroyed exposes it". The story's author retired `a1` in
version 2 of its key log, and the thief's fourth version of the paper,
signed with `a1` and naming version 1, is signed directly without tainted
signatures against `logA2`. The story checks it by computation; here the
general theorem `retired_key_signs` ([chapter 13](66-security.md)) gives
it from the parts of the signature, each checked alone: that the
signature verifies and signs the version, that version 1 of the key log
lists `a1` with a `threshold` of 1, and that `logA2` exposes nothing.

    example : SignedClean E logA2 paperLine paper4 4 :=
      retired_key_signs E (X := "author") (kl := logA2) (s := sigThief) (by decide) (by decide)
        (by decide) (by decide) (by decide) rfl rfl (by decide) rfl rfl rfl (by decide) (by decide)

The remedy is the exposure in `logA3`, after which the author's archive
refuses the thief's version (the first section of this chapter), and which
whoever holds `a1` could not have prevented (`current_keys_cannot_block`).

## A takeover, and the owner's answer

"Whoever holds `nextThreshold` rotation keys of the latest version of a
key log, not revealed, takes the owner over (with a `nextThreshold` of 1,
a single key, section 6.2), without a fork, by signing the next version
with keys of its own; the owner can then only end it, and only if it still
holds copies of those keys itself, by signing another version of that
number, a fork (section 6.3)" (section 15.1, not among the residual risks
but next to them).

In `w19`, the latest version of the author's key log is version 2, whose
rotation key is `a5555`, not yet revealed. A thief who stole it signs a
third version, `k3x`, with a current key of its own, `xx`, and deposits it
in the author's archive: a valid step, and a valid key log, which
`KeyLogOk.append_keyed` also gives from the parts of the step.

    def wTake : World Nat := setEntry w19 "author" (logLine "author") (.live logTake)

    theorem sTake : ValidStep E w19 wTake := append_keyLog rfl rfl (by decide)

    example : KeyLogOk E "author" logTake :=
      (by decide : KeyLogOk E "author" logA2).append_keyed E rfl rfl (by decide)

From then on `xx` is a key of the author (`takeover_ownerKey`), and the
author's archive adds the thief's fourth version of the paper, signed with
`xx`, as the author's: nothing in the format tells them apart.

    example : OwnerKey E wTake "author" sigXP :=
      takeover_ownerKey E (b := "author") (o := logA2) (x := k3x) (ss := [sigK3x]) (k := keysX)
        rfl rfl rfl ⟨rfl, rfl, rfl⟩ (by decide)

    example : LineOk E wTake "author" (arch ["author"]) paperLine (paper3.append v4 [sigXP]) :=
      lineOk_host rfl (by decide) (by decide) (by decide) (by decide) (by decide)

The author, who still holds `a5555`, cannot extend the key log past the
thief's version (`takeover_locks_out`): a fourth version needs the
thief's rotation key. It answers with another third version, `k3end`,
signed with `a5555`, which ends it. The author's archive, which holds the
thief's side, meets it and appends a fork record carrying it: a valid
step, and the archive is frozen.

    def carriedO : Carried Nat :=
      { version := 3, digest := toy ((logA2.append k3end).inventory 3), keys := keysEnd,
        sigs := [sigK3o], depositor := k3end.depositor, message := k3end.message }

    def frO : Version Nat :=
      { documentVersion := 0, files := [], description := "", keys := none, carried := [carriedO],
        depositor := "author", message := "fork record" }

    def logAnswer : Obj Nat := logTake.append frO

    def wAnswer : World Nat := setEntry wTake "author" (logLine "author") (.live logAnswer)

    theorem sAnswer : ValidStep E wTake wAnswer := append_keyLog rfl rfl (by decide)

    theorem answered : Events E w0 wAnswer := .tail (.tail story_events (.step sTake)) (.step sAnswer)

    example (o' : Obj Nat) : ¬ LineOk E wAnswer "author" (arch ["author"]) paperLine o' :=
      frozen_adds_nothing E (kl := logAnswer) rfl (by decide)

The freeze lasts: after any events, the author's archive holds the paper
with the versions of `paper3`, or not at all.

    example {w' : World Nat} (hs : Events E wAnswer w') {o' : Obj Nat}
        (h : lookup w' "author" (.line paperLine) = some (.live o')) :
        o'.versions = paper3.versions := by
      obtain ⟨_, hl⟩ := Events.fork_freezes_forever E hs (a := "author") (X := "author")
        (kl := logAnswer) rfl (by decide)
      obtain ⟨o, ho, hv⟩ := hl paperLine rfl (by decide) o' h
      have : lookup wAnswer "author" (.line paperLine) = some (.live paper3) := rfl
      rw [this] at ho; cases ho; exact hv

The answer protects the owner's past: against the copy with the fork
record, whose fork point is 3, the thief's fourth version, which names the
thief's version 3, is contested, and the author's own version 3, which
names version 2, is signed and not contested. What the owner cannot get
back is the identity: "an owner whose rotation keys are stolen can add
nothing more under that identity, and continues under a successor
(sections 6.6 and 7.5)" (section 15.1).

    example : Contested E logAnswer paperLine (paper3.append v4 [sigXP]) 4 ∧
        SignedNotContested E logAnswer paperLine paper3 3 := by
      decide

    end OpenSheaf.Risks
