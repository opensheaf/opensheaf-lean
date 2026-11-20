-- Generated from literate/72-risks.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Security
import OpenSheaf.Story

namespace OpenSheaf.Risks

open OpenSheaf OpenSheaf.Story

theorem story_exp : Events E w0 wExp := .tail story_events (.step sExp)

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

example : lookup wOld "old" (.line paperLine) = some (.live paper4) := rfl

example : ¬ LineOk E wOld "author" (arch ["author"]) paperLine paper4 :=
  not_lineOk (kl := logA3) rfl (by decide)

example : SignedNotContested E logA2 paperLine paper4 4 ∧
    Contested E logA3 paperLine paper4 4 := by
  decide

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

example : Contested E logForkE paperLine paper3 1 ∧
    SignedNotContested E logFork paperLine paper3 1 := by
  decide

example : Contested E logForkE paperLine paper3 3 ∧
    SignedNotContested E logA2 paperLine paper3 1 := by
  decide

theorem forkedE : Events E w0 wForkE := .tail story_events (.step sForkE)

example {w' : World Nat} (hs : Events E wForkE w') {o' : Obj Nat}
    (h : lookup w' "coauthor" (.line paperLine) = some (.live o')) :
    o'.versions = paper3.versions := by
  obtain ⟨_, hl⟩ := Events.fork_freezes_forever E hs (a := "coauthor") (X := "author")
    (kl := logForkE) rfl (by decide)
  obtain ⟨o, ho, hv⟩ := hl paperLine rfl (by decide) o' h
  have : lookup wForkE "coauthor" (.line paperLine) = some (.live paper3) := rfl
  rw [this] at ho; cases ho; exact hv

example : SignedClean E logA2 paperLine paper4 4 :=
  retired_key_signs E (X := "author") (kl := logA2) (s := sigThief) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl rfl (by decide) rfl rfl rfl (by decide) (by decide)

def wTake : World Nat := setEntry w19 "author" (logLine "author") (.live logTake)

theorem sTake : ValidStep E w19 wTake := append_keyLog rfl rfl (by decide)

example : KeyLogOk E "author" logTake :=
  (by decide : KeyLogOk E "author" logA2).append_keyed E rfl rfl (by decide)

example : OwnerKey E wTake "author" sigXP :=
  takeover_ownerKey E (b := "author") (o := logA2) (x := k3x) (ss := [sigK3x]) (k := keysX)
    rfl rfl rfl ⟨rfl, rfl, rfl⟩ (by decide)

example : LineOk E wTake "author" (arch ["author"]) paperLine (paper3.append v4 [sigXP]) :=
  lineOk_host rfl (by decide) (by decide) (by decide) (by decide) (by decide)

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

example {w' : World Nat} (hs : Events E wAnswer w') {o' : Obj Nat}
    (h : lookup w' "author" (.line paperLine) = some (.live o')) :
    o'.versions = paper3.versions := by
  obtain ⟨_, hl⟩ := Events.fork_freezes_forever E hs (a := "author") (X := "author")
    (kl := logAnswer) rfl (by decide)
  obtain ⟨o, ho, hv⟩ := hl paperLine rfl (by decide) o' h
  have : lookup wAnswer "author" (.line paperLine) = some (.live paper3) := rfl
  rw [this] at ho; cases ho; exact hv

example : Contested E logAnswer paperLine (paper3.append v4 [sigXP]) 4 ∧
    SignedNotContested E logAnswer paperLine paper3 3 := by
  decide

end OpenSheaf.Risks
