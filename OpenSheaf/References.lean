-- Generated from literate/80-references.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Story

namespace OpenSheaf

open OpenSheaf.Patterns

variable {D : Type} [DecidableEq D] (hash : Hash D)

omit [DecidableEq D] in
theorem Version.ref_pin {v : Version D} {r : Ref D} (hr : r ∈ v.refs) : r.pin ∈ v.pins :=
  List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩)

/-- **References never dangle**, in a world built by valid steps. -/
theorem ValidSteps.refs_resolve {w : World D}
    (hs : ValidSteps hash (fun _ => (none : Option (Archive D))) w)
    {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
    {v : Version D} (hv : v ∈ o.versions) {r : Ref D} (hr : r ∈ v.refs) :
    ∃ t, resolve hash w r.pin = .ok t :=
  hs.pins_ok hash a oid o hl v hv r.pin (Version.ref_pin hr)

/-- With takedowns, references resolve or report `removed`. -/
theorem Events.refs_held {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w)
    {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
    {v : Version D} (hv : v ∈ o.versions) {r : Ref D} (hr : r ∈ v.refs) :
    (∃ t, resolve hash w r.pin = .ok t) ∨ resolve hash w r.pin = .removed :=
  (Events.sound hash hs).2 a oid o hl v hv r.pin (Version.ref_pin hr)

/-- **No two versions refer to each other**, in a world built by events. -/
theorem no_mutual_refs {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) {s t : Site}
    (h1 : PinsTo hash w s t) : ¬ PinsTo hash w t s :=
  fun h2 => no_cycles_events hash hs s (.cons h1 (.single h2))

/-- What a verifier aware of references reports for a version. -/
def verifyRefs (w : World D) (v : Version D) : List (Ref D × Resolution D) :=
  v.refs.map fun r => (r, resolve hash w r.pin)

/-- **A pin fixes what the version refers to.** -/
theorem pin_fixes_refs {w w' : World D} (hs : Steps w w') {p : Pin D} {a : Version D}
    (hp : resolve hash w p = .ok a) (hok : ∀ r ∈ a.refs, ∃ d, resolve hash w r.pin = .ok d) :
    resolve hash w' p = .ok a ∧ verifyRefs hash w' a = verifyRefs hash w a := by
  refine ⟨Steps.resolve_ok hash hs hp, ?_⟩
  unfold verifyRefs
  apply List.map_congr_left
  intro r hr
  obtain ⟨d, hd⟩ := hok r hr
  rw [Steps.resolve_ok hash hs hd, hd]

/-- **References travel with every copy.** -/
theorem copy_keeps_refs {o c : Obj D} {p : Pin D} {a u : Version D}
    (hcol : NoCollision hash (c.inventory p.version) (o.inventory p.version))
    (ho : resolveEntry hash (some (.live o)) p = .ok a)
    (hc : resolveEntry hash (some (.live c)) p = .ok u) : u.refs = a.refs := by
  rw [copy_authentic hash hcol ho hc]

/-- **A core verifier does not see a takedown behind a reference.** -/
theorem takedown_behind_ref {w : World D} {b : ArchiveId} {x : ObjectId} {o : Obj D}
    (hl : lookup w b x = some (.live o)) {s : Members D}
    (hs : ∀ p ∈ s.pins, ¬ (p.archive = b ∧ p.object = x)) {r : Ref D}
    (hr : r.pin.archive = b ∧ r.pin.object = x) :
    verify hash (takedown hash w b x o) s = verify hash w s ∧
      resolve hash (takedown hash w b x o) r.pin = .removed := by
  refine ⟨?_, takedown_removed hash hl hr⟩
  unfold verify
  apply List.map_congr_left
  intro p hp
  rw [takedown_other hash hl (hs p hp)]

end OpenSheaf

namespace OpenSheaf.Companions

open OpenSheaf OpenSheaf.Patterns OpenSheaf.Story

def y0 : World Nat := fun _ => none
def y1 : World Nat := fun b => if b = "author" then some (emptyArchive ["author"]) else y0 b
def y2 : World Nat := fun b => if b = "journal" then some (emptyArchive ["editor"]) else y1 b

theorem b1 : StepBy toy "author" y0 y1 := .newArchive _ _ _ rfl (fun _ => rfl) (by decide)
theorem b2 : StepBy toy "editor" y1 y2 := .newArchive _ _ _ rfl (fun _ => rfl) (by decide)

def d1 : Version Nat :=
  { documentVersion := 1, files := [("details.tm", 61)], description := "The detailed argument",
    depositor := "author", message := "first version" }

def d2 : Version Nat :=
  Version.revise [d1] [("details.tm", 62), ("details.lean", 63)] none "The detailed argument"
    "author" "a gap closed; with a formal proof"

def details2 : Obj Nat :=
  { archive := "author", id := "kpz-details", kind := .document, versions := [d1, d2] }

def y3 : World Nat := setEntry y2 "author" "kpz-details" (.live details2)

theorem b3 : StepBy toy "author" y2 y3 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
    (by simp [details2, d1, d2, Version.revise, Version.pins]) (Or.inl rfl) (by decide)
    (by decide) (by decide)

def pinD2 : Pin Nat := ⟨"author", "kpz-details", 2, toy (details2.inventory 2)⟩

def a1 : Version Nat :=
  { documentVersion := 1, files := [("account.tm", 71)], description := "A short account",
    refs := [⟨"IsSupplementedBy", pinD2⟩], depositor := "author", message := "first version" }

def account : Obj Nat :=
  { archive := "author", id := "kpz-account", kind := .document, versions := [a1] }

def y4 : World Nat := setEntry y3 "author" "kpz-account" (.live account)

theorem b4 : StepBy toy "author" y3 y4 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
    (fun v hv p hp => held_of_isOk ((by decide :
      ∀ v ∈ account.versions, ∀ p ∈ v.pins, (resolve toy y3 p).isOk = true) v hv p hp))
    (Or.inl rfl) (by decide) (by decide) (by decide)

def pinA1 : Pin Nat := ⟨"author", "kpz-account", 1, toy (account.inventory 1)⟩

def d3 : Version Nat :=
  { Version.describe [d1, d2] d2 "The detailed argument" "author" "link back to the account"
    with refs := [⟨"IsSupplementTo", pinA1⟩] }

def details3 : Obj Nat := details2.append d3

def y5 : World Nat := setEntry y4 "author" "kpz-details" (.live details3)

theorem b5 : StepBy toy "author" y4 y5 :=
  .append _ _ _ _ _ _ rfl rfl (by decide) (by decide) (by decide) (by decide)
    (fun p hp => held_of_isOk ((by decide :
      ∀ p ∈ d3.pins, (resolve toy y4 p).isOk = true) p hp)) (Or.inl rfl) (by decide)
    (by decide) (by decide)

example : d3.documentVersion = d2.documentVersion := by decide

def issue7 : Members Nat :=
  { type := .selection,
    members := [{ archive := "author", object := "kpz-account", pins := [pinA1] }] }

def i1 : Version Nat :=
  { documentVersion := 1, files := [], members := some issue7, description := "Issue 7",
    depositor := "editor", message := "accepted: the account, version 1" }

def issueObj : Obj Nat :=
  { archive := "journal", id := "issue-7", kind := .collection, versions := [i1] }

def y6 : World Nat := setEntry y5 "journal" "issue-7" (.live issueObj)
def y7 : World Nat := setEntry y6 "journal" "kpz-account" (.live account)

theorem b6 : StepBy toy "editor" y5 y6 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
    (fun v hv p hp => held_of_isOk ((by decide :
      ∀ v ∈ issueObj.versions, ∀ p ∈ v.pins, (resolve toy y5 p).isOk = true) v hv p hp))
    (Or.inl rfl) (by decide) (by decide) (by decide)

theorem b7 : StepBy toy "editor" y6 y7 :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩
    (fun v hv p hp => held_of_isOk ((by decide :
      ∀ v ∈ account.versions, ∀ p ∈ v.pins, (resolve toy y6 p).isOk = true) v hv p hp))
    (Or.inr ⟨account, rfl, rfl, [], (List.append_nil _).symm⟩) (by decide) (by decide) (by decide)

theorem steps : Star ByAgent y0 y7 :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.refl _)
    ⟨_, b1⟩) ⟨_, b2⟩) ⟨_, b3⟩) ⟨_, b4⟩) ⟨_, b5⟩) ⟨_, b6⟩) ⟨_, b7⟩

theorem valid : ValidSteps toy y0 y7 := steps.mono fun ⟨_, h⟩ => h.toValidStep toy

example : verify toy y7 issue7 = [(pinA1, .ok a1)] := by decide

example : verifyRefs toy y7 a1 = [(⟨"IsSupplementedBy", pinD2⟩, .ok d2)] := by decide

example : verifyRefs toy y7 d3 = [(⟨"IsSupplementTo", pinA1⟩, .ok a1)] := by decide

example : ∃ t, resolve toy y7 pinD2 = .ok t :=
  ValidSteps.refs_resolve toy valid (a := "author") (oid := "kpz-account") (o := account) rfl
    (v := a1) (by simp [account]) (r := ⟨"IsSupplementedBy", pinD2⟩) (by simp [a1])

example (s : Site) : ¬ Chain (PinsTo toy y7) s s := no_cycles toy valid s

example : (resolve toy y4 ⟨"author", "kpz-account", 2, 0⟩).isOk = false := by decide

def yGone : World Nat := fun b => if b = "author" then none else y7 b

example : resolveVia toy yGone pinA1 ["journal"] = .ok a1 := by decide

example : resolveVia toy yGone pinD2 ["journal"] = .unavailable := by decide

def yDown : World Nat := takedown toy y7 "author" "kpz-details" details3

example : verify toy yDown issue7 = [(pinA1, .ok a1)] := by decide

example : verifyRefs toy yDown a1 = [(⟨"IsSupplementedBy", pinD2⟩, .removed)] := by decide

example : verify toy yDown issue7 = verify toy y7 issue7 ∧ resolve toy yDown pinD2 = .removed :=
  takedown_behind_ref toy (o := details3) rfl (by decide) (r := ⟨"IsSupplementedBy", pinD2⟩)
    ⟨rfl, rfl⟩

end OpenSheaf.Companions
