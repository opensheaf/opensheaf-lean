-- Generated from literate/80-references.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Story

namespace OpenSheaf

open OpenSheaf.Patterns

variable {D : Type} [DecidableEq D] (E : Env D)

omit [DecidableEq D] in
theorem Version.ref_pin {v : Version D} {r : Ref D} (hr : r ∈ v.refs) : r.pin ∈ v.pins :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩))

/-- **References never dangle**, in a world built by valid steps. -/
theorem ValidSteps.refs_resolve {w : World D}
    (hs : ValidSteps E (fun _ => (none : Option (Archive D))) w)
    {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
    {v : Version D} (hv : v ∈ o.versions) {r : Ref D} (hr : r ∈ v.refs) :
    Found E.hash w r.pin :=
  hs.pins_ok E a oid o hl v hv r.pin (Version.ref_pin hr)

/-- With takedowns, references are found or report `removed`. -/
theorem Events.refs_held {w : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w)
    {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
    {v : Version D} (hv : v ∈ o.versions) {r : Ref D} (hr : r ∈ v.refs) :
    Held E w r.pin :=
  (Events.sound E hs).2 a oid o hl v hv r.pin (Version.ref_pin hr)

/-- What a verifier aware of references reports for a version. -/
def verifyRefs (w : World D) (v : Version D) : List (Ref D × Resolution D) :=
  v.refs.map fun r => (r, resolve E.hash w r.pin)

/-- **A pin fixes what the version refers to.** -/
theorem pin_fixes_refs {w w' : World D}
    (hw' : Events E (fun _ => (none : Option (Archive D))) w') (hs : Steps w w') {p : Pin D}
    {a : Version D} (hp : resolve E.hash w p = .ok a) (hhp : HonestPins E w' [p])
    (hhr : HonestPins E w' (a.refs.map (·.pin)))
    (hok : ∀ r ∈ a.refs, ∃ d, resolve E.hash w r.pin = .ok d) :
    resolve E.hash w' p = .ok a ∧ verifyRefs E w' a = verifyRefs E w a := by
  have h1 := hhp p (List.mem_singleton_self _)
  refine ⟨Steps.resolve_ok E hw' hs h1.1 h1.2 hp, ?_⟩
  unfold verifyRefs
  apply List.map_congr_left
  intro r hr
  obtain ⟨d, hd⟩ := hok r hr
  have h2 := hhr r.pin (List.mem_map.mpr ⟨r, hr, rfl⟩)
  rw [Steps.resolve_ok E hw' hs h2.1 h2.2 hd, hd]

/-- **References travel with every copy.** -/
theorem copy_keeps_refs {o c : Obj D} {p : Pin D} {a u : Version D}
    (hcol : NoCollision E (c.inventory p.version) (o.inventory p.version))
    (ho : resolveEntry E.hash (some (.live o)) p = .ok a)
    (hc : resolveEntry E.hash (some (.live c)) p = .ok u) : u.refs = a.refs := by
  rw [copy_authentic E hcol ho hc]

/-- **A core verifier does not see a takedown behind a reference.** -/
theorem takedown_behind_ref {w : World D} {b : ArchiveId} {x : ObjectId} {o : Obj D}
    (hl : lookup w b x = some (.live o)) {s : Members D}
    (hs : ∀ p ∈ s.pins, ∀ c ∈ p.hints, ¬ (c = b ∧ ObjectId.line p.line = x)) {r : Ref D}
    (hr : ObjectId.line r.pin.line = x) :
    verify E (takedown E.hash w b x o) s = verify E w s ∧
      resolveAt E.hash (takedown E.hash w b x o) b r.pin = .removed := by
  refine ⟨?_, takedown_removed E.hash hl hr⟩
  unfold verify
  apply List.map_congr_left
  intro p hp
  unfold resolve
  congr 2
  apply List.map_congr_left
  intro c hc
  rw [takedown_other E.hash hl (hs p hp c hc)]

end OpenSheaf

namespace OpenSheaf.Companions

open OpenSheaf OpenSheaf.Patterns OpenSheaf.Story

def genDt : Genesis Nat := { kind := .document, nonce := "details", originator := "author" }
def detailsLine : LineId := ⟨"details", "author"⟩

def d1 : Version Nat :=
  { documentVersion := 1, files := [("details.tm", 61)], description := "The detailed argument",
    depositor := "author", message := "first version" }

def d2 : Version Nat :=
  Version.revise [d1] [("details.tm", 62), ("details.lean", 63)] none "The detailed argument"
    "author" "a gap closed; with a formal proof"

def details0 : Obj Nat :=
  { id := .line detailsLine, kind := .document, genesis := some genDt, versions := [d1, d2] }

def sigD2 : Sig Nat := ⟨detailsLine, 2, toy (details0.inventory 2), "a1", logPin "author" logA1 1⟩

def details2 : Obj Nat := { details0 with sigs := [sigD2] }

def pinD2 : Pin Nat := ⟨detailsLine, 2, toy (details2.inventory 2), ["author"]⟩

def genAc : Genesis Nat := { kind := .document, nonce := "account", originator := "author" }
def accountLine : LineId := ⟨"account", "author"⟩

def a1 : Version Nat :=
  { documentVersion := 1, files := [("account.tm", 71)], description := "A short account",
    refs := [⟨"IsSupplementedBy", pinD2⟩], depositor := "author", message := "first version" }

def account0 : Obj Nat :=
  { id := .line accountLine, kind := .document, genesis := some genAc, versions := [a1] }

def sigA1 : Sig Nat := ⟨accountLine, 1, toy (account0.inventory 1), "a1", logPin "author" logA1 1⟩

def account : Obj Nat := { account0 with sigs := [sigA1] }

def pinA1 : Pin Nat := ⟨accountLine, 1, toy (account.inventory 1), ["author", "journal"]⟩

def d3 : Version Nat :=
  { Version.describe [d1, d2] d2 "The detailed argument" "author" "link back to the account"
    with refs := [⟨"IsSupplementTo", pinA1⟩] }

def sigD3 : Sig Nat :=
  ⟨detailsLine, 3, toy ((details2.append d3).inventory 3), "a1", logPin "author" logA1 1⟩

def details3 : Obj Nat := details2.append d3 [sigD3]

example : d3.documentVersion = d2.documentVersion := by decide

def issue7 : Members Nat :=
  { type := .selection,
    members := [{ line := accountLine, hints := ["author", "journal"], pins := [pinA1] }] }

def genI7 : Genesis Nat := { kind := .collection, nonce := "issue7", originator := "journal" }
def issueLine : LineId := ⟨"issue7", "journal"⟩

def i1 : Version Nat :=
  { documentVersion := 1, files := [], members := some issue7, description := "Issue 7",
    depositor := "journal", message := "accepted: the account, version 1" }

def issue0 : Obj Nat :=
  { id := .line issueLine, kind := .collection, genesis := some genI7, versions := [i1] }

def sigI1 : Sig Nat := ⟨issueLine, 1, toy (issue0.inventory 1), "j1", logPin "journal" logJ 1⟩

def issueObj : Obj Nat := { issue0 with sigs := [sigI1] }

def madeC : List (Sig Nat) := [sigD2, sigA1, sigD3, sigI1]

def EC : Env Nat :=
  { hash := toy, keyDigest := keyDigest, nameOf := nameOf, verifies := fun s => decide (s ∈ madeC) }

def y0 : World Nat := fun _ => none
def y1 : World Nat := fun b => if b = "author" then some (arch ["author"]) else y0 b
def y2 : World Nat := fun b => if b = "journal" then some (arch ["journal"]) else y1 b
def y3 : World Nat := setEntry y2 "author" (logLine "author") (.live logA1)
def y4 : World Nat := setEntry y3 "journal" (logLine "journal") (.live logJ)
def y5 : World Nat := setEntry y4 "journal" (logLine "author") (.live logA1)
def y6 : World Nat := setEntry y5 "author" (.line detailsLine) (.live details2)
def y7 : World Nat := setEntry y6 "author" (.line accountLine) (.live account)
def y8 : World Nat := setEntry y7 "author" (.line detailsLine) (.live details3)
def y9 : World Nat := setEntry y8 "journal" (.line issueLine) (.live issueObj)
def y10 : World Nat := setEntry y9 "journal" (.line accountLine) (.live account)

theorem b1 : ValidStep EC y0 y1 := .newArchive _ _ _ rfl (fun _ => rfl)
theorem b2 : ValidStep EC y1 y2 := .newArchive _ _ _ rfl (fun _ => rfl)

theorem b3 : ValidStep EC y2 y3 := create_keyLog rfl rfl (by decide)
theorem b4 : ValidStep EC y3 y4 := create_keyLog rfl rfl (by decide)
theorem b5 : ValidStep EC y4 y5 := create_keyLog rfl rfl (by decide)

theorem b6 : ValidStep EC y5 y6 := create_hosted rfl rfl rfl (no_pins (by decide)) (by decide)
theorem b7 : ValidStep EC y6 y7 := create_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)
theorem b8 : ValidStep EC y7 y8 := append_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)
theorem b9 : ValidStep EC y8 y9 := create_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)

theorem copy_y9 : CopyOf y9 "journal" account := ⟨"author", account, by decide, rfl, rfl, [], by simp⟩

theorem b10 : ValidStep EC y9 y10 :=
  create_copy rfl rfl rfl copy_y9 (pins_resolve (by decide)) (by decide)

theorem valid : ValidSteps EC y0 y10 :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.refl _) b1) b2) b3) b4)
    b5) b6) b7) b8) b9) b10

example : verify EC y10 issue7 = [(pinA1, .ok a1)] := by decide

example : verifyRefs EC y10 a1 = [(⟨"IsSupplementedBy", pinD2⟩, .ok d2)] := by decide

example : verifyRefs EC y10 d3 = [(⟨"IsSupplementTo", pinA1⟩, .ok a1)] := by decide

example : Found toy y10 pinD2 :=
  ValidSteps.refs_resolve EC valid (a := "author") (oid := .line accountLine) (o := account) rfl
    (v := a1) (by simp [account, account0]) (r := ⟨"IsSupplementedBy", pinD2⟩) (by simp [a1])

example : (resolve toy y7 ⟨accountLine, 2, 0, ["author"]⟩).isOk = false := by decide

def yGone : World Nat := fun b => if b = "author" then none else y10 b

example : resolve toy yGone pinA1 = .ok a1 := by decide

example : resolve toy yGone { pinD2 with hints := ["author", "journal"] } = .unavailable := by
  decide

def yDown : World Nat := takedown toy y10 "author" (.line detailsLine) details3

example : verify EC yDown issue7 = [(pinA1, .ok a1)] := by decide

example : verifyRefs EC yDown a1 = [(⟨"IsSupplementedBy", pinD2⟩, .removed)] := by decide

example : verify EC yDown issue7 = verify EC y10 issue7 ∧
    resolveAt toy yDown "author" pinD2 = .removed :=
  takedown_behind_ref EC (o := details3) rfl (by decide) (r := ⟨"IsSupplementedBy", pinD2⟩) rfl

end OpenSheaf.Companions
