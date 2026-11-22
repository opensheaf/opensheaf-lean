-- Generated from literate/70-story.md by opensheaf-literate: edit the document, not this file.
import OpenSheaf.Impossible
import OpenSheaf.Drafts

namespace OpenSheaf.Story

open OpenSheaf OpenSheaf.Patterns

/-- A toy number for an object identifier. -/
def idNum : ObjectId → Nat
  | .line l => 1000 * l.name.length + 100 * l.owner.length
  | .draft d => 10 * d.length

/-- A toy digest of an inventory. -/
def toy : Hash Nat := fun i =>
  i.versions.foldl (fun h v => 31 * h + v.description.length + 7 * v.documentVersion
    + (v.files.map fun f => 1 + f.1.length + 13 * f.2).sum + v.depositor.length
    + 3 * ((v.keys.map (·.keys.length)).getD 0))
    (i.versions.length + idNum i.id)

/-- The toy digest of a key. -/
def keyDigest (k : Key) : Nat := k.length

/-- The toy names of a genesis record: its nonce. -/
def nameOf (g : Genesis Nat) (_ : Nat) : Name := g.nonce

def keysA1 : Keys Nat := { keys := ["a1"], threshold := 1, next := [4], nextThreshold := 1 }
def keysJ1 : Keys Nat := { keys := ["j1"], threshold := 1, next := [4], nextThreshold := 1 }
def keysC1 : Keys Nat := { keys := ["c1"], threshold := 1, next := [4], nextThreshold := 1 }

def genA : Genesis Nat := { kind := .owner, nonce := "author", keys := some keysA1 }
def genJ : Genesis Nat := { kind := .owner, nonce := "journal", keys := some keysJ1 }
def genC : Genesis Nat := { kind := .owner, nonce := "coauthor", keys := some keysC1 }

def keyLog (x : OwnerName) (g : Genesis Nat) : Obj Nat :=
  { id := .line (keyLogLine x), kind := .owner, genesis := some g,
    versions := [firstKeyVersion g] }

def logA1 : Obj Nat := keyLog "author" genA
def logJ : Obj Nat := keyLog "journal" genJ
def logC : Obj Nat := keyLog "coauthor" genC

def logPin (x : OwnerName) (o : Obj Nat) (n : Nat) : Pin Nat :=
  ⟨keyLogLine x, n, toy (o.inventory n), []⟩

def genP : Genesis Nat := { kind := .document, nonce := "paper", originator := "author" }
def paperLine : LineId := ⟨"paper", "author"⟩

def v1 : Version Nat :=
  { documentVersion := 1, files := [("paper.tm", 101), ("paper.pdf", 102)],
    description := "On sheaves of documents", depositor := "author",
    message := "sealed: first version" }

def paper0 : Obj Nat :=
  { id := .line paperLine, kind := .document, genesis := some genP, versions := [v1] }

def sigP1 : Sig Nat := ⟨paperLine, 1, toy (paper0.inventory 1), "a1", logPin "author" logA1 1⟩

def paper1 : Obj Nat := { paper0 with sigs := [sigP1] }

def pinV1 : Pin Nat := ⟨paperLine, 1, toy (paper1.inventory 1), ["author"]⟩

def issue7 : Members Nat :=
  { type := .selection, members := [{ line := paperLine, hints := ["author"], pins := [pinV1] }] }

def genI : Genesis Nat := { kind := .collection, nonce := "issue7", originator := "journal" }
def issueLine : LineId := ⟨"issue7", "journal"⟩

def i1 : Version Nat :=
  { documentVersion := 1, files := [], members := some issue7, description := "Issue 7",
    depositor := "journal", message := "issue 7: the papers accepted" }

def issue0 : Obj Nat :=
  { id := .line issueLine, kind := .collection, genesis := some genI, versions := [i1] }

def sigI1 : Sig Nat := ⟨issueLine, 1, toy (issue0.inventory 1), "j1", logPin "journal" logJ 1⟩

def issue : Obj Nat := { issue0 with sigs := [sigI1] }

def joint : Members Nat :=
  { type := .catalogue,
    members := [{ line := paperLine, hints := ["author"], follow := true, pins := [pinV1] }] }

def genJt : Genesis Nat := { kind := .collection, nonce := "joint", originator := "coauthor" }
def jointLine : LineId := ⟨"joint", "coauthor"⟩

def j1 : Version Nat :=
  { documentVersion := 1, files := [], members := some joint, description := "Joint papers",
    depositor := "coauthor", message := "joint papers" }

def joint0 : Obj Nat :=
  { id := .line jointLine, kind := .collection, genesis := some genJt, versions := [j1] }

def sigJ1 : Sig Nat := ⟨jointLine, 1, toy (joint0.inventory 1), "c1", logPin "coauthor" logC 1⟩

def jointObj : Obj Nat := { joint0 with sigs := [sigJ1] }

def arch (owners : List OwnerName) : Archive Nat := { entries := fun _ => none, owners }

def w0 : World Nat := fun _ => none
def w1 : World Nat := fun b => if b = "author" then some (arch ["author"]) else w0 b
def w2 : World Nat := fun b => if b = "journal" then some (arch ["journal"]) else w1 b
def w3 : World Nat := fun b => if b = "coauthor" then some (arch ["coauthor"]) else w2 b

def logLine (x : OwnerName) : ObjectId := .line (keyLogLine x)

def w4 : World Nat := setEntry w3 "author" (logLine "author") (.live logA1)
def w5 : World Nat := setEntry w4 "journal" (logLine "journal") (.live logJ)
def w6 : World Nat := setEntry w5 "coauthor" (logLine "coauthor") (.live logC)
def w7 : World Nat := setEntry w6 "coauthor" (logLine "author") (.live logA1)

def w8 : World Nat := setEntry w7 "author" (.line paperLine) (.live paper1)
def w9 : World Nat := setEntry w8 "journal" (.line issueLine) (.live issue)
def w10 : World Nat := setEntry w9 "coauthor" (.line jointLine) (.live jointObj)
def w11 : World Nat := setEntry w10 "coauthor" (.line paperLine) (.live paper1)

def keysA2 : Keys Nat := { keys := ["a33"], threshold := 1, next := [5], nextThreshold := 1 }

def k2 : Version Nat :=
  { documentVersion := 0, files := [], description := "", keys := some keysA2,
    depositor := "author", message := "a1 retired, a33 added" }

def sigK2 : Sig Nat :=
  ⟨keyLogLine "author", 2, toy ((logA1.append k2).inventory 2), "a222", logPin "author" logA1 1⟩

def logA2 : Obj Nat := logA1.append k2 [sigK2]

def w12 : World Nat := setEntry w11 "author" (logLine "author") (.live logA2)
def w13 : World Nat := setEntry w12 "coauthor" (logLine "author") (.live logA2)

def v2 : Version Nat :=
  Version.revise [v1] [("paper.tm", 201), ("paper.pdf", 202)] none
    "On sheaves of documents" "author" "revised after the referees' comments"

def v3 : Version Nat :=
  Version.describe [v1, v2] v1 "On sheaves of documents, I" "author" "title of version 1"

def sigP2 : Sig Nat := ⟨paperLine, 2, toy ((paper1.append v2).inventory 2), "a33", logPin "author" logA2 2⟩
def paper2 : Obj Nat := paper1.append v2 [sigP2]

def sigP3 : Sig Nat := ⟨paperLine, 3, toy ((paper2.append v3).inventory 3), "a33", logPin "author" logA2 2⟩
def paper3 : Obj Nat := paper2.append v3 [sigP3]

def w14 : World Nat := setEntry w13 "author" (.line paperLine) (.live paper2)
def w15 : World Nat := setEntry w14 "author" (.line paperLine) (.live paper3)

def j2 : Version Nat :=
  Version.revise [j1] [] (some (collect toy w15 joint)) "Joint papers" "coauthor" "followed: paper"

def sigJ2 : Sig Nat :=
  ⟨jointLine, 2, toy ((jointObj.append j2).inventory 2), "c1", logPin "coauthor" logC 1⟩

def joint2 : Obj Nat := jointObj.append j2 [sigJ2]

def w16 : World Nat := setEntry w15 "coauthor" (.line jointLine) (.live joint2)

def w17 : World Nat := setEntry w16 "coauthor" (.line paperLine) (.live paper2)
def w18 : World Nat := setEntry w17 "coauthor" (.line paperLine) (.live paper3)

def copyLine : LineId := ⟨"paper", "journal"⟩

def copy0 : Obj Nat :=
  acceptedCopy copyLine genP pinV1 v1 [sigP1] [] "On sheaves of documents (accepted)" "journal"
    "accepted copy of paper v1"

def sigAC : Sig Nat := ⟨copyLine, 1, toy (copy0.inventory 1), "j1", logPin "journal" logJ 1⟩

def copy : Obj Nat :=
  acceptedCopy copyLine genP pinV1 v1 [sigP1] [sigAC] "On sheaves of documents (accepted)" "journal"
    "accepted copy of paper v1"

def w19 : World Nat := setEntry w18 "journal" (.line copyLine) (.live copy)

def v4 : Version Nat :=
  Version.revise paper3.versions [("paper.tm", 666)] none "On sheaves of documents" "author"
    "quietly changed"

def sigThief : Sig Nat :=
  ⟨paperLine, 4, toy ((paper3.append v4).inventory 4), "a1", logPin "author" logA2 1⟩

def keysA3 : Keys Nat :=
  { keys := ["a33"], threshold := 1, next := [6], nextThreshold := 1, exposed := ["a1"] }

def k3 : Version Nat :=
  { documentVersion := 0, files := [], description := "", keys := some keysA3,
    depositor := "author", message := "a1 exposed" }

def sigK3 : Sig Nat :=
  ⟨keyLogLine "author", 3, toy ((logA2.append k3).inventory 3), "a5555", logPin "author" logA2 2⟩

def logA3 : Obj Nat := logA2.append k3 [sigK3]

def i2x : Version Nat :=
  Version.describe issue.versions i1 "Issue 7, as the author would have it" "author" "changed"

def sigAI : Sig Nat :=
  ⟨issueLine, 2, toy ((issue.append i2x).inventory 2), "a33", logPin "author" logA2 2⟩

def k2t : Version Nat :=
  { documentVersion := 0, files := [], description := "",
    keys := some { keys := ["x"], threshold := 1, next := [9], nextThreshold := 1 },
    depositor := "thief", message := "taken over" }

def sigK2t : Sig Nat :=
  ⟨keyLogLine "author", 2, toy ((logA1.append k2t).inventory 2), "a222", logPin "author" logA1 1⟩

def k3c : Version Nat :=
  { documentVersion := 0, files := [], description := "",
    keys := some { keys := ["a33"], threshold := 1, next := [7], nextThreshold := 1 },
    depositor := "author", message := "signed with a current key" }

def sigBad : Sig Nat :=
  ⟨keyLogLine "author", 3, toy ((logA2.append k3c).inventory 3), "a33", logPin "author" logA2 2⟩

def i2 : Version Nat :=
  Version.describe issue.versions i1 "Issue 7 (one paper taken down)" "journal"
    "notice: a paper was taken down"

def sigI2 : Sig Nat := ⟨issueLine, 2, toy ((issue.append i2).inventory 2), "j1", logPin "journal" logJ 1⟩

def keysE : Keys Nat :=
  { keys := ["x"], threshold := 1, next := [9], nextThreshold := 1, exposed := ["a1"] }

def k2e : Version Nat :=
  { documentVersion := 0, files := [], description := "", keys := some keysE,
    depositor := "a thief", message := "a1 exposed, by the thief" }

def sigK2e : Sig Nat :=
  ⟨keyLogLine "author", 2, toy ((logA1.append k2e).inventory 2), "a222", logPin "author" logA1 1⟩

def keysX : Keys Nat := { keys := ["xx"], threshold := 1, next := [8], nextThreshold := 1 }

def k3x : Version Nat :=
  { documentVersion := 0, files := [], description := "", keys := some keysX,
    depositor := "thief", message := "taken over, without a fork" }

def sigK3x : Sig Nat :=
  ⟨keyLogLine "author", 3, toy ((logA2.append k3x).inventory 3), "a5555", logPin "author" logA2 2⟩

def logTake : Obj Nat := logA2.append k3x [sigK3x]

def sigXP : Sig Nat :=
  ⟨paperLine, 4, toy ((paper3.append v4).inventory 4), "xx", logPin "author" logTake 3⟩

def keysEnd : Keys Nat := { ended := true }

def k3end : Version Nat :=
  { documentVersion := 0, files := [], description := "", keys := some keysEnd,
    depositor := "author", message := "ended: a5555 was stolen" }

def sigK3o : Sig Nat :=
  ⟨keyLogLine "author", 3, toy ((logA2.append k3end).inventory 3), "a5555", logPin "author" logA2 2⟩

/-- Every signature someone made, with a key they held. -/
def made : List (Sig Nat) :=
  [sigP1, sigI1, sigJ1, sigK2, sigP2, sigP3, sigJ2, sigAC, sigI2, sigThief, sigK3, sigAI, sigK2t,
    sigBad, sigK2e, sigK3x, sigXP, sigK3o]

def E : Env Nat :=
  { hash := toy, keyDigest := keyDigest, nameOf := nameOf, verifies := fun s => decide (s ∈ made) }

/-- An object whose versions record no branch point passes the check of
branch points. -/
theorem branch_none {F : Env Nat} {w : World Nat} {o : Obj Nat} (h : ∀ v ∈ o.versions, v.parent = none) :
    ∀ i (hi : i < o.versions.length), BranchPointOk F w (prevParent o.versions i) o.versions[i] := by
  intro i hi
  unfold BranchPointOk
  rw [h _ (List.getElem_mem hi)]
  cases i with
  | zero => rfl
  | succ j =>
    simp only [prevParent, List.getElem?_eq_getElem (show j < o.versions.length by omega),
      Option.bind_some]
    exact h _ (List.getElem_mem _)

theorem branch_none_append {F : Env Nat} {w : World Nat} {o : Obj Nat} {x : Version Nat}
    (h : ∀ v ∈ o.versions, v.parent = none) (hx : x.parent = none) :
    BranchPointOk F w (o.versions.getLast?.bind (·.parent)) x := by
  unfold BranchPointOk
  rw [hx]
  cases hl : o.versions.getLast? with
  | none => rfl
  | some v => exact h v (List.mem_of_getLast? hl)

/-- An object whose versions hold no pins passes the check of pins. -/
theorem no_pins {F : Env Nat} {w : World Nat} {o : Obj Nat} (h : ∀ v ∈ o.versions, v.pins = []) :
    ∀ v ∈ o.versions, ∀ p ∈ v.pins, PinOk F w p := by
  intro v hv p hp; rw [h v hv] at hp; cases hp

/-- A pin of a line that is not a key log, whose resolution gives a version,
may be held by a new version. -/
theorem pinOk_of_isOk {F : Env Nat} {w : World Nat} {p : Pin Nat}
    (h : p.line ≠ keyLogLine p.line.owner ∧ (resolve F.hash w p).isOk = true) : PinOk F w p := by
  refine ⟨h.1, Or.inl ((found_iff F.hash).mpr ?_)⟩
  have h2 := h.2
  cases hr : resolve F.hash w p <;> simp_all [Resolution.isOk]

/-- The pins of a list of versions, each of a line that is not a key log and
resolving to a version, may be held. -/
theorem pins_resolve {F : Env Nat} {w : World Nat} {vs : List (Version Nat)}
    (h : ∀ v ∈ vs, ∀ p ∈ v.pins, p.line ≠ keyLogLine p.line.owner ∧ (resolve F.hash w p).isOk = true) :
    ∀ v ∈ vs, ∀ p ∈ v.pins, PinOk F w p :=
  fun v hv p hp => pinOk_of_isOk (h v hv p hp)

theorem identity_owner {F : Env Nat} {l : LineId} {o : Obj Nat} {g : Genesis Nat} (hg : o.genesis = some g)
    (hk : g.kind = o.kind) (ho : o.kind = .owner) (hl : l = keyLogLine l.owner)
    (hkl : KeyLogOk F l.owner o) : IdentityOk F l o := by
  unfold IdentityOk; rw [hg]; exact ⟨hk, by rw [if_yes ho]; exact ⟨hl, hkl⟩⟩

theorem identity_origin {F : Env Nat} {l : LineId} {o : Obj Nat} {g : Genesis Nat} (hg : o.genesis = some g)
    (hk : g.kind = o.kind) (ho : o.kind ≠ .owner) (hl : l.owner = g.originator)
    (hn : l.name = F.nameOf g 0) (hp : ∀ v ∈ o.versions, v.parent = none) : IdentityOk F l o := by
  unfold IdentityOk; rw [hg]; exact ⟨hk, by rw [if_no ho]; exact Or.inl ⟨hl, hn, hp⟩⟩

theorem lineOk_host {F : Env Nat} {w : World Nat} {a : ArchiveId} {ar : Archive Nat} {l : LineId}
    {o kl : Obj Nat} (hkl : lookup w a (.line (keyLogLine l.owner)) = some (.live kl))
    (hv : KeyLogOk F l.owner kl) (hf : ¬ Frozen kl) (hs : SignedClean F kl l o o.versions.length)
    (hin : l.owner ∈ ar.owners) (he : ¬ HasEnding kl) : LineOk F w a ar l o :=
  ⟨kl, hkl, hv, hf, hs, Or.inl ⟨hin, he⟩⟩

/-- The genesis record of `o` names the line `l` of its originator (sections 5.1
and 5.2). -/
def Origin (F : Env Nat) (l : LineId) (o : Obj Nat) : Prop :=
  match o.genesis with
  | none => False
  | some g => g.kind = o.kind ∧ l.owner = g.originator ∧ l.name = F.nameOf g 0

instance (F : Env Nat) (l : LineId) (o : Obj Nat) : Decidable (Origin F l o) := by
  unfold Origin; split <;> infer_instance

theorem Origin.identity {F : Env Nat} {l : LineId} {o : Obj Nat} (h : Origin F l o)
    (hk : o.kind ≠ .owner) (hp : ∀ v ∈ o.versions, v.parent = none) : IdentityOk F l o := by
  unfold Origin at h
  split at h
  · exact h.elim
  · rename_i g hg
    exact identity_origin hg h.1 hk h.2.1 h.2.2 hp

/-- A new object `o` of the originator's line `l`, as computation checks it. -/
def NewLine (F : Env Nat) (l : LineId) (o : Obj Nat) : Prop :=
  o.id = .line l ∧ o.versions ≠ [] ∧ o.kind ≠ .owner ∧ WellFormed o.versions ∧
    (∀ v ∈ o.versions, (v.members.isSome = true ↔ o.kind = .collection) ∧ v.membersOk ∧
      v.parent = none) ∧ StatusOk o.versions ∧ Origin F l o

instance (F : Env Nat) (l : LineId) (o : Obj Nat) : Decidable (NewLine F l o) := by
  unfold NewLine; infer_instance

theorem NewLine.wf {F : Env Nat} {l : LineId} {o : Obj Nat} (h : NewLine F l o) : o.WF (.line l) := by
  obtain ⟨hid, hne, hk, hwf, hv, hst, ho⟩ := h
  refine ⟨hid, hne, fun _ => hwf, fun v hv' => (hv v hv').1, fun v hv' => (hv v hv').2.1, hst, ?_⟩
  unfold Origin at ho
  split at ho
  · exact ho.elim
  · rename_i g hg; rw [hg]; rfl

/-- The version `x` added to the object `o` of an originator's line, as
computation checks it. -/
def NextVersion (o : Obj Nat) (x : Version Nat) : Prop :=
  Extends o.versions x ∧ StatusStep o.versions x ∧
    (x.members.isSome = true ↔ o.kind = .collection) ∧ x.membersOk ∧ x.parent = none ∧
    (∀ v ∈ o.versions, v.parent = none) ∧ o.kind ≠ .owner

instance (o : Obj Nat) (x : Version Nat) : Decidable (NextVersion o x) := by
  unfold NextVersion; infer_instance

/-- The head of `o` is signed by the owner of `l`, against the copy `kl` of its
key log (section 7.5). -/
def SignedAgainst (F : Env Nat) (l : LineId) (o kl : Obj Nat) : Prop :=
  KeyLogOk F l.owner kl ∧ ¬ Frozen kl ∧ SignedClean F kl l o o.versions.length

instance (F : Env Nat) (l : LineId) (o kl : Obj Nat) : Decidable (SignedAgainst F l o kl) := by
  unfold SignedAgainst; infer_instance

theorem create_keyLog {F : Env Nat} {w : World Nat} {a : ArchiveId} {ar : Archive Nat}
    {X : OwnerName} {g : Genesis Nat} (ha : w a = some ar) (hfree : ar.entries (logLine X) = none)
    (hkl : KeyLogOk F X (keyLog X g)) : ValidStep F w (setEntry w a (logLine X) (.live (keyLog X g))) := by
  obtain ⟨g', _, hp⟩ := hkl.parts
  have hg : g' = g := by have := hp.genesis; simp only [keyLog, Option.some.injEq] at this; exact this.symm
  subst hg
  refine .create _ _ _ _ _ ha hfree ⟨rfl, by simp [keyLog], fun h => (h rfl).elim,
    by simp [keyLog, firstKeyVersion], by simp [keyLog, firstKeyVersion, Version.membersOk],
    StatusOk.single _ (fun _ => rfl), rfl⟩
    (no_pins (by simp [keyLog, firstKeyVersion, Version.pins, Version.memberPins, Version.parentPins]))
    (fun _ => branch_none (by simp [keyLog, firstKeyVersion]))
    (fun _ => by simp [HeadFollows, keyLog, firstKeyVersion, Version.FollowsHeads])
    ⟨identity_owner hp.genesis hp.gkind rfl rfl hkl, fun h => (h rfl).elim⟩ (by simp [keyLog])

theorem append_keyLog {F : Env Nat} {w : World Nat} {a : ArchiveId} {ar : Archive Nat}
    {X : OwnerName} {o : Obj Nat} {x : Version Nat} {ss : List (Sig Nat)} (ha : w a = some ar)
    (ho : ar.entries (logLine X) = some (.live o))
    (h : KeyLogOk F X (o.append x ss) ∧ StatusStep o.versions x ∧ x.members = none ∧
      x.pins = [] ∧ x.parent = none ∧ (∀ v ∈ o.versions, v.parent = none) ∧
      ∀ s ∈ ss, SigOk F w a (o.append x ss) s) :
    ValidStep F w (setEntry w a (logLine X) (.live (o.append x ss))) := by
  obtain ⟨hkl, hst, hm, hpins, hx, hpar, hsigs⟩ := h
  obtain ⟨_, _, hp⟩ := hkl.parts
  have hk : o.kind = .owner := hp.kind
  exact .append _ _ _ _ _ _ _ ha ho (fun h => (h hk).elim) hst (by simp [hm, hk])
    (by simp [Version.membersOk, hm]) (by simp [hpins])
    (fun _ => branch_none_append hpar hx) (fun _ _ => by simp [Version.FollowsHeads, hm])
    ⟨identity_owner hp.genesis (hp.gkind.trans hk.symm) hk rfl hkl, fun h => (h hk).elim⟩ hsigs

theorem create_hosted {F : Env Nat} {w : World Nat} {a : ArchiveId} {ar : Archive Nat}
    {l : LineId} {o kl : Obj Nat} (ha : w a = some ar) (hfree : ar.entries (.line l) = none)
    (hkl : lookup w a (.line (keyLogLine l.owner)) = some (.live kl))
    (hpins : ∀ v ∈ o.versions, ∀ p ∈ v.pins, PinOk F w p)
    (h : NewLine F l o ∧ HeadFollows F w o.versions ∧ SignedAgainst F l o kl ∧
      l.owner ∈ ar.owners ∧ ¬ HasEnding kl ∧ ∀ s ∈ o.sigs, SigOk F w a o s) :
    ValidStep F w (setEntry w a (.line l) (.live o)) := by
  obtain ⟨hn, hf, ⟨hv, hfr, hs⟩, hin, he, hsigs⟩ := h
  have hpar : ∀ v ∈ o.versions, v.parent = none := fun v hv' => (hn.2.2.2.2.1 v hv').2.2
  exact .create _ _ _ _ _ ha hfree hn.wf hpins (fun _ => branch_none hpar) (fun _ => hf)
    ⟨hn.2.2.2.2.2.2.identity hn.2.2.1 hpar, fun _ => lineOk_host hkl hv hfr hs hin he⟩ hsigs

theorem append_hosted {F : Env Nat} {w : World Nat} {a : ArchiveId} {ar : Archive Nat}
    {l : LineId} {o kl : Obj Nat} {x : Version Nat} {ss : List (Sig Nat)} (ha : w a = some ar)
    (ho : ar.entries (.line l) = some (.live o))
    (hkl : lookup w a (.line (keyLogLine l.owner)) = some (.live kl))
    (hpins : ∀ v ∈ [x], ∀ p ∈ v.pins, PinOk F w p)
    (h : Origin F l o ∧ NextVersion o x ∧ x.FollowsHeads F w ∧ SignedAgainst F l (o.append x ss) kl ∧
      l.owner ∈ ar.owners ∧ ¬ HasEnding kl ∧ ∀ s ∈ ss, SigOk F w a (o.append x ss) s) :
    ValidStep F w (setEntry w a (.line l) (.live (o.append x ss))) := by
  obtain ⟨hor, ⟨hext, hst, hk, hm, hx, hpar, hko⟩, hf, ⟨hv, hfr, hs⟩, hin, he, hsigs⟩ := h
  have hpar' : ∀ v ∈ (o.append x ss).versions, v.parent = none := by
    simpa [Obj.append, or_imp, forall_and] using ⟨hpar, hx⟩
  exact .append _ _ _ _ _ _ _ ha ho (fun _ => hext) hst hk hm (hpins x (List.mem_singleton_self _))
    (fun _ => branch_none_append hpar hx) (fun _ _ => hf)
    ⟨Origin.identity (o := o.append x ss) hor hko hpar', fun _ => lineOk_host hkl hv hfr hs hin he⟩
    hsigs

theorem create_copy {F : Env Nat} {w : World Nat} {a : ArchiveId} {ar : Archive Nat}
    {l : LineId} {o kl : Obj Nat} (ha : w a = some ar) (hfree : ar.entries (.line l) = none)
    (hkl : lookup w a (.line (keyLogLine l.owner)) = some (.live kl)) (hcopy : CopyOf w a o)
    (hpins : ∀ v ∈ o.versions, ∀ p ∈ v.pins, PinOk F w p)
    (h : NewLine F l o ∧ SignedAgainst F l o kl ∧ ∀ s ∈ o.sigs, SigOk F w a o s) :
    ValidStep F w (setEntry w a (.line l) (.live o)) := by
  obtain ⟨hn, ⟨hv, hfr, hs⟩, hsigs⟩ := h
  have hpar : ∀ v ∈ o.versions, v.parent = none := fun v hv' => (hn.2.2.2.2.1 v hv').2.2
  exact .create _ _ _ _ _ ha hfree hn.wf hpins (fun h => absurd hcopy h) (fun h => absurd hcopy h)
    ⟨hn.2.2.2.2.2.2.identity hn.2.2.1 hpar, fun _ => ⟨kl, hkl, hv, hfr, hs, Or.inr hcopy⟩⟩ hsigs

theorem append_copy {F : Env Nat} {w : World Nat} {a : ArchiveId} {ar : Archive Nat}
    {l : LineId} {o kl : Obj Nat} {x : Version Nat} {ss : List (Sig Nat)} (ha : w a = some ar)
    (ho : ar.entries (.line l) = some (.live o))
    (hkl : lookup w a (.line (keyLogLine l.owner)) = some (.live kl)) (hcopy : CopyOf w a (o.append x ss))
    (hpins : ∀ v ∈ [x], ∀ p ∈ v.pins, PinOk F w p)
    (h : Origin F l o ∧ NextVersion o x ∧ SignedAgainst F l (o.append x ss) kl ∧
      ∀ s ∈ ss, SigOk F w a (o.append x ss) s) :
    ValidStep F w (setEntry w a (.line l) (.live (o.append x ss))) := by
  obtain ⟨hor, ⟨hext, hst, hk, hm, hx, hpar, hko⟩, ⟨hv, hfr, hs⟩, hsigs⟩ := h
  have hpar' : ∀ v ∈ (o.append x ss).versions, v.parent = none := by
    simpa [Obj.append, or_imp, forall_and] using ⟨hpar, hx⟩
  exact .append _ _ _ _ _ _ _ ha ho (fun _ => hext) hst hk hm (hpins x (List.mem_singleton_self _))
    (fun h => absurd hcopy h) (fun h => absurd hcopy h)
    ⟨Origin.identity (o := o.append x ss) hor hko hpar', fun _ => ⟨kl, hkl, hv, hfr, hs, Or.inr hcopy⟩⟩
    hsigs

theorem s1 : ValidStep E w0 w1 := .newArchive _ _ _ rfl (fun _ => rfl)
theorem s2 : ValidStep E w1 w2 := .newArchive _ _ _ rfl (fun _ => rfl)
theorem s3 : ValidStep E w2 w3 := .newArchive _ _ _ rfl (fun _ => rfl)

theorem s4 : ValidStep E w3 w4 := create_keyLog rfl rfl (by decide)
theorem s5 : ValidStep E w4 w5 := create_keyLog rfl rfl (by decide)
theorem s6 : ValidStep E w5 w6 := create_keyLog rfl rfl (by decide)
theorem s7 : ValidStep E w6 w7 := create_keyLog rfl rfl (by decide)

theorem s8 : ValidStep E w7 w8 := create_hosted rfl rfl rfl (no_pins (by decide)) (by decide)

theorem s9 : ValidStep E w8 w9 := create_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)
theorem s10 : ValidStep E w9 w10 := create_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)

theorem copy_w10 : CopyOf w10 "coauthor" paper1 :=
  ⟨"author", paper1, by decide, rfl, rfl, [], by simp⟩

theorem s11 : ValidStep E w10 w11 := create_copy rfl rfl rfl copy_w10 (no_pins (by decide)) (by decide)

theorem s12 : ValidStep E w11 w12 := append_keyLog rfl rfl (by decide)
theorem s13 : ValidStep E w12 w13 := append_keyLog rfl rfl (by decide)

theorem s14 : ValidStep E w13 w14 := append_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)
theorem s15 : ValidStep E w14 w15 := append_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)

example : v2.documentVersion = 2 ∧ v3.documentVersion = 1 := by decide

theorem s16 : ValidStep E w15 w16 := append_hosted rfl rfl rfl (pins_resolve (by decide)) (by decide)

theorem copy_w16 : CopyOf w16 "coauthor" paper2 :=
  ⟨"author", paper3, by decide, rfl, rfl, [v3], by simp [paper3, paper2, Obj.append]⟩

theorem copy_w17 : CopyOf w17 "coauthor" paper3 :=
  ⟨"author", paper3, by decide, rfl, rfl, [], by simp⟩

theorem s17 : ValidStep E w16 w17 :=
  append_copy rfl rfl rfl copy_w16 (pins_resolve (by decide)) (by decide)
theorem s18 : ValidStep E w17 w18 :=
  append_copy rfl rfl rfl copy_w17 (pins_resolve (by decide)) (by decide)

theorem s19 : ValidStep E w18 w19 :=
  acceptedCopy_valid E (a := "journal") rfl rfl genP pinV1 v1 [sigP1] [sigAC] _ _ _
    (b := "author") (by decide) (by decide) (by decide) (by simp [v1])
    (by
      unfold IdentityOk
      refine ⟨rfl, ?_⟩
      rw [if_no (by decide)]
      refine Or.inr ⟨by decide, ⟨0, by decide, rfl⟩, ?_⟩
      intro v hv
      simp only [acceptedCopy, List.mem_singleton] at hv
      subst hv
      exact ⟨_, rfl, by decide, 0, by decide, rfl⟩)
    (lineOk_host rfl (by decide) (by decide) (by decide) (by decide) (by decide))
    (by decide)

def pinCopy : Pin Nat := ⟨copyLine, 1, toy (copy.inventory 1), ["journal"]⟩

theorem story : ValidSteps E w0 w19 :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail
    (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.refl _) s1) s2) s3) s4) s5) s6) s7) s8)
    s9) s10) s11) s12) s13) s14) s15) s16) s17) s18) s19

theorem story_events : Events E w0 w19 := story.mono .step

theorem story_wf : WFWorld E w19 := story.wf E (WFWorld.empty E)

theorem story_pins : PinsOk E w19 := story.pins_ok E

example : HeadSigned E w19 paperLine paper3 :=
  Events.headsSigned E story_events (b := "coauthor") rfl (by decide)

example : KeyLogOk E "author" logA2 :=
  Events.keyLogsOk E story_events (b := "coauthor") (l := keyLogLine "author") rfl rfl

example : HeadSigned E w19 issueLine issue :=
  Events.headsSigned E story_events (b := "journal") rfl (by decide)

example : BranchOk E (prevParent copy.versions 0) (copy.versions[0]'(by decide)) :=
  Events.branchesOk E story_events "journal" (.line copyLine) copy rfl 0 (by decide)

example : verify E w19 issue7 = [(pinV1, .ok v1)] := by decide

example : verify E w19 issue7 = verify E w9 issue7 := by decide

example : collect toy w19 issue7 = issue7 := by decide

def pinV3 : Pin Nat := ⟨paperLine, 3, toy (paper3.inventory 3), ["author"]⟩

example : j2.members = some
    { joint with members :=
        [{ line := paperLine, hints := ["author"], follow := true, pins := [pinV3] }] } := by
  decide

example : resolve toy w19 pinV3 = .ok v3 := by decide

example : resolve toy w19 ⟨paperLine, 3, toy (paper1.inventory 1), ["author"]⟩ = .mismatch := by
  decide

example : resolve toy w19 ⟨paperLine, 4, toy (paper1.inventory 1), ["author"]⟩ = .unavailable := by
  decide

example : resolveAt toy w19 "coauthor" pinV3 = .ok v3 := by decide

example : (copy.versions.map (·.files)) = [v1.files] := by decide

def wGone : World Nat := fun b => if b = "author" then none else w19 b

example : resolve toy wGone pinV3 = .unavailable := by decide

example : resolve toy wGone { pinV3 with hints := ["author", "coauthor"] } = .ok v3 := by decide

example : verify E wGone issue7 = [(pinV1, .unavailable)] := by decide

example : resolve toy wGone { pinV3 with hints := ["author", "coauthor"] } = .ok v3 :=
  resolve_stand_in E (pre := ["author"]) (post := []) (b := "coauthor") rfl
    (fun b' hb' u h => by
      simp only [List.mem_singleton] at hb'
      subst hb'
      have hu : resolveAt E.hash wGone "author" { pinV3 with hints := ["author", "coauthor"] } =
          .unavailable := by decide
      rw [hu] at h; cases h)
    (by decide)

def wDown : World Nat := takedown toy w19 "author" (.line paperLine) paper3

example : verify E wDown issue7 = [(pinV1, .removed)] := by decide

example : resolve toy wDown ⟨paperLine, 1, 0, ["author"]⟩ = .removed := by decide

example : resolve toy wDown pinCopy = resolve toy w19 pinCopy := by decide

example : (resolve toy wDown pinCopy).isOk = true := by decide

theorem story_down : Events E w0 wDown := .tail story_events (.takedown _ _ _ _ (by decide) rfl)

example : SoundWorld E wDown := Events.sound E story_down

def pinV2 : Pin Nat := ⟨paperLine, 2, toy (paper3.inventory 2), ["author"]⟩

theorem pinV2_unheld : ¬ HeldBy wDown pinV2 := by
  intro h
  have no : ∀ (o : Obj Nat), (∀ v ∈ o.versions, ∀ q ∈ v.pins, ¬ q.names pinV2) →
      ∀ c, Entry.live o = .live c → ∀ v ∈ c.versions, ∀ q ∈ v.pins, ¬ q.names pinV2 := by
    intro o ho c hc; cases hc; exact ho
  replace h := heldBy_setEntry h (fun c hc => by cases hc)
  repeat replace h := heldBy_setEntry h (no _ (by decide))
  repeat replace h := heldBy_newArchive rfl (fun _ => rfl) h
  obtain ⟨_, _, _, _, _, hl, _⟩ := h
  simp [lookup, w0] at hl

example : ¬ PinOk E wDown pinV2 := by
  rintro ⟨_, ⟨b, hb, t, ht⟩ | ⟨_, hh⟩⟩
  · simp only [pinV2, List.mem_singleton] at hb
    subst hb
    have hr : resolveAt E.hash wDown "author" pinV2 = .removed := by decide
    rw [hr] at ht; cases ht
  · exact pinV2_unheld hh

def wDown2 : World Nat := setEntry wDown "journal" (.line issueLine) (.live (issue.append i2 [sigI2]))

theorem s20 : ValidStep E wDown wDown2 :=
  append_hosted rfl rfl rfl
    (fun v hv p hp => by
      simp only [List.mem_singleton] at hv
      subst hv
      have h := (by decide : ∀ p ∈ i2.pins, p.line ≠ keyLogLine p.line.owner ∧
        p.hints = ["author"] ∧ resolveAt toy wDown "author" p = .removed) p hp
      refine ⟨h.1, Or.inr ⟨⟨"author", by rw [h.2.1]; simp, h.2.2⟩,
        "journal", .line issueLine, issue, i1, p, rfl, by decide, ?_, Pin.names_refl p⟩⟩
      exact (hp : p ∈ i1.pins))
    (by decide)

example : verify E wDown2 issue7 = [(pinV1, .removed)] := by decide

example : resolve toy wDown { pinV1 with hints := ["author", "coauthor"] } = .ok v1 := by decide

def d1 : Version Nat :=
  { documentVersion := 1, files := [("sequel.tm", 401)], description := "A sequel",
    depositor := "author", message := "started" }

def draft : Obj Nat := { id := .draft "sequel", kind := .document, genesis := none, versions := [d1] }

def wDraft : World Nat := setEntry w19 "author" (.draft "sequel") (.live draft)

theorem sDraft : ValidStep E w19 wDraft :=
  .create _ _ _ _ _ rfl rfl ⟨rfl, by decide, fun _ => by decide, by decide, by decide,
    by decide, rfl⟩ (no_pins (by decide)) (fun _ => branch_none (by decide)) (fun _ => by decide)
    ⟨rfl, by decide, by decide⟩
    (by decide)

def wNoDraft : World Nat := clearEntry wDraft "author" (.draft "sequel")

example : resolve toy wNoDraft pinV3 = resolve toy wDraft pinV3 :=
  DraftEvent.resolve E (.delete _ _ _ _ _ rfl rfl) pinV3

theorem not_lineOk {F : Env Nat} {w : World Nat} {a : ArchiveId} {ar : Archive Nat} {l : LineId}
    {o kl : Obj Nat} (hkl : lookup w a (.line (keyLogLine l.owner)) = some (.live kl))
    (hs : ¬ SignedClean F kl l o o.versions.length) : ¬ LineOk F w a ar l o := by
  rintro ⟨kl', hkl', _, _, hs', _⟩
  rw [hkl] at hkl'; cases hkl'
  exact hs hs'

def issueX : Obj Nat := issue.append i2x [sigAI]

example : ¬ LineOk E w19 "journal" (arch ["journal"]) issueLine issueX :=
  not_lineOk (kl := logJ) rfl (by decide)

def sigForged : Sig Nat :=
  ⟨issueLine, 2, toy ((issue.append i2x).inventory 2), "j1", logPin "journal" logJ 1⟩

example : E.verifies sigForged = false := by decide

example : ¬ LineOk E w19 "journal" (arch ["journal"]) issueLine (issue.append i2x [sigForged]) :=
  not_lineOk (kl := logJ) rfl (by decide)

def v1' : Version Nat := { v1 with files := [("paper.tm", 666), ("paper.pdf", 102)] }

def wTamper : World Nat :=
  setEntry w19 "author" (.line paperLine) (.live { paper3 with versions := [v1', v2, v3] })

example : verify E wTamper issue7 = [(pinV1, .mismatch)] := by decide

example : resolve toy wTamper pinV3 = .mismatch := by decide

example : resolve toy wTamper { pinV1 with hints := ["author", "coauthor"] } = .ok v1 := by decide

example : resolve toy w19 ⟨paperLine, 4, toy ((paper3.append v3).inventory 4), ["author"]⟩ =
    .unavailable := by
  decide

def wd : Version Nat := v3.withdraw "author" "retracted"

example : (Version.describe (paper3.versions ++ [wd]) v1 "On sheaves" "author" "again").status =
    .withdrawn := by decide

example : ¬ StatusStep (paper3.versions ++ [wd]) { v1 with message := "back" } := by
  decide

example : ¬ StatusOk (paper3.versions ++ [wd, { v1 with message := "back" }]) := by decide

def back : Version Nat :=
  Version.revise (paper3.versions ++ [wd]) [("paper.tm", 301), ("paper.pdf", 302)] none
    "On sheaves of documents" "author" "corrected"

example : back.status = .active ∧ StatusStep (paper3.versions ++ [wd]) back :=
  ⟨rfl, revise_statusStep _ _ _ _ _ _⟩

example : DocWithdrawn (paper3.versions ++ [wd, back]) 1 :=
  ⟨0, 3, by decide, by decide, by decide, by decide⟩

example : resolveEntry toy (some (.live copy)) pinV1 = .mismatch := by decide

example : resolveEntry toy (some (.live copy)) pinV1 ≠ .ok v1 :=
  branch_not_copy E (o := paper1) (v := v1) (by decide) (fun h => absurd h (by decide)) (by decide)

def twoPins : Members Nat :=
  { type := .catalogue, members := [{ line := paperLine, hints := ["author"], pins := [pinV1, pinV3] }] }

def followed : Members Nat :=
  { type := .selection,
    members := [{ line := paperLine, hints := ["author"], follow := true, pins := [pinV1] }] }

def unpinned : Members Nat :=
  { type := .selection, members := [{ line := paperLine, hints := ["author"], pins := [] }] }

def nowhere : Members Nat :=
  { type := .selection, members := [{ line := paperLine, hints := [], pins := [{ pinV1 with hints := [] }] }] }

example : ¬ twoPins.WF ∧ ¬ followed.WF ∧ ¬ unpinned.WF ∧ ¬ nowhere.WF := by decide

example : ¬ CopyOf w11 "coauthor" (paper1.append v3) := by
  rintro ⟨b, c, hb, hl, _, t, ht⟩
  by_cases ha : b = "author"
  · subst ha
    have : lookup w11 "author" (.line paperLine) = some (.live paper1) := rfl
    rw [show (paper1.append v3).id = .line paperLine from rfl, this] at hl
    cases hl
    have := congrArg List.length ht
    simp [paper1, paper0, Obj.append] at this
  · have hn : lookup w11 b (.line paperLine) = none := by
      by_cases hj : b = "journal"
      · subst hj; rfl
      · simp [lookup, w11, w10, w9, w8, w7, w6, w5, w4, w3, w2, w1, w0, setEntry, ha, hj, hb]
    rw [show (paper1.append v3).id = .line paperLine from rfl, hn] at hl
    cases hl

def paper4 : Obj Nat := paper3.append v4 [sigThief]

example : LineOk E w19 "author" (arch ["author"]) paperLine paper4 :=
  lineOk_host rfl (by decide) (by decide) (by decide) (by decide) (by decide)

def wExp : World Nat := setEntry w19 "author" (logLine "author") (.live logA3)

theorem sExp : ValidStep E w19 wExp := append_keyLog rfl rfl (by decide)

example : ¬ LineOk E wExp "author" (arch ["author"]) paperLine paper4 :=
  not_lineOk (kl := logA3) rfl (by decide)

example : ¬ KeyLogOk E "author" (logA2.append k3c [sigBad]) := by
  refine current_keys_cannot_extend E (by decide) rfl ?_
  intro s hs _ _ hv
  have hs' : s = sigK2 ∨ s = sigBad := by simpa [logA2, logA1, keyLog, Obj.append] using hs
  rcases hs' with rfl | rfl
  · exact absurd hv (by decide)
  · exact ⟨1, by decide, keysA2, rfl, by decide⟩

def keysT : Keys Nat := { keys := ["x"], threshold := 1, next := [9], nextThreshold := 1 }

def carriedT : Carried Nat :=
  { version := 2
    digest := toy ((logA1.append k2t).inventory 2)
    keys := keysT
    sigs := [sigK2t]
    depositor := k2t.depositor
    message := k2t.message }

def fr : Version Nat :=
  { documentVersion := 0, files := [], description := "", keys := none,
    carried := [carriedT],
    depositor := "coauthor", message := "fork record" }

def logFork : Obj Nat := logA2.append fr

def wFork : World Nat := setEntry w19 "coauthor" (logLine "author") (.live logFork)

theorem sFork : ValidStep E w19 wFork := append_keyLog rfl rfl (by decide)

example (o' : Obj Nat) : ¬ LineOk E wFork "coauthor" (arch ["coauthor"]) paperLine o' :=
  frozen_adds_nothing E (kl := logFork) rfl (by decide)

example : SignedNotContested E logFork paperLine paper3 1 ∧
    Contested E logFork paperLine paper3 3 ∧ SignedNotContested E logA2 paperLine paper3 3 := by
  decide

theorem after9 : ValidSteps E w9 w19 :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.refl _) s10) s11) s12)
    s13) s14) s15) s16) s17) s18) s19

example : resolveAt toy w19 "author" pinV1 = .ok v1 :=
  Steps.resolveAt_ok toy (after9.toSteps E) (by decide)

example : resolveAt toy wDown "author" pinV1 = .removed :=
  (takedown_reported E (w := w19) (a := "author") (oid := .line paperLine) rfl "author" pinV1).trans
    (by decide)

example : resolveAt toy w19 "author" pinV1 ≠ .ok v1' :=
  pin_meaning_fixed E (after9.toSteps E) (b := "author") (p := pinV1) (v := v1) (by decide)
    (by decide)

theorem author_w19 : lookup w19 "author" (.line paperLine) = some (.live paper3) := rfl

example (u : Version Nat) : resolveAt toy wTamper "author" pinV1 ≠ .ok u :=
  tamper_detected E (w := w19) (a := "author") (o := paper3) (p := pinV1) (v := v1)
    (o' := { paper3 with versions := [v1', v2, v3] }) author_w19
    (by decide) (fun h => absurd (congrArg toy h) (by decide))
    (fun h => absurd h (by decide)) u

example : ¬ Steps w19 wTamper := fun hs =>
  history_not_rewritten hs author_w19 rfl (by decide)

example {w' : World Nat}
    (h : DocWithdrawnAt (setEntry w19 "author" (.line paperLine) (.live (paper3.append wd)))
      "author" (.line paperLine) 1)
    (hs : Steps (setEntry w19 "author" (.line paperLine) (.live (paper3.append wd))) w') :
    DocWithdrawnAt w' "author" (.line paperLine) 1 :=
  Steps.docWithdrawn_stays hs h

end OpenSheaf.Story
