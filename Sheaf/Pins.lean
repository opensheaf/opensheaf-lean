-- Generated from literate-sheaf/50-pins.md by opensheaf-literate: edit the document, not this file.
import Sheaf.World

namespace OpenSheaf.Sheaf

variable {D : Type} [DecidableEq D] (E : Env D)

/-- **A pin names a section.** Two objects, kept anywhere, in any world, that
both resolve a pin give the same section over the same set, unless their
inventories collide. -/
theorem pin_names_section {o c : Obj D} {p : Pin D} {v u : Version D}
    (hcol : NoCollision E (c.inventory p.version) (o.inventory p.version))
    (ho : resolveEntry E.hash (some (.live o)) p = .ok v)
    (hc : resolveEntry E.hash (some (.live c)) p = .ok u) :
    (∀ x, Covers c p.version x ↔ Covers o p.version x) ∧
    ∀ x (hx : Covers c p.version x) (hx' : Covers o p.version x),
      objSec c p.version x hx = objSec o p.version x hx' := by
  obtain ⟨_, hdo⟩ := resolveEntry_live_ok E.hash ho
  obtain ⟨_, hdc⟩ := resolveEntry_live_ok E.hash hc
  have heq := hcol (hdc.trans hdo.symm)
  have hi : c.id = o.id := congrArg Inventory.id heq
  have ht : c.versions.take p.version = o.versions.take p.version :=
    congrArg Inventory.versions heq
  refine ⟨fun x => ?_, fun x _ _ => ?_⟩
  · simp only [Covers, hi, ht]
  · simp only [objSec, ht]

/-- The version a pin resolves to is the value of the section at the named
document version it holds. -/
theorem resolve_value {o : Obj D} (hwf : WellFormed o.versions) {p : Pin D} {v : Version D}
    (ho : resolveEntry E.hash (some (.live o)) p = .ok v) (hx : Covers o p.version (o.name v)) :
    objSec o p.version (o.name v) hx = v.content :=
  objSec_piece hwf (versionAt_mem_take (resolveEntry_live_ok E.hash ho).1) hx

omit [DecidableEq D] in
/-- **An accepted copy holds what was vetted, at another point.** The section
of an accepted copy at its first document version is the content of the
revision it copies, a document (section 9.6). -/
theorem acceptedCopy_value (l : LineId) (g : Genesis D) (src : Pin D) (v : Version D)
    (psigs ss : List (Sig D)) (d c m : String) (hm : v.members = none)
    (hx : Covers (acceptedCopy l g src v psigs ss d c m) 1 ⟨.line l, 1⟩) :
    objSec (acceptedCopy l g src v psigs ss d c m) 1 ⟨.line l, 1⟩ hx = v.content := by
  simp [objSec, docContent, acceptedCopy, branchVersion, Version.content, hm]

/-- So the copy and the original agree, through the pin of the branch point,
on two different named document versions. -/
theorem acceptedCopy_agrees {o : Obj D} (hwf : WellFormed o.versions) {src : Pin D}
    {v : Version D} (ho : resolveEntry E.hash (some (.live o)) src = .ok v)
    (hm : v.members = none) (l : LineId) (g : Genesis D) (psigs ss : List (Sig D))
    (d c m : String) (hx : Covers (acceptedCopy l g src v psigs ss d c m) 1 ⟨.line l, 1⟩)
    (hy : Covers o src.version (o.name v)) :
    objSec (acceptedCopy l g src v psigs ss d c m) 1 ⟨.line l, 1⟩ hx =
      objSec o src.version (o.name v) hy := by
  rw [acceptedCopy_value l g src v psigs ss d c m hm, resolve_value E hwf ho]

/-- **Every branch holds the files of its parent**, in every world built by
events: the files of the value at the first document version of a branch are
those of the parent version, wherever it is found, unless the copy found
collides with the inventory the branch point was checked against. -/
theorem Events.branch_value_files {w : World D}
    (hs : Events E (fun _ => (none : Option (Archive D))) w) {b : ArchiveId}
    {l : LineId} {c : Obj D} (hl : lookup w b (.line l) = some (.live c)) (hk : c.kind ≠ .owner)
    {x : Version D} (h1 : c.versionAt 1 = some x) {pa : Parent D} (hpa : x.parent = some pa)
    (hx : Covers c 1 (c.name x)) :
    ∃ j : Inventory D, E.hash j = pa.pin.digest ∧
      ∀ b' c' u, lookup w b' (.line pa.pin.line) = some (.live c') →
        resolveAt E.hash w b' pa.pin = .ok u → NoCollision E (c'.inventory pa.pin.version) j →
        (objSec c 1 (c.name x) hx).files = u.content.files := by
  have hne : c.versions ≠ [] := by
    intro he; simp [Obj.versionAt, he] at h1
  have h0 : 0 < c.versions.length := List.length_pos_iff.mpr hne
  have hx0 : c.versions[0] = x := by
    simp only [Obj.versionAt, show (1 : Nat) ≠ 0 by omega, ite_false, Nat.sub_self,
      List.getElem?_eq_getElem h0] at h1
    exact Option.some.inj h1
  obtain ⟨j, hj, _, _, _, hf⟩ := Events.branch_files E hs hl h0 (by rw [hx0]; exact hpa)
    (by simp [prevParent])
  refine ⟨j, hj, fun b' c' u hc' hu hcol => ?_⟩
  have hf := hf b' c' u hc' hu hcol
  rw [objSec_piece ((Events.sound E hs).1 _ _ _ hl |>.history hk) (versionAt_mem_take h1) hx]
  rw [hx0] at hf
  simp only [Version.content, hf]

end OpenSheaf.Sheaf
