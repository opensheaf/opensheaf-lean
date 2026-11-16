-- Generated from literate-sheaf/50-pins.md by opensheaf-literate: edit the document, not this file.
import Sheaf.World

namespace OpenSheaf.Sheaf

variable {D : Type} [DecidableEq D] (hash : Hash D)

/-- **A pin names a section.** Two objects, kept anywhere, in any world, that
both resolve a pin give the same section over the same set, unless their
inventories collide. -/
theorem pin_names_section {o c : Obj D} {p : Pin D} {v u : Version D}
    (hcol : NoCollision hash (c.inventory p.version) (o.inventory p.version))
    (ho : resolveEntry hash (some (.live o)) p = .ok v)
    (hc : resolveEntry hash (some (.live c)) p = .ok u) :
    (∀ x, Covers c p.version x ↔ Covers o p.version x) ∧
    ∀ x (hx : Covers c p.version x) (hx' : Covers o p.version x),
      objSec c p.version x hx = objSec o p.version x hx' := by
  obtain ⟨_, hdo⟩ := resolveEntry_live_ok hash ho
  obtain ⟨_, hdc⟩ := resolveEntry_live_ok hash hc
  have heq := hcol (hdc.trans hdo.symm)
  have ha : c.archive = o.archive := congrArg Inventory.archive heq
  have hi : c.id = o.id := congrArg Inventory.id heq
  have ht : c.versions.take p.version = o.versions.take p.version :=
    congrArg Inventory.versions heq
  refine ⟨fun x => ?_, fun x _ _ => ?_⟩
  · simp only [Covers, ha, hi, ht]
  · simp only [objSec, ht]

/-- The version a pin resolves to is the value of the section at the named
document version it holds. -/
theorem resolve_value {o : Obj D} (hwf : WellFormed o.versions) {p : Pin D} {v : Version D}
    (ho : resolveEntry hash (some (.live o)) p = .ok v) (hx : Covers o p.version (o.name v)) :
    objSec o p.version (o.name v) hx = v.content :=
  objSec_piece hwf (versionAt_mem_take (resolveEntry_live_ok hash ho).1) hx

omit [DecidableEq D] in
/-- **An accepted copy holds what was vetted, at another point.** The section
of an accepted copy at its first document version is the content of the
revision it copies, a document (section 10.5). -/
theorem acceptedCopy_value (s : ArchiveId) (cid : ObjectId) (src : Pin D) (v : Version D)
    (d c m : String) (hm : v.members = none)
    (hx : Covers (acceptedCopy s cid src v d c m) 1 ⟨s, cid, 1⟩) :
    objSec (acceptedCopy s cid src v d c m) 1 ⟨s, cid, 1⟩ hx = v.content := by
  simp [objSec, docContent, acceptedCopy, copyVersion, Version.content, hm]

/-- So the copy and the original agree, through the pin of the source, on two
different named document versions. -/
theorem acceptedCopy_agrees {o : Obj D} (hwf : WellFormed o.versions) {src : Pin D}
    {v : Version D} (ho : resolveEntry hash (some (.live o)) src = .ok v)
    (hm : v.members = none) (s : ArchiveId) (cid : ObjectId) (d c m : String)
    (hx : Covers (acceptedCopy s cid src v d c m) 1 ⟨s, cid, 1⟩)
    (hy : Covers o src.version (o.name v)) :
    objSec (acceptedCopy s cid src v d c m) 1 ⟨s, cid, 1⟩ hx =
      objSec o src.version (o.name v) hy := by
  rw [acceptedCopy_value s cid src v d c m hm, resolve_value hash hwf ho]

/-- **Every copy holds the files of its source**, in every world built by
events: the files of the value at the first document version of an object
that records a source are those of the version the source resolves to. -/
theorem Events.copy_files {w : World D}
    (hs : Events hash (fun _ => (none : Option (Archive D))) w) {b : ArchiveId}
    {i : ObjectId} {c : Obj D} (hl : lookup w b i = some (.live c)) {x : Version D}
    (h1 : c.versionAt 1 = some x) {src : Pin D} (hsx : x.source = some src)
    {u : Version D} (hu : resolve hash w src = .ok u) (hx : Covers c 1 (c.name x)) :
    (objSec c 1 (c.name x) hx).files = u.content.files := by
  rw [objSec_piece ((Events.sound hash hs).1 _ _ _ hl).history (versionAt_mem_take h1) hx]
  simp only [Version.content, Events.copyChecks hash hs hl x src h1 hsx u hu]

end OpenSheaf.Sheaf
