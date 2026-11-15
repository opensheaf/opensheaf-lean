# Pins and accepted copies

The previous chapter proved that copies agree in a world built by valid
events. There the agreement comes from the protocol: the steps that write
mirrors, and the rule of section 7.3. A pin gives agreement in another way,
from the digest. Any two objects that resolve the same pin give the same
section, wherever they are kept and whatever world they belong to, unless
their inventories collide. A reader who holds a pin does not need to trust
the archive that serves it, or to know that the archive is a mirror: the
compatibility of what they read is checked, not assumed.

An accepted copy (section 10.5) is the other case. It holds the content of
the revision it copies, but under its own name, in the selection's archive.
It is not the same point as the original, and the sheaf does not glue them.
The pin of its source relates the two points: the value of the copy at its
first document version is the value of the original at the revision.

## A pin names a section

The digest of an inventory fixes the inventory: the archive and identifier
of the object, and its object versions up to the pinned one. So, unless
two inventories collide, a pin fixes both the set held by its object
version and the section over it. The hypothesis on collisions is the same
as in the model (`NoCollision`).

    -- in Sheaf/Pins.lean:
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

The theorem needs no hypothesis on the world, and no well-formed history.
It is the sheaf-theoretic reading of section 6.4: "Any copy whose bytes
match the pinned digest is acceptable: integrity comes from the pin, not
from the place." What any such copy gives is a section of the same sheaf.

## The version a pin resolves to

The version a pin resolves to is one of the pieces of the pinned object
version, so its content is the value of the section at the document
version it holds.

    omit [DecidableEq D] in
    theorem versionAt_mem_take {o : Obj D} {n : Nat} {v : Version D}
        (h : o.versionAt n = some v) : v ∈ o.versions.take n := by
      unfold Obj.versionAt at h
      split at h
      · contradiction
      · rename_i hn
        have h' : (o.versions.take n)[n - 1]? = some v := by
          rw [List.getElem?_take]; simp [show n - 1 < n by omega, h]
        exact List.mem_of_getElem? h'

    /-- The version a pin resolves to is the value of the section at the named
    document version it holds. -/
    theorem resolve_value {o : Obj D} (hwf : WellFormed o.versions) {p : Pin D} {v : Version D}
        (ho : resolveEntry hash (some (.live o)) p = .ok v) (hx : Covers o p.version (o.name v)) :
        objSec o p.version (o.name v) hx = v.content :=
      objSec_piece hwf (versionAt_mem_take (resolveEntry_live_ok hash ho).1) hx

## Accepted copies

The first document version of an accepted copy holds the files of the
revision it copies, byte for byte (section 10.5). In the model, a copy
keeps the files and the references of the revision, and a copy is made of
a document, which has no member list. So the value of the copy at its first
document version is the content of the revision.

    omit [DecidableEq D] in
    /-- **An accepted copy holds what was vetted, at another point.** The section
    of an accepted copy at its first document version is the content of the
    revision it copies, a document (section 10.5). -/
    theorem acceptedCopy_value (s : ArchiveId) (cid : ObjectId) (src : Pin D) (v : Version D)
        (d c m : String) (hm : v.members = none)
        (hx : Covers (acceptedCopy s cid src v d c m) 1 ⟨s, cid, 1⟩) :
        objSec (acceptedCopy s cid src v d c m) 1 ⟨s, cid, 1⟩ hx = v.content := by
      simp [objSec, docContent, acceptedCopy, copyVersion, Version.content, hm]

With the previous theorem, the copy and the original agree through the pin
of the source. The two values are equal, at two different points: the
copy's own name, and the revision's name. So an accepted copy is not a
second section over the same set, as a mirror is: the theorem is an
equality of the values at two different points of the base. The verifier checks that the
map preserves it (section 14: "for each accepted copy, check that its first
document version holds exactly the files of the source version").

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

    end OpenSheaf.Sheaf
