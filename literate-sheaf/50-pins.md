# Pins and accepted copies

The previous chapter proved that copies agree in a world built by events,
when owners are honest. There the agreement comes from the protocol and the
owners' keys: the steps that write copies, the signatures they check, and
the rule of section 4.2. A pin gives agreement in another way,
from the digest. Any two objects that resolve the same pin give the same
section, wherever they are kept and whatever world they belong to, unless
their inventories collide. A reader who holds a pin does not need to trust
the archive that serves it, or to know that the archive is a mirror: the
compatibility of what they read is checked, not assumed.

An accepted copy (section 9.6) is the other case. It is a branch: another
line, of the selection's owner, which holds the content of the revision it
copies under its own name. It is not the same point as the original, and
the sheaf does not glue them. The pin of its branch point relates the two
points: the value of the copy at its first document version is the value of
the original at the revision.

## A pin names a section

The digest of an inventory fixes the inventory: the identifier of the
object, its genesis record, and its object versions up to the pinned one. So, unless
two inventories collide, a pin fixes both the set held by its object
version and the section over it. The hypothesis on collisions is the same
as in the model (`NoCollision`).

    -- in Sheaf/Pins.lean:
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

The theorem needs no hypothesis on the world, and no well-formed history.
It is the sheaf-theoretic reading of section 8.5: "any copy whose bytes
match the pin will do". What any such copy gives is a section of the same sheaf.

## The version a pin resolves to

The version a pin resolves to is one of the pieces of the pinned object
version, so its content is the value of the section at the document
version it holds.

    /-- The version a pin resolves to is the value of the section at the named
    document version it holds. -/
    theorem resolve_value {o : Obj D} (hwf : WellFormed o.versions) {p : Pin D} {v : Version D}
        (ho : resolveEntry E.hash (some (.live o)) p = .ok v) (hx : Covers o p.version (o.name v)) :
        objSec o p.version (o.name v) hx = v.content :=
      objSec_piece hwf (versionAt_mem_take (resolveEntry_live_ok E.hash ho).1) hx

## Accepted copies

The first version of a branch holds exactly the files of its parent version
(section 9.2), and an accepted copy is a branch (section 9.6). Two
statements say so. The first is about the copy the model builds
(`acceptedCopy`): it keeps the files of the revision, and a copy is made of
a document, which has no member list, so the value of the copy at its first
document version is the content of the revision. The second is about every
branch in every world built by events, however it was made: by the model's
`Events.branch_files`, the files of a version that sets a branch point are
those of the parent version, wherever a reader finds it, unless two
inventories with the parent's digest collide.

    omit [DecidableEq D] in
    /-- **An accepted copy holds what was vetted, at another point.** The section
    of an accepted copy at its first document version is the content of the
    revision it copies, a document (section 9.6). -/
    theorem acceptedCopy_value (l : LineId) (g : Genesis D) (src : Pin D) (v : Version D)
        (psigs ss : List (Sig D)) (d c m : String) (hm : v.members = none)
        (hx : Covers (acceptedCopy l g src v psigs ss d c m) 1 ⟨.line l, 1⟩) :
        objSec (acceptedCopy l g src v psigs ss d c m) 1 ⟨.line l, 1⟩ hx = v.content := by
      simp [objSec, docContent, acceptedCopy, branchVersion, Version.content, hm]

With the previous theorem, the copy and the original agree through the pin
of the branch point. The two values are equal, at two different points:
the copy's own name, and the revision's name. So an accepted copy is not a
second section over the same set, as a mirror is: the theorem is an
equality of the values at two different points of the base. Section 9.3
asks the verifier to check it: "every file of the head state of
`parent.inventory.json` ... is present at the same logical path with the
same digest".

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

For any branch of a world built by events, the files agree; the member
list is not checked by section 9.3, and the model does not check it either.

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
