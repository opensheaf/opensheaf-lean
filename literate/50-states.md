# Draft, private and public

This chapter models a **proposal**, not the specification: the three states
discussed in
[issue #29](https://github.com/opensheaf/opensheaf.github.io/issues/29).
It lives in a namespace of its own, `OpenSheaf.States`, and nothing else in
the model depends on it.

The proposal:

- an object version may be a **draft** (`"draft": true` in `object.json`).
  Drafts form a tail of the history, and may be rewritten until they are
  sealed or sent;
- a sealed version is **private** until its archive serves the object, and
  then **public**: an archive may serve only part of its objects;
- a version may pin only versions **at least as fixed** as itself, in the
  order draft < private < public. A public version pins only public
  versions, a private one private or public ones, a draft anything.

Rewriting drafts breaks immutability, which [chapter 3](30-archive.md)
proved only for steps that add versions. The point of the rule is to
confine the damage to drafts. The chapter proves that it does: rewriting
drafts never changes what a pin held by a sealed version resolves to, in any
archive (`sealed_pins_survive`). It also proves that publishing an object
keeps the rule, provided the object's sealed versions pin only public
versions (`publish_fixed`).

    -- in OpenSheaf/States.lean:
    import OpenSheaf.Archive

    namespace OpenSheaf.States

    open OpenSheaf

## Fixity

The three states, ordered by a rank.

    /-- How fixed a version is. -/
    inductive Fixity
      | draft
      | priv
      | pub
      deriving DecidableEq, Repr

    /-- The order draft < private < public. -/
    def Fixity.rank : Fixity → Nat
      | .draft => 0
      | .priv => 1
      | .pub => 2

Whether an archive serves an object is not part of the object: it is a
choice of the archive, which can change. The model records it as a
function, and the draft marker as a predicate on versions, both left as
parameters (the specification has neither yet).

    /-- Which objects each archive serves. -/
    abbrev Serving := ArchiveId → ObjectId → Bool

    variable {D : Type} (isDraft : Version D → Bool)

    /-- The fixity of a version of object `oid` of archive `a`. -/
    def fixity (served : Serving) (a : ArchiveId) (oid : ObjectId) (v : Version D) : Fixity :=
      if isDraft v then .draft else if served a oid then .pub else .priv

Three facts about ranks: they are at most 2; they are positive exactly for
sealed versions; and serving more objects only raises them.

    theorem rank_le_two (served : Serving) (a : ArchiveId) (oid : ObjectId) (v : Version D) :
        (fixity isDraft served a oid v).rank ≤ 2 := by
      unfold fixity
      split
      · simp [Fixity.rank]
      · split <;> simp [Fixity.rank]

    theorem rank_pos_iff (served : Serving) (a : ArchiveId) (oid : ObjectId) (v : Version D) :
        1 ≤ (fixity isDraft served a oid v).rank ↔ isDraft v = false := by
      unfold fixity
      cases h : isDraft v
      · simp only [Bool.false_eq_true, ite_false]
        split <;> simp [Fixity.rank]
      · simp [Fixity.rank]

    /-- Serving more objects makes versions only more fixed. -/
    theorem rank_mono {served served' : Serving}
        (hs : ∀ b x, served b x = true → served' b x = true)
        (a : ArchiveId) (oid : ObjectId) (v : Version D) :
        (fixity isDraft served a oid v).rank ≤ (fixity isDraft served' a oid v).rank := by
      unfold fixity
      cases isDraft v
      · cases h : served a oid
        · cases served' a oid <;> simp [Fixity.rank]
        · simp [hs a oid h, Fixity.rank]
      · simp [Fixity.rank]

## Drafts as a tail

Drafts come after every sealed version: a history is a sealed prefix
followed by drafts.

    /-- Drafts form a tail of the history. -/
    def DraftTail (vs : List (Version D)) : Prop :=
      ∃ sealed drafts, vs = sealed ++ drafts ∧
        (∀ v ∈ sealed, isDraft v = false) ∧ (∀ v ∈ drafts, isDraft v = true)

Rewriting drafts replaces the tail by new versions: revised drafts, or the
same versions sealed. The sealed prefix stays.

    section Rewrite

    variable [DecidableEq D] (hash : Hash D)

    /-- Replace the drafts of an object (the tail after `sealed`) by new versions:
    drafts revised, or sealed. -/
    def rewriteDrafts (w : World D) (a : ArchiveId) (oid : ObjectId) (o : Obj D)
        (sealed newTail : List (Version D)) : World D :=
      setEntry w a oid (.live { o with versions := sealed ++ newTail })

A pin that resolved to a sealed version still resolves to it. The pinned
version is not a draft, so it lies in the sealed prefix (otherwise it would
be among the drafts), and the prefix lemma of [chapter 3](30-archive.md)
applies.

    /-- Rewriting drafts does not change what a pin of a sealed version resolves
    to. -/
    theorem rewrite_keeps_sealed {w : World D} {a : ArchiveId} {oid : ObjectId} {o : Obj D}
        {sealed drafts newTail : List (Version D)}
        (hl : lookup w a oid = some (.live o)) (hv : o.versions = sealed ++ drafts)
        (hd : ∀ v ∈ drafts, isDraft v = true) {p : Pin D} {t : Version D}
        (hp : resolve hash w p = .ok t) (ht : isDraft t = false) :
        resolve hash (rewriteDrafts w a oid o sealed newTail) p = .ok t := by
      obtain ⟨ar, ha⟩ := lookup_some_archive hl
      unfold resolve rewriteDrafts at *
      rw [lookup_setEntry ha]
      split
      · rename_i hc
        obtain ⟨h1, h2⟩ := hc
        rw [h1, h2, hl] at hp
        obtain ⟨hvat, _⟩ := resolveEntry_live_ok hash hp
        have hn : p.version ≤ sealed.length := by
          obtain ⟨hpos, _⟩ := Obj.versionAt_bounds hvat
          refine Nat.le_of_not_lt fun hlt => ?_
          unfold Obj.versionAt at hvat
          have hne : p.version ≠ 0 := by omega
          simp only [hne, ite_false] at hvat
          rw [hv, List.getElem?_append_right (by omega)] at hvat
          have := hd t (List.mem_of_getElem? hvat)
          rw [ht] at this
          contradiction
        exact resolveEntry_prefix hash hv rfl hn hp
      · exact hp

## The rule

The rule of the proposal, for every version of every live object, and every
pin it holds that resolves:

    /-- Versions pin only versions at least as fixed as themselves. -/
    def Fixed (w : World D) (served : Serving) : Prop :=
      ∀ a oid o, lookup w a oid = some (.live o) →
        ∀ v ∈ o.versions, ∀ p ∈ v.pins, ∀ t, resolve hash w p = .ok t →
          (fixity isDraft served a oid v).rank ≤
            (fixity isDraft served p.archive p.object t).rank

Its first consequence: a sealed version pins only sealed versions, since a
positive rank can only be below a positive rank.

    /-- Under the rule, a sealed version pins only sealed versions. -/
    theorem Fixed.target_sealed {w : World D} {served : Serving} (hF : Fixed isDraft hash w served)
        {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
        {v : Version D} (hv : v ∈ o.versions) (hs : isDraft v = false)
        {p : Pin D} (hp : p ∈ v.pins) {t : Version D} (hr : resolve hash w p = .ok t) :
        isDraft t = false := by
      have h := hF a oid o hl v hv p hp t hr
      have h1 := (rank_pos_iff isDraft served a oid v).mpr hs
      exact (rank_pos_iff isDraft served p.archive p.object t).mp (by omega)

And the theorem the proposal is for. Under the rule, rewriting the drafts of
any object leaves every pin held by any sealed version, of any object of any
archive, resolving as before. Authors may revise their drafts freely: no
sealed record, theirs or anyone else's, can depend on them.

    /-- **Drafts are safe to rewrite.** Under the rule, rewriting the drafts of an
    object never changes what a pin held by a sealed version resolves to. -/
    theorem sealed_pins_survive {w : World D} {served : Serving}
        (hF : Fixed isDraft hash w served)
        {a : ArchiveId} {oid : ObjectId} {o : Obj D} {sealed drafts newTail : List (Version D)}
        (hl : lookup w a oid = some (.live o)) (hv : o.versions = sealed ++ drafts)
        (hd : ∀ v ∈ drafts, isDraft v = true)
        {b : ArchiveId} {x : ObjectId} {o' : Obj D} (hl' : lookup w b x = some (.live o'))
        {v : Version D} (hv' : v ∈ o'.versions) (hs : isDraft v = false)
        {p : Pin D} (hp : p ∈ v.pins) {t : Version D} (hr : resolve hash w p = .ok t) :
        resolve hash (rewriteDrafts w a oid o sealed newTail) p = .ok t :=
      rewrite_keeps_sealed isDraft hash hl hv hd hr (hF.target_sealed isDraft hash hl' hv' hs hp hr)

What is not proved yet: that rewriting keeps the rule itself. A pin held by
a draft that did not resolve before the rewrite (it named a version that
did not exist yet) might resolve after it, to a new version whose fixity
the rule does not control. Excluding that needs the digest of the new
inventory to differ from the digest in the pin: collision resistance, the
first place where the model will need a hypothesis on `hash`.

## Publication

Publishing an object makes the archive serve it.

    /-- Serve one more object. -/
    def publish (served : Serving) (a : ArchiveId) (oid : ObjectId) : Serving :=
      fun b x => if b = a ∧ x = oid then true else served b x

    theorem publish_mono (served : Serving) (a : ArchiveId) (oid : ObjectId) (b : ArchiveId)
        (x : ObjectId) (h : served b x = true) : publish served a oid b x = true := by
      unfold publish; split <;> simp_all

Publication raises the sealed versions of the object from private to public,
so the rule can fail only for the pins they hold: each must then name a
public version. That is the hypothesis `hpre`, and it is enough. Pins held
by other objects are not at risk, since publication only raises the rank of
their targets.

    /-- **Publication keeps the rule**, when the sealed versions of the object
    published pin only public versions. -/
    theorem publish_fixed {w : World D} {served : Serving} (hF : Fixed isDraft hash w served)
        {a : ArchiveId} {oid : ObjectId} {o : Obj D} (hl : lookup w a oid = some (.live o))
        (hpre : ∀ v ∈ o.versions, isDraft v = false → ∀ p ∈ v.pins, ∀ t,
          resolve hash w p = .ok t → served p.archive p.object = true ∧ isDraft t = false) :
        Fixed isDraft hash w (publish served a oid) := by
      intro b x o' hl' v hv p hp t hr
      have hmono := rank_mono isDraft (publish_mono served a oid)
      by_cases hc : b = a ∧ x = oid
      · obtain ⟨rfl, rfl⟩ := hc
        rw [hl] at hl'
        cases hl'
        cases hdv : isDraft v
        · obtain ⟨hsrv, htd⟩ := hpre v hv hdv p hp t hr
          have h2 : (fixity isDraft (publish served b x) p.archive p.object t).rank = 2 := by
            simp [fixity, htd, publish_mono served b x _ _ hsrv, Fixity.rank]
          have := rank_le_two isDraft (publish served b x) b x v
          omega
        · simp [fixity, hdv, Fixity.rank]
      · have hsame : fixity isDraft (publish served a oid) b x v = fixity isDraft served b x v := by
          simp [fixity, publish, hc]
        have := hF b x o' hl' v hv p hp t hr
        have := hmono p.archive p.object t
        rw [hsame]
        omega

    end Rewrite

    end OpenSheaf.States
