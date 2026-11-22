# Copies, mirrors and branches

A line is "its signed versions, wherever they are stored" (section 7): the
same line may be kept by several archives, each holding a **copy**, and a
copy kept where the owner does not write is a **mirror** (section 11). A
**branch** is another owner's line that continues the work from a signed
version of the first, its branch point (section 9); an **accepted copy**
is a branch kept by the owner of a selection, from a revision it vetted
(section 9.6). Integrity comes from pins and signatures, not places: "any
copy whose bytes match the pin will do" (section 8.5).

This chapter proves that copies and branches behave as the specification
says:

- any two copies of a line, wherever they are kept, are prefixes of one
  another, as long as the owner's keys sign one history
  (`Events.copiesAgree`); and when they are not, the owner's keys signed
  both sides (`Events.fork_signed`), "a fork whose sides are both signed was
  made with keys of the owner" (section 7.4);
- so a pin resolves to the same version at every hint, and keeps resolving
  to it (`Steps.resolve_ok`);
- any copy, trusted or not, resolves a pin only to the version pinned,
  unless the digests collide (`copy_authentic`, `resolve_sound`), and a
  copy at a later hint stands in for the hints before it
  (`resolve_stand_in`);
- a branch holds its parent's files, as a verifier checks (section 9.3),
  in every world built by events, unless inventories collide
  (`Events.branch_files`); an accepted copy survives a takedown of the
  parent, and is never taken for it (`acceptedCopy_survives`,
  `branch_not_copy`).

    -- in OpenSheaf/Copies.lean:
    import OpenSheaf.Acts

    namespace OpenSheaf

    variable {D : Type} [DecidableEq D] (E : Env D)

## Collisions

The statements about copies that come from anywhere need a hypothesis on
the digest: only the digest ties a copy to the version pinned. The tempting
hypothesis, that `hash` is injective, cannot hold for a real digest: there
are infinitely many inventories and only finitely many SHA-512 digests, so
some inventories share a digest. What cryptography offers is that nobody
can *find* two such inventories. The model therefore assumes, each time,
only that the two inventories being compared do not collide: if their
digests are equal, so are they. This is the hypothesis a reader relies on
when they accept a copy because its digest matches.

    /-- The inventories `i` and `j` do not collide. -/
    def NoCollision (i j : Inventory D) : Prop := E.hash i = E.hash j → i = j

## One history

Section 7.4: "An owner MUST NOT sign two different object versions with the
same number for the same line". An owner that keeps the rule, and whose
current keys nobody else holds, signs **one history**: there is a list of
versions of which every version it signs is a prefix. The model states it
as a hypothesis on the signatures that verify, `SignsHistory`: every
signature of the line that verifies and is the owner's signs the digest of
a prefix of one history `H`.

A signature names a digest, not an inventory, so a copy whose head the
owner signed is a prefix of `H` only if its inventory does not collide with
the prefix of `H` of the same length. The second hypothesis,
`NoCollisionWith`, says so, for the copies a world holds and for no other
inventory: it is the hypothesis of `copy_authentic` below, made of the
inventories the world holds and the history the owner signed. Together they
are `OneHistory`. Neither assumes that the digest function is injective on
anything but these pairs, so both can hold of SHA-512, and they can hold
of a line in the toy worlds of the stories too. The signatures that count
are those made with keys of versions of the owner's key log that the world
holds (`OwnerKey`, [chapter 8](47-acts.md)): nothing is assumed of key
logs that could be written but are held nowhere.

    /-- One list is a prefix of the other. -/
    def Comparable {α : Type} (l l' : List α) : Prop :=
      (∃ t, l' = l ++ t) ∨ (∃ t, l = l' ++ t)

    theorem Comparable.symm {α : Type} {l l' : List α} (h : Comparable l l') : Comparable l' l :=
      h.elim Or.inr Or.inl

    theorem comparable_of_prefixes {α : Type} {l1 l2 t1 t2 L : List α} (h1 : L = l1 ++ t1)
        (h2 : L = l2 ++ t2) : Comparable l1 l2 := by
      rcases List.append_eq_append_iff.mp (h1.symm.trans h2) with ⟨a, ha, _⟩ | ⟨c, hc, _⟩
      · exact Or.inl ⟨a, ha⟩
      · exact Or.inr ⟨c, hc⟩

    /-- The inventory of the first `n` versions of the history `H` of line `l`,
    whose genesis record is `g`. -/
    def histInv (l : LineId) (g : Option (Genesis D)) (H : List (Version D)) (n : Nat) :
        Inventory D :=
      ⟨.line l, g, H.take n⟩

    /-- **The owner of `l` signs one history** `H`: every signature of `l` that
    verifies and is the owner's signs the digest of a prefix of `H`. -/
    def SignsHistory (w : World D) (l : LineId) (g : Option (Genesis D)) (H : List (Version D)) :
        Prop :=
      ∀ s, E.verifies s = true → s.line = l → OwnerKey E w l.owner s →
        s.version ≤ H.length ∧ s.digest = E.hash (histInv l g H s.version)

    /-- No inventory of a copy of `l` held in `w` collides with the prefix of `H` of
    the same length. -/
    def NoCollisionWith (w : World D) (l : LineId) (g : Option (Genesis D)) (H : List (Version D)) :
        Prop :=
      ∀ b o, lookup w b (.line l) = some (.live o) → o.kind ≠ .owner →
        ∀ n, n ≤ o.versions.length → NoCollision E (o.inventory n) (histInv l g H n)

    /-- In the world `w`, the owner of `l` signs one history, which no copy held
    collides with. -/
    def OneHistory (w : World D) (l : LineId) : Prop :=
      ∃ g H, SignsHistory E w l g H ∧ NoCollisionWith E w l g H

The head of every copy is signed by its owner (`Events.headsSigned`,
[chapter 8](47-acts.md)), and its inventory is the whole copy. Under the
hypotheses, the copy is therefore a prefix of the owner's history.

    /-- Any two copies of the line `l`, wherever they are kept, are prefixes of one
    another (key logs apart). -/
    def CopiesAgree (w : World D) (l : LineId) : Prop :=
      ∀ b b' o o', lookup w b (.line l) = some (.live o) → lookup w b' (.line l) = some (.live o') →
        o.kind ≠ .owner → o'.kind ≠ .owner → Comparable o.versions o'.versions

    theorem Events.prefix_history {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {l : LineId}
        {g : Option (Genesis D)} {H : List (Version D)} (hsh : SignsHistory E w l g H)
        (hnc : NoCollisionWith E w l g H) {b : ArchiveId} {o : Obj D}
        (hl : lookup w b (.line l) = some (.live o)) (hk : o.kind ≠ .owner) :
        o.versions.length ≤ H.length ∧ o.versions = H.take o.versions.length := by
      obtain ⟨s, _, hver, hsg, hown⟩ := Events.headsSigned E hs hl hk
      obtain ⟨hle, hd⟩ := hsh s hver hsg.1 hown
      rw [hsg.2.1] at hle hd
      have heq := hnc b o hl hk _ (Nat.le_refl _) (hsg.2.2.1.symm.trans hd)
      refine ⟨hle, ?_⟩
      have := congrArg Inventory.versions heq
      simpa [Obj.inventory, histInv] using this

A copy that is a prefix of the owner's history holds its genesis record
too: the inventory compared names it.

    theorem Events.genesis_history {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {l : LineId}
        {g : Option (Genesis D)} {H : List (Version D)} (hsh : SignsHistory E w l g H)
        (hnc : NoCollisionWith E w l g H) {b : ArchiveId} {o : Obj D}
        (hl : lookup w b (.line l) = some (.live o)) (hk : o.kind ≠ .owner) : o.genesis = g := by
      obtain ⟨s, _, hver, hsg, hown⟩ := Events.headsSigned E hs hl hk
      obtain ⟨_, hd⟩ := hsh s hver hsg.1 hown
      rw [hsg.2.1] at hd
      have heq := hnc b o hl hk _ (Nat.le_refl _) (hsg.2.2.1.symm.trans hd)
      exact congrArg Inventory.genesis heq

    /-- **Copies agree**, in every world built by events, takedowns included, when
    the owner signs one history. -/
    theorem Events.copiesAgree {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {l : LineId}
        (h1 : OneHistory E w l) : CopiesAgree w l := by
      intro b b' o o' hl hl' hk hk'
      obtain ⟨g, H, hsh, hnc⟩ := h1
      obtain ⟨_, h⟩ := Events.prefix_history E hs hsh hnc hl hk
      obtain ⟨_, h'⟩ := Events.prefix_history E hs hsh hnc hl' hk'
      have e1 := List.take_append_drop o.versions.length H
      have e2 := List.take_append_drop o'.versions.length H
      rw [← h] at e1; rw [← h'] at e2
      exact comparable_of_prefixes e1.symm e2.symm

The hypothesis holds of an earlier world when it holds of a later one
reached by steps: the copies of the earlier world are prefixes of copies of
the later one, and their inventories are the same.

    omit [DecidableEq D] in
    theorem NoCollisionWith.back {w w' : World D} (hs : Steps w w') {l : LineId}
        {g : Option (Genesis D)} {H : List (Version D)} (hnc : NoCollisionWith E w' l g H) :
        NoCollisionWith E w l g H := by
      intro b o hl hk n hn
      obtain ⟨o', hl', hg⟩ := Steps.live_grows hs hl
      obtain ⟨t, ht⟩ := hg.versions
      have hk' : o'.kind ≠ .owner := by rw [hg.kind]; exact hk
      have hn' : n ≤ o'.versions.length := by rw [ht]; simp; omega
      have hinv : o'.inventory n = o.inventory n :=
        inventory_prefix (t := []) ⟨hg.id, hg.genesis⟩ (by simp) ht hn
      rw [← hinv]
      exact hnc b o' hl' hk' n hn'

    omit [DecidableEq D] in
    theorem SignsHistory.back {w w' : World D} (hs : Steps w w') {l : LineId}
        {g : Option (Genesis D)} {H : List (Version D)} (h : SignsHistory E w' l g H) :
        SignsHistory E w l g H :=
      fun s hv hl ho => h s hv hl (ho.steps E hs)

    omit [DecidableEq D] in
    theorem OneHistory.back {w w' : World D} (hs : Steps w w') {l : LineId}
        (h : OneHistory E w' l) : OneHistory E w l := by
      obtain ⟨g, H, hsh, hnc⟩ := h
      exact ⟨g, H, hsh.back E hs, hnc.back E hs⟩

Without the hypothesis, copies may fork, and section 7.4 says what that
means: "a fork whose sides are both signed was made with keys of the
owner". In the model the heads of both copies are signed with current keys
of versions of the owner's key log that the world holds (`OwnerKey`,
[chapter 8](47-acts.md)): the owner's keys, or those of whoever extended
its key log with its rotation keys, which the key log then shows, unless
names collide (`Events.ownerKey_origin`). And the hypothesis fails: those
keys signed no single history of the line that the copies do not collide
with. The fork is the keys' doing, not the archives'.

    /-- **A fork of a line was signed with keys of its owner's key log**, which
    then sign no one history. -/
    theorem Events.fork_signed {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {l : LineId}
        {b b' : ArchiveId} {o o' : Obj D} (hl : lookup w b (.line l) = some (.live o))
        (hl' : lookup w b' (.line l) = some (.live o')) (hk : o.kind ≠ .owner)
        (hk' : o'.kind ≠ .owner) (hfork : ¬ Comparable o.versions o'.versions) :
        HeadSigned E w l o ∧ HeadSigned E w l o' ∧ ¬ OneHistory E w l :=
      ⟨Events.headsSigned E hs hl hk, Events.headsSigned E hs hl' hk',
        fun h1 => hfork (Events.copiesAgree E hs h1 b b' o o' hl hl' hk hk')⟩

## A pin means one version, wherever it is found

Two copies that agree give the same version for every pin they both
resolve: the version at the pinned number is the same in both, whatever the
digest. So in a world where copies agree, resolution through the hints
does not depend on which hint answers.

    omit [DecidableEq D] in
    theorem Comparable.versionAt {o o' : Obj D} (h : Comparable o.versions o'.versions) {n : Nat}
        {u v : Version D} (hu : o.versionAt n = some u) (hv : o'.versionAt n = some v) : u = v := by
      rcases h with ⟨t, ht⟩ | ⟨t, ht⟩
      · have := versionAt_prefix (o := o) (o' := o') (t := []) (by simp) ht
          (Obj.versionAt_bounds hu).2 hu
        rw [hv] at this; exact (Option.some.inj this).symm
      · have := versionAt_prefix (o := o') (o' := o) (t := []) (by simp) ht
          (Obj.versionAt_bounds hv).2 hv
        rw [hu] at this; exact Option.some.inj this

    theorem agree_resolveAt {w : World D} {l : LineId} (hagree : CopiesAgree w l)
        {b b' : ArchiveId} {p : Pin D} (hp : p.line = l) {u v : Version D}
        (hk : ∀ c c', lookup w b (.line l) = some (.live c) → lookup w b' (.line l) = some (.live c') →
          c.kind ≠ .owner ∧ c'.kind ≠ .owner)
        (hu : resolveAt E.hash w b p = .ok u) (hv : resolveAt E.hash w b' p = .ok v) : u = v := by
      unfold resolveAt at hu hv
      rw [hp] at hu hv
      obtain ⟨c, hc⟩ := resolveEntry_ok_live E.hash hu
      obtain ⟨c', hc'⟩ := resolveEntry_ok_live E.hash hv
      rw [hc] at hu; rw [hc'] at hv
      obtain ⟨hk1, hk2⟩ := hk c c' hc hc'
      exact (hagree b b' c c' hc hc' hk1 hk2).versionAt (resolveEntry_live_ok E.hash hu).1
        (resolveEntry_live_ok E.hash hv).1

In a world built by events, a copy of kind `owner` is a key log, at the
line `(X, X)` of its owner (`KeyLogOk`, [chapter 4](35-owners.md)); a line
that is not of that form has documents and collections for copies.

    theorem Events.keyLog_line {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {b : ArchiveId} {l : LineId}
        {o : Obj D} (hl : lookup w b (.line l) = some (.live o)) (hk : o.kind = .owner) :
        l = keyLogLine l.owner := by
      obtain ⟨_, _, hp⟩ := (Events.keyLogsOk E hs hl hk).parts
      have hid := hp.id
      have := ((Events.sound E hs).1 _ _ _ hl).id
      rw [this] at hid
      exact ObjectId.line.inj hid

A line that is not a key log, and whose owner signs one history, therefore
keeps the meaning of every pin of it, through hints and steps alike: what a
pin resolved to, it resolves to after any number of steps, whichever hint
answers.

    /-- **A pin keeps its meaning, at every hint.** -/
    theorem Steps.resolve_ok {w w' : World D}
        (hw' : Events E (fun _ => (none : Option (Archive D))) w') (hs : Steps w w') {p : Pin D}
        (h1 : OneHistory E w' p.line) (hnk : p.line ≠ keyLogLine p.line.owner)
        {v : Version D} (h : resolve E.hash w p = .ok v) : resolve E.hash w' p = .ok v := by
      have hk : ∀ b c, lookup w' b (.line p.line) = some (.live c) → c.kind ≠ .owner :=
        fun b c hc hko => hnk (Events.keyLog_line E hw' hc hko)
      obtain ⟨b, hb, hbv⟩ := resolve_ok_at E.hash h
      have hbv' := Steps.resolveAt_ok E.hash hs hbv
      obtain ⟨u, hu⟩ := resolve_ok_of_at E.hash hb hbv'
      obtain ⟨b', _, hbu⟩ := resolve_ok_at E.hash hu
      have := agree_resolveAt E (Events.copiesAgree E hw' h1) rfl
        (fun c c' hc hc' => ⟨hk _ _ hc, hk _ _ hc'⟩) hbu hbv'
      rw [hu, this]

## Any copy, from anywhere

A reader who fetches a copy from an archive they do not trust, or from a
disk found in a drawer, has no reason to believe that it is a faithful
copy. The pin is enough, unless the copy's inventory collides with the
inventory pinned: if the copy resolves the pin at all, it resolves it to
the version pinned. This is the use of SHA-512 in the specification.

    /-- **A pin authenticates any copy**, unless the inventories collide. -/
    theorem copy_authentic {o c : Obj D} {p : Pin D} {v u : Version D}
        (hcol : NoCollision E (c.inventory p.version) (o.inventory p.version))
        (ho : resolveEntry E.hash (some (.live o)) p = .ok v)
        (hc : resolveEntry E.hash (some (.live c)) p = .ok u) : u = v := by
      obtain ⟨hvo, hdo⟩ := resolveEntry_live_ok E.hash ho
      obtain ⟨hvc, hdc⟩ := resolveEntry_live_ok E.hash hc
      have heq : c.inventory p.version = o.inventory p.version := hcol (hdc.trans hdo.symm)
      rw [versionAt_congr_take (congrArg Inventory.versions heq), hvo] at hvc
      cases hvc
      rfl

## Resolution through the hints

Section 12.3: a resolver tries the locations it has, and "a copy that
passes is a copy of the line, wherever found". The model's resolution
takes the first version found among the hints ([chapter 3](30-archive.md)).
When the hints before it give no version (the archive is gone, the line is
lost or altered there), a copy at a later hint gives the answer.

    omit [DecidableEq D] in
    theorem pick_append_ok {pre post : List (Resolution D)} {v : Version D}
        (hpre : ∀ r ∈ pre, ∀ u, r ≠ .ok u) : pick (pre ++ .ok v :: post) = .ok v := by
      induction pre with
      | nil =>
        show (if (pick post).rank ≤ (Resolution.ok v).rank then Resolution.ok v else pick post) = .ok v
        have : (pick post).rank ≤ (Resolution.ok v : Resolution D).rank := by
          cases pick post <;> simp [Resolution.rank]
        rw [if_yes this]
      | cons r pre ih =>
        simp only [List.cons_append, pick]
        rw [ih fun r' hr' u => hpre r' (List.mem_cons_of_mem _ hr') u]
        have hr : r.rank < 3 := by
          cases r with
          | ok u => exact absurd rfl (hpre _ (List.mem_cons_self ..) u)
          | _ => simp [Resolution.rank]
        have : ¬ (Resolution.ok v : Resolution D).rank ≤ r.rank := by
          show ¬ 3 ≤ r.rank; omega
        rw [if_no this]

    /-- **A copy at a later hint stands in** for the hints before it, when they give
    no version. -/
    theorem resolve_stand_in {w : World D} {p : Pin D} {pre post : List ArchiveId}
        {b : ArchiveId} (hh : p.hints = pre ++ b :: post) {v : Version D}
        (hbefore : ∀ b' ∈ pre, ∀ u, resolveAt E.hash w b' p ≠ .ok u)
        (hb : resolveAt E.hash w b p = .ok v) : resolve E.hash w p = .ok v := by
      unfold resolve
      rw [hh, List.map_append, List.map_cons, hb]
      apply pick_append_ok
      intro r hr u
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hr
      exact hbefore b' hb' u

Whatever copy answers, the answer is right: a version found through the
hints is the version pinned, unless a copy consulted collides with it.

    /-- **Resolution through the hints is sound**: what it finds is the version
    pinned, whoever holds the copy, unless a copy consulted collides. -/
    theorem resolve_sound {w : World D} {p : Pin D} {o : Obj D} {u v : Version D}
        (hcol : ∀ b ∈ p.hints, ∀ c, lookup w b (.line p.line) = some (.live c) →
          NoCollision E (c.inventory p.version) (o.inventory p.version))
        (ho : resolveEntry E.hash (some (.live o)) p = .ok v)
        (h : resolve E.hash w p = .ok u) : u = v := by
      obtain ⟨b, hb, hbu⟩ := resolve_ok_at E.hash h
      unfold resolveAt at hbu
      obtain ⟨c, hc⟩ := resolveEntry_ok_live E.hash hbu
      rw [hc] at hbu
      exact copy_authentic E (hcol b hb c hc) ho hbu

## Branches hold their parents' files

A branch point is checked when it is set, against the parent version found
at a hint ([chapter 7](45-worlds.md)). What the check found stays true,
whatever happens to that copy later, if the model states it without the
world: the pin fixes an inventory of the parent's line, whose last version
holds the branch's files.

    /-- `u` is the version a pin fixes: the last version of an inventory of the
    pin's line, of the pinned number, with the pin's digest. -/
    def PinnedVersion (p : Pin D) (u : Version D) : Prop :=
      ∃ i : Inventory D, i.id = .line p.line ∧ E.hash i = p.digest ∧
        i.versions.length = p.version ∧ i.versions.getLast? = some u

    theorem pinnedVersion_of_resolveAt {w : World D} (hw : SoundWorld E w) {b : ArchiveId}
        {p : Pin D} {u : Version D} (h : resolveAt E.hash w b p = .ok u) : PinnedVersion E p u := by
      unfold resolveAt at h
      obtain ⟨c, hc⟩ := resolveEntry_ok_live E.hash h
      rw [hc] at h
      obtain ⟨hv, hd⟩ := resolveEntry_live_ok E.hash h
      have hid : c.id = .line p.line := (hw.1 _ _ _ hc).id
      obtain ⟨h1, h2⟩ := Obj.versionAt_bounds hv
      exact ⟨c.inventory p.version, hid, hd, by simp [Obj.inventory]; omega, getLast?_take hv⟩

    /-- A version that sets a new branch point holds the files of the parent
    version that the pin fixes, and its document version (sections 9.2 and 9.4). -/
    def BranchOk (prev : Option (Parent D)) (x : Version D) : Prop :=
      ∀ pa, x.parent = some pa → ¬ Parent.Keeps prev pa →
        ∃ u, PinnedVersion E pa.pin u ∧ x.files = u.files ∧ u.documentVersion = pa.documentVersion

    /-- Every version of every object that sets a new branch point holds its
    parent's files. -/
    def BranchesOk (w : World D) : Prop :=
      ∀ b x o, lookup w b x = some (.live o) →
        ∀ i (h : i < o.versions.length), BranchOk E (prevParent o.versions i) o.versions[i]

The check of a valid step gives it, in a sound world.

    theorem branchPointOk_ok {w : World D} (hw : SoundWorld E w) {prev : Option (Parent D)}
        {x : Version D} (h : BranchPointOk E w prev x) : BranchOk E prev x := by
      intro pa hpa hne
      unfold BranchPointOk at h
      rw [hpa] at h
      rcases h with h | ⟨_, b, _, u, hu, hf, hdv, _⟩
      · exact absurd h hne
      · exact ⟨u, pinnedVersion_of_resolveAt E hw hu, hf, hdv⟩

The branch point before a version depends only on the versions before it.

    omit [DecidableEq D] in
    theorem prevParent_append {l t : List (Version D)} {i : Nat} (hi : i ≤ l.length) :
        prevParent (l ++ t) i = prevParent l i := by
      cases i with
      | zero => rfl
      | succ j => simp only [prevParent, List.getElem?_append_left (show j < l.length by omega)]

    omit [DecidableEq D] in
    theorem prevParent_last (l : List (Version D)) :
        prevParent l l.length = l.getLast?.bind (·.parent) := by
      cases h : l.length with
      | zero => simp [List.length_eq_zero_iff.mp h, prevParent]
      | succ j => simp [prevParent, List.getLast?_eq_getElem?, h]

A copy holds the versions of the copy it copies, at the same numbers.

    omit [DecidableEq D] in
    theorem branchesOk_prefix {o c : Obj D} {t : List (Version D)} (ht : c.versions = o.versions ++ t)
        (hc : ∀ i (h : i < c.versions.length), BranchOk E (prevParent c.versions i) c.versions[i]) :
        ∀ i (h : i < o.versions.length), BranchOk E (prevParent o.versions i) o.versions[i] := by
      intro i hi
      have hic : i < c.versions.length := by rw [ht]; simp; omega
      have := hc i hic
      have h1 : c.versions[i] = o.versions[i] := by simp [ht, List.getElem_append_left hi]
      rw [h1, ht, prevParent_append (by omega)] at this
      exact this

    theorem ValidStep.branchesOk {w w' : World D} (hs : ValidStep E w w') (hsound : SoundWorld E w)
        (hw : BranchesOk E w) : BranchesOk E w' := by
      intro b x o' hl
      cases hs with
      | newArchive a ar ha hempty =>
        rw [lookup_newArchive ha hempty] at hl; exact hw b x o' hl
      | create a ar oid o ha ho hwf _ hbranch =>
        rw [lookup_setEntry ha] at hl
        split at hl
        · injection hl with hl; injection hl with hl; subst hl
          by_cases hcopy : CopyOf w a o
          · obtain ⟨b', c, _, hc, _, t, ht⟩ := hcopy
            exact branchesOk_prefix E ht (hw b' _ c hc)
          · exact fun i hi => branchPointOk_ok E hsound (hbranch hcopy i hi)
        · exact hw b x o' hl
      | append a ar oid o y ss ha ho _ _ _ _ _ hbranch =>
        rw [lookup_setEntry ha] at hl
        split at hl
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases hl
          by_cases hcopy : CopyOf w b (o.append y ss)
          · obtain ⟨b', c, _, hc, _, t, ht⟩ := hcopy
            exact branchesOk_prefix E ht (hw b' _ c hc)
          · have hlo : lookup w b x = some (.live o) := by simp [lookup, ha, ho]
            intro i hi
            have hi2 : i < o.versions.length + 1 := by simpa [Obj.append] using hi
            by_cases hlt : i < o.versions.length
            · have := hw b x o hlo i hlt
              rw [append_getElem_old hlt]
              show BranchOk E (prevParent (o.versions ++ [y]) i) _
              rw [prevParent_append (by omega)]
              exact this
            · have hi' : i = o.versions.length := by omega
              subst hi'
              rw [append_getElem_last]
              show BranchOk E (prevParent (o.versions ++ [y]) o.versions.length) _
              rw [prevParent_append (Nat.le_refl _), prevParent_last]
              exact branchPointOk_ok E hsound (hbranch hcopy)
        · exact hw b x o' hl
      | witness a ar oid o ss ha ho =>
        rw [lookup_setEntry ha] at hl
        split at hl
        · rename_i hc
          obtain ⟨rfl, rfl⟩ := hc
          cases hl
          exact hw b x o (by simp [lookup, ha, ho])
        · exact hw b x o' hl

    theorem Event.branchesOk {w w' : World D} (he : Event E w w')
        (hw : SoundWorld E w ∧ BranchesOk E w) : SoundWorld E w' ∧ BranchesOk E w' := by
      refine ⟨he.sound E hw.1, ?_⟩
      cases he with
      | step hs => exact hs.branchesOk E hw.1 hw.2
      | takedown a oid o _ hl =>
        exact fun b x o' h => hw.2 b x o' (lookup_takedown E.hash hl h).2

    theorem Events.branchesOk {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) : BranchesOk E w :=
      (hs.invariant _ (fun he hw => Event.branchesOk E he hw)
        ⟨SoundWorld.empty E, fun _ _ _ h => by simp [lookup] at h⟩).2

The check of section 9.3, "every file of the head state of
`parent/inventory.json` ... is present at the same logical path with the
same digest", holds then of every branch, in every world built by events,
whatever copy of the parent a verifier finds: there is an inventory of the
parent's line, with the pinned digest and number, whose last version holds
the branch's files (the one the branch point was checked against), and any
copy that resolves the pin holds the same version, unless its inventory
collides with that one.

    /-- **Every branch point holds its parent's files**, in every world built by
    events, unless the copy of the parent found collides with the inventory the
    branch point was checked against. -/
    theorem Events.branch_files {w : World D}
        (hs : Events E (fun _ => (none : Option (Archive D))) w) {b : ArchiveId} {x : ObjectId}
        {o : Obj D} (hl : lookup w b x = some (.live o)) {i : Nat} (hi : i < o.versions.length)
        {pa : Parent D} (hpa : o.versions[i].parent = some pa)
        (hnew : ¬ Parent.Keeps (prevParent o.versions i) pa) :
        ∃ j : Inventory D, E.hash j = pa.pin.digest ∧ j.id = .line pa.pin.line ∧
          j.versions.length = pa.pin.version ∧
          (∃ u', j.versions.getLast? = some u' ∧ o.versions[i].files = u'.files) ∧
          ∀ b' c u, lookup w b' (.line pa.pin.line) = some (.live c) →
            resolveAt E.hash w b' pa.pin = .ok u → NoCollision E (c.inventory pa.pin.version) j →
            o.versions[i].files = u.files := by
      obtain ⟨u', ⟨j, hjid, hj, hjlen, hlast⟩, hf, _⟩ := Events.branchesOk E hs b x o hl i hi pa hpa hnew
      refine ⟨j, hj, hjid, hjlen, ⟨u', hlast, hf⟩, fun b' c u hc hu hcol => ?_⟩
      unfold resolveAt at hu
      rw [hc] at hu
      obtain ⟨hv, hd⟩ := resolveEntry_live_ok E.hash hu
      have heq := hcol (hd.trans hj.symm)
      have hlast' : (c.versions.take pa.pin.version).getLast? = some u := getLast?_take hv
      have : (c.inventory pa.pin.version).versions = j.versions := congrArg Inventory.versions heq
      simp only [Obj.inventory] at this
      rw [this, hlast] at hlast'
      cases hlast'
      exact hf

## Accepted copies

An accepted copy is a branch of a selection's owner, the curator, made from
a revision it vetted (section 9.6): a new line `l`, of the curator, with the
genesis record of the work, whose first version holds the files of the
revision, records the revision's pin as its branch point, with the parent
owner's signatures as evidence (section 9.2), and is signed by the curator.
Its description, depositor and message are the curator's, given as
parameters; its document version is 1 (section 9.4, as [chapter
7](45-worlds.md) says).

It also keeps the references of the revision. This is a **modelling
choice** on issue #28: section 9.7 asks a branch to keep "the relations of
the parent version", which are DataCite relations; the references of the
model are those of the extension proposed in #28, which does not yet say
what branches do with them. Keeping them is the natural reading, since a
reference pins the same version whoever holds it.

    /-- The first version of a branch from the version `v`, pinned by `src`, with
    the parent's signatures `psigs` as evidence (section 9.2). -/
    def branchVersion (src : Pin D) (v : Version D) (psigs : List (Sig D))
        (description curator message : String) : Version D :=
      { documentVersion := 1, files := v.files, description, refs := v.refs,
        parent := some ⟨src, v.documentVersion, psigs⟩, depositor := curator, message }

    /-- The accepted copy of the revision `v`, pinned by `src`, as the line `l` of
    the curator, with the genesis record `g` and the curator's signatures `ss`
    (section 9.6). -/
    def acceptedCopy (l : LineId) (g : Genesis D) (src : Pin D) (v : Version D)
        (psigs ss : List (Sig D)) (description curator message : String) : Obj D :=
      { id := .line l, kind := .document, genesis := some g,
        versions := [branchVersion src v psigs description curator message], sigs := ss }

It is a well-formed object, and creating it is a valid step whenever the
line is free in the curator's archive, the revision is found at a hint of
its pin, the references may be held by a new version, and its identity and
signature pass the checks of [chapter 7](45-worlds.md) (`IdentityOk`,
`LineOk`): the curator is not the originator nor the revision's owner, the
line is named by a name of the genesis record, and the curator's archive
hosts the curator, holds its valid key log, and has the copy signed. These
last two are about keys, and the stories check them by computation.
Section 9.6 speaks of copying a revision, a document; the model does not
check that, and a copy of a collection version would lose its member list,
which the model keeps apart from files. The tools copy only documents.

    theorem acceptedCopy_wf (l : LineId) (g : Genesis D) (src : Pin D) (v : Version D)
        (psigs ss : List (Sig D)) (d c m : String) :
        (acceptedCopy l g src v psigs ss d c m).WF (.line l) :=
      ⟨rfl, by simp [acceptedCopy], fun _ => WellFormed.single rfl,
        by simp [acceptedCopy, branchVersion], by simp [acceptedCopy, branchVersion, Version.membersOk],
        StatusOk.single _ (fun _ => rfl), rfl⟩

    theorem acceptedCopy_valid {w : World D} {a : ArchiveId} {ar : Archive D} {l : LineId}
        (ha : w a = some ar) (hfree : ar.entries (.line l) = none) (g : Genesis D) (src : Pin D)
        (v : Version D) (psigs ss : List (Sig D)) (d c m : String)
        {b : ArchiveId} (hb : b ∈ src.hints) (hsrc : resolveAt E.hash w b src = .ok v)
        (hsrcl : src.line ≠ keyLogLine src.line.owner) (hrefs : ∀ r ∈ v.refs, PinOk E w r.pin)
        (hid : IdentityOk E l (acceptedCopy l g src v psigs ss d c m))
        (hline : LineOk E w a ar l (acceptedCopy l g src v psigs ss d c m))
        (hsigs : ∀ s ∈ ss, SigOk E w a (acceptedCopy l g src v psigs ss d c m) s) :
        ValidStep E w (setEntry w a (.line l) (.live (acceptedCopy l g src v psigs ss d c m))) := by
      refine .create w a ar _ _ ha hfree (acceptedCopy_wf l g src v psigs ss d c m) ?_ ?_ ?_
        ⟨hid, fun _ => hline⟩ hsigs
      · intro x hx p hp
        simp only [acceptedCopy, List.mem_singleton] at hx
        subst hx
        simp only [branchVersion, Version.pins, Version.memberPins, Version.parentPins,
          List.nil_append, List.mem_append, List.mem_map, List.mem_singleton] at hp
        rcases hp with ⟨r, hr, rfl⟩ | rfl
        · exact hrefs r hr
        · exact ⟨hsrcl, Or.inl ⟨b, hb, v, hsrc⟩⟩
      · intro _ i hi
        simp only [acceptedCopy, List.length_singleton] at hi
        have : i = 0 := by omega
        subst this
        simp only [acceptedCopy, List.getElem_cons_zero, BranchPointOk, branchVersion, prevParent]
        exact Or.inr ⟨fun _ h => (nomatch h), b, hb, v, hsrc, rfl, rfl, fun _ h => (nomatch h)⟩
      · intro _
        simp [HeadFollows, acceptedCopy, branchVersion, Version.FollowsHeads]

The copy is another line, kept by the curator's archive, so a takedown of
the parent leaves it alone: the pin of its first version still resolves to
it there. This is what accepted copies are for. The theorem holds of every
object other than the one taken down; nothing in it is particular to
branches, which is the point: a branch is another line.

    /-- **An accepted copy survives the parent**, as every other line does. -/
    theorem acceptedCopy_survives {w : World D} {a s : ArchiveId} {oid : ObjectId} {l : LineId}
        {o c : Obj D} {x : Version D} (hl : lookup w a oid = some (.live o))
        (hc : lookup w s (.line l) = some (.live c)) (h1 : c.versionAt 1 = some x)
        (hdiff : ¬ (s = a ∧ ObjectId.line l = oid)) :
        resolveAt E.hash (takedown E.hash w a oid o) s ⟨l, 1, E.hash (c.inventory 1), []⟩ = .ok x := by
      rw [takedown_other E.hash hl hdiff]
      unfold resolveAt
      simp only [hc]
      exact resolveEntry_live_of E.hash h1 rfl

And it is never taken for the parent. Its inventories name another line,
so they differ from the parent's, and, unless they collide, so do their
digests: a pin of the parent cannot resolve on the branch. This is why "an
accepted copy is not a mirror: a location holding only it is never given in
`at` for the parent's line" (section 9.6).

    /-- **A branch is not a copy of its parent.** -/
    theorem branch_not_copy {o c : Obj D} {p : Pin D} {v u : Version D}
        (hother : c.id ≠ o.id)
        (hcol : NoCollision E (c.inventory p.version) (o.inventory p.version))
        (ho : resolveEntry E.hash (some (.live o)) p = .ok v) :
        resolveEntry E.hash (some (.live c)) p ≠ .ok u := by
      intro hc
      obtain ⟨_, hdo⟩ := resolveEntry_live_ok E.hash ho
      obtain ⟨_, hdc⟩ := resolveEntry_live_ok E.hash hc
      have heq := hcol (hdc.trans hdo.symm)
      exact hother (congrArg Inventory.id heq)

    end OpenSheaf
