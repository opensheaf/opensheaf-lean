# OpenSheaf in Lean

A formal model of the [OpenSheaf specification](https://opensheaf.org/)
(version 0.2, draft) in [Lean 4](https://lean-lang.org/): lines and their
object versions and document versions, owners and their key logs with
pre-rotation, signatures, archives and copies, pins, catalogues and
selections, branches and drafts, and the changes that archives go through,
with proofs of the properties that the specification states in prose.

The model is **non-normative**: where it and the specification differ, the
specification holds, and the difference is a bug of one or the other, to be
reported. Its purpose is to make the semantics precise, to find ambiguities
and corner cases of the text, and to check design proposals before they are
written into the specification. Until 19 November 2026 it modelled version
0.1 of the specification; its history keeps that model.

This repository holds two literate programs, published together at
<https://opensheaf.org/opensheaf-lean/>, with a landing page for both:

- **the model** (`literate/`, the library `OpenSheaf`), at
  <https://opensheaf.org/opensheaf-lean/model/>;
- **OpenSheaf as a sheaf** (`literate-sheaf/`, the library `Sheaf`), an
  application of the model, at <https://opensheaf.org/opensheaf-lean/sheaf/>:
  named document versions of lines, ordered by deposit, are the base, each
  object version is a section, and in every world built by events the
  sections of all copies glue into exactly one when owners sign one
  history; a fork of a line, signed by its owner's keys, is what stops
  them gluing.

## Contents of the model

| Chapter | Specification | What it proves |
|---|---|---|
| [Basic](literate/10-basic.md) (`OpenSheaf/Basic.lean`) | sections 4 to 9; issues #21, #28 | definitions: names, owner names, lines and drafts, pins with their hints (`at`), member lists, references (a role and a pin, as proposed in #21 and #28), `keys.json`, signature files, fork records' carried versions, branch points, object versions |
| [Object](literate/20-object.md) (`OpenSheaf/Object.lean`) | sections 4.1 to 4.3, 5.1, 13.1 | genesis records; inventories name their object and its genesis record, and fix every earlier inventory (the inventory chain, #46); the environment (digests, key digests, names, which signatures verify); document versions count the changes of content (section 4.2): description-only versions and withdrawals keep the number, new content gets the next one, and each keeps a history well formed; no reinstatement (the choice on #25) |
| [Archive](literate/30-archive.md) (`OpenSheaf/Archive.lean`) | sections 3, 4, 8.5, 12.3, 13 | archives host owners; resolution at an archive and through the hints of a pin; **immutability**: once a pin resolves to a version at an archive, no deposit, new object, new archive or new witness changes it (`Step.resolveAt_ok`, `Steps.resolveAt_ok`), so a pin found stays found (`Steps.found`); a takedown makes pins of the line resolve there to `removed`, and changes nothing else (`takedown_removed`, `takedown_other`) |
| [Owners](literate/35-owners.md) (`OpenSheaf/Owners.lean`) | sections 5.2, 6.1 to 6.3; issue #58 | **key logs with pre-rotation**: the rules on `keys.json`, the computed first version, versions signed by the rotation keys of the version before, ending versions and fork records; a key log never forks at its first version, unless genesis records collide (`no_fork_at_first`); no key is both current and rotation key (`KeyLogOk.disjoint`), so current keys can neither change a key log nor fork it (`current_keys_cannot_extend`, `current_keys_cannot_fork`); after an ending version only a fork record, and nothing after a fork record (`KeyLogOk.after_end`, `KeyLogOk.fork_last`); fork records check the versions they carry, and both sides of a fork are signed by rotation keys committed in the version before the fork point (`KeyLogOk.fork_needs_rotation`, `KeyLogOk.held_rotation`) |
| [Lines](literate/38-lines.md) (`OpenSheaf/Lines.lean`) | sections 6.3, 6.4, 7.1, 7.3 | signed directly, vouched for, contested (exposed keys, fork points), against a copy of the owner's key log; a signed version has a good signature by a current key of a version that is not an ending version (`SignedWith.signer`); more signature files, or a weaker test, keep it signed (`SignedWith.mono`); a rotation key never signs a line (`rotation_key_signs_no_line`) |
| [Collection](literate/40-collection.md) (`OpenSheaf/Collection.lean`) | sections 8.2 to 8.4 | updating a **selection** leaves it unchanged (`collect_selection`); in a **catalogue**, members with `follow` move to the head of the first copy found at their hints, which resolves there (`collect_follow`, `collect_fixed`, `headPin_resolves`); member lists obey section 8 (non-empty `at`, one pin per catalogue member, non-empty revision sets, no `follow` in a selection), and updating keeps them (`collect_wf`) |
| [Worlds](literate/45-worlds.md) (`OpenSheaf/Worlds.lean`) | sections 4, 5, 7.5, 8, 9, 11, 13 | **valid steps**: identity (names of the genesis record, originator's line or branch), signatures against the archive's copy of the owner's key log (signed, not contested, not frozen; ended owners only copied; one version at a time), mirrors that only copy, branch points that hold their parents' files and move only forward, member lists, followed members (the head, or the pin kept when the head does not extend it), witnesses whose keys the key log allows, drafts that are drafts, pins found or carried over and never naming a key log; they keep worlds well formed (`ValidStep.wf`), every member is pinned and no pin dangles (`ValidSteps.members_pinned`, `ValidSteps.pins_ok`); with **takedowns**, every pin held is found or reports removed (`Events.sound`); tombstones stay (`Events.tomb_stays`); objects only grow (`Steps.live_grows`) |
| [Acts](literate/47-acts.md) (`OpenSheaf/Acts.lean`) | sections 3, 7.5, 11, 15.1 | **owners sign, places host**: in every world built by events, the head of every copy of every line is signed with a current key of a version of its owner's key log that the world holds, and every key log is valid (`Events.ownersSign`); so forgery needs such a key (`forgery_needs_owner_key`), which is a key of the owner's genesis record or of a key-log version signed by rotation keys of the one before, unless names collide (`Events.ownerKey_origin`); key logs are not taken down in the model; a mirror only copies (`mirror_copies`); a fork freezes the owner (`frozen_adds_nothing`); an ended owner deposits nothing (`ended_copies`); exposed keys add nothing (`exposed_keys_add_nothing`); every copy keeps the identity of its line (`Events.identitiesOk`), so the copies of a line hold one genesis record unless the names of the two records collide (`Events.genesis_agree`) |
| [Copies](literate/48-copies.md) (`OpenSheaf/Copies.lean`) | sections 7.4, 8.5, 9, 11, 12.3 | copies of a line agree when its owner signs one history and no copy held collides with it (`Events.copiesAgree`), and a fork of a line was signed with keys of the owner's key log (`Events.fork_signed`); a pin keeps its meaning at every hint (`Steps.resolve_ok`); a pin authenticates any copy, unless inventories collide (`copy_authentic`, `resolve_sound`); a copy at a later hint stands in (`resolve_stand_in`); branches hold their parents' files in every world built by events, unless the copy found collides with the inventory checked (`Events.branch_files`); an accepted copy is a valid step (`acceptedCopy_valid`), survives the parent (`acceptedCopy_survives`) and is never taken for it (`branch_not_copy`) |
| [Drafts](literate/50-drafts.md) (`OpenSheaf/Drafts.lean`) | section 10 | drafts rewritten or deleted touch no line (`DraftEvent.lines`): every pin resolves as before (`DraftEvent.resolveAt`, `DraftEvent.resolve`), and worlds stay sound (`DraftEvent.sound`); sealing makes a new line, document version 1 |
| [Patterns](literate/60-patterns.md) (`OpenSheaf/Patterns.lean`) | the use cases | the promises of the use cases, for every world: a vetted selection verifies identically after any steps, when the owners pinned are honest (`selection_stable`), and so do nested collections (`nested_stable`); a catalogue pins a co-author's new deposit (`follow_after_deposit`); a description-only correction is not a new document version (`correction_same_document_version`); a withdrawal keeps the vetted revision (`withdrawal_keeps_vetted`), in both columns of the table "What happens when" (`withdrawal_both_columns`); only the owner adds to a member (`member_signed`, `owner_decides`); a takedown is reported (`takedown_reported`); a mirror is a receipt (`mirror_receipt`); a record taken down at the end of its retention reports removed forever, and leaves the rest as it was (`record_retention`) |
| [Impossible](literate/65-impossible.md) (`OpenSheaf/Impossible.lean`) | sections 4, 4.2, 8.5, 13 | breaks of the protocol shown impossible or detected: a pin cannot change its meaning (`pin_meaning_fixed`, `pin_meaning_fixed_hints`); history cannot be rewritten by any steps (`history_not_rewritten`), and rewriting it outside the protocol is detected unless the inventories collide (`tamper_detected`); tombstoned identifiers are never reused (`no_reuse`); one document version has one content and one content one document version, numbers start at 1 with no gaps (`one_number_one_content`, `one_content_one_number`, `doc_pos`, `no_gaps`); **pins cannot form cycles** in any world built by valid steps whose owners sign one history, which no copy held collides with (`no_cycles`); no pin held names a key log (`Events.pinsNoKeyLog`, `Events.pinned_not_owner`); a withdrawal cannot be undone (`ValidSteps.withdrawn_stays`, the choice on #25) |
| [Story](literate/70-story.md) (`OpenSheaf/Story.lean`) | the use cases | tests: a world built by nineteen valid steps from nothing (three owners with key logs, a paper sealed and revised after a key rotation, a journal issue and accepted copy, a co-author's catalogue and mirror), then a lost archive, a takedown and a draft, with each verifier report checked by `decide`; attempts that fail (a signature not the owner's, a rewrite in place, a pin of a version that does not exist yet, a fresh pin into a line taken down, a reinstatement, a branch posing as its parent, bad member lists, a mirror that does not copy, a version signed with an exposed key, a key log changed with current keys, a fork record that freezes the owner); and the general theorems applied to the same worlds |
| [Record](literate/75-record.md) (`OpenSheaf/Record.lean`) | the use case "A learning record" | tests: a student's thesis and the department's record of it, built by valid steps from nothing; the department's copy is a receipt that catches a rewrite of the first submission, the comments' `Reviews` reference stays on the version commented on, the heads are signed by their owners, and the record is deleted at the end of its retention without touching the thesis |
| [References](literate/80-references.md) (`OpenSheaf/References.lean`) | section 4.4; issues #21, #28 | **pinned references** between documents: they are found, or reported removed (`ValidSteps.refs_resolve`, `Events.refs_held`); a pin fixes what its version refers to, when owners are honest (`pin_fixes_refs`); every copy carries the references (`copy_keeps_refs`), not the versions they name; a takedown behind a reference is invisible to a verifier that knows only the core (`takedown_behind_ref`); the short account and its detailed argument, computed |

## Contents of the sheaf

| Chapter | Module | What it proves |
|---|---|---|
| [Sheaves on an order](literate-sheaf/10-order.md) | `Sheaf.Order` | the sheaf condition for sections on a preorder (`sheaf`); local conditions glue on an Alexandrov space (`glue_satisfies`) |
| [Named document versions](literate-sheaf/20-base.md) | `Sheaf.Base` | the base, named document versions of lines, and the order of deposit; the content of a document version, as a value |
| [An object version is a section](literate-sheaf/30-object.md) | `Sheaf.Object` | its set is open (`covers_open`) and is what its pieces hold (`covers_iff`); its pieces glue, by section 4.2 (`pieces_compatible`, `objSec_glues`); a later object version restricts to an earlier one (`objSec_restrict`) |
| [The sections of a world glue](literate-sheaf/40-world.md) | `Sheaf.World` | with the model's `Events.copiesAgree`, the sections of a world glue, uniquely, when owners are honest (`world_glues`); otherwise an owner's keys signed a fork (`no_glue_fork`); a condition checked piece by piece holds of the whole (`world_newContent`) |
| [Pins and accepted copies](literate-sheaf/50-pins.md) | `Sheaf.Pins` | a pin names a section, unless inventories collide (`pin_names_section`); an accepted copy, a branch, holds the vetted content at another point (`acceptedCopy_agrees`), and every branch holds its parent's files (`Events.branch_value_files`) |
| [Collections and what they pin](literate-sheaf/55-collections.md) | `Sheaf.Collections` | the pins of member lists in the order; below a collection version lies each member it pins, with the content its pin fixes, or its line was taken down at a hint (`members_below`, `collection_members`) |
| [The order with pins](literate-sheaf/57-acyclic.md) | `Sheaf.Acyclic` | in every world built by valid steps with honest owners, the order with pins is a partial order (`byPins_antisymm`); steps keep its edges (`Steps.le`), a takedown adds none (`takedown_pinStep`); the case with takedowns is open |
| [A story, as a sheaf](literate-sheaf/60-story.md) | `Sheaf.Story` | the model's story as a sheaf: its owners are honest, so its sections glue with no hypothesis (`story_honest`, `story_glues`); by computation, descriptions do not glue (`descriptions_incompatible`); a forged copy, read as a fork, and a reused number do not glue |
| [Names are eternal](literate-sheaf/70-eternal.md) | `Sheaf.Eternal` | a named document version has the same content in any two worlds built by events, and their glued sections agree, when owners are honest (`names_eternal`, `glue_eternal`) |
| [What lies below is fixed](literate-sheaf/71-below.md) | `Sheaf.Below` | once a named document version is held, no later valid step adds or removes anything below it in the order with pins, and the glued sections agree below it (`below_back`, `below_fixed`, `below_values`) |
| [Verification is lifting](literate-sheaf/72-lifting.md) | `Sheaf.Lifting` | the inventories of a world glue (`inventory_glues`); hashing is injective on the sections it compares, unless they collide (`digests_injective`); every copy that holds the pinned version gives the same verdict, when owners are honest (`copies_same_verdict`); a pin resolves exactly when it lifts (`lifts_iff`), uniquely (`lift_unique`) |
| [Verification is local](literate-sheaf/74-local.md) | `Sheaf.Local` | restricting a world restricts its sheaf (`restrict_glue`); a collection verifies in its support as in the whole world (`verify_local`) |
| [Separate worlds](literate-sheaf/76-federation.md) | `Sheaf.Federation` | two worlds built by events glue when owners are honest, though they may share lines (`separate_glue`), and each keeps its section (`union_restricts_left`, `union_restricts_right`) |
| [Descriptions are the fibres](literate-sheaf/78-fibres.md) | `Sheaf.Fibres` | the document version an object version holds: its image is what the world holds (`proj_image`), its fibres are the contents (`proj_fibre`), content factors through it (`content_factors`), but it is not monotone; the top is monotone (`top_mono`, `covers_principal`) and its fibres are runs of description-only versions (`top_step_iff`) |
| [The citable section](literate-sheaf/79-citable.md) | `Sheaf.Citable` | the worlds of a run glue over time into one section over everything ever held, when owners are honest (`citable_glues`) |

## Modelling choices

See the [introduction](literate/index.md#modelling-choices) of the model.
In short: digests, key digests, names and which signatures verify are given
by an environment; most theorems assume nothing of them; those about
copies from anywhere, tampering and branches assume that the inventories
compared do not collide, and those about the agreement of copies that each
owner signs one history and that no copy held collides with it
(`OneHistory`). Each assumes only that given pairs of inventories do not
collide, never that the digest is injective. Open questions of the specification
on which the model makes a choice are marked in their chapters.

## Next

- the parts of section 4.2 not yet modelled: completion of a version
  deposited without sources, `history` for versions deposited out of order,
  notices, and the document's own files told from note files;
- revisions of selections with their `documentVersion` (section 8.4);
- licences: mirrors only of lines whose licences allow redistribution
  (section 11.2);
- the evidence of a branch point (`parent.inventory.json`,
  `parent.object.json`, `parent.chain/`) and the check of section 9.3
  without the parent; moving a branch point with files of its own (#57);
- the clashes of section 5.3, reused genesis records (section 5.4), and
  returns of a line taken down (section 13.2);
- pins form no cycles also with takedowns among the events, when a line
  taken down comes back elsewhere (the proof needs the history of the
  world, [What cannot happen](literate/65-impossible.md));
- timestamps, and the evidence that dates a signature before an exposure
  or a fork (section 7.3);
- keepers and accepted successors (section 6.6);
- a verifier, executable, proved against this model.

## Build

Install Lean with [elan](https://github.com/leanprover/elan) and the
literate tools, then

    pip install -r requirements-literate.txt
    literate tangle                       # the model's Lean files
    literate tangle literate-sheaf/*.md   # the sheaf's Lean files
    lake build --wfail                    # check every proof

The model has no dependencies beyond Lean's standard library.

## Licence

GNU General Public License, version 3 or later (see `LICENSE`).
