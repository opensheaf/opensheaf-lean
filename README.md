# OpenSheaf in Lean

A formal model of the [OpenSheaf specification](https://opensheaf.org/)
(version 0.1, draft) in [Lean 4](https://lean-lang.org/): objects, object
versions and document versions, archives, pins, catalogues and selections,
and the changes that archives go through, with proofs of the properties that
the specification states in prose.

The model is **non-normative**: where it and the specification differ, the
specification holds, and the difference is a bug of one or the other, to be
reported. Its purpose is to make the semantics precise, to find ambiguities
and corner cases of the text, and to check design proposals before they are
written into the specification.

This repository holds two literate programs, published together at
<https://opensheaf.org/opensheaf-lean/>, with a landing page for both:

- **the model** (`literate/`, the library `OpenSheaf`), at
  <https://opensheaf.org/opensheaf-lean/model/>;
- **OpenSheaf as a sheaf** (`literate-sheaf/`, the library `Sheaf`), an
  application of the model, at <https://opensheaf.org/opensheaf-lean/sheaf/>:
  named document versions, ordered by history, are the base, each object
  version is a section, and in every world built by events the sections of
  all copies glue into exactly one.

## Contents of the model

| Chapter | Specification | What it proves |
|---|---|---|
| [Basic](literate/10-basic.md) (`OpenSheaf/Basic.lean`) | sections 3, 7, 9, 10; issues #21, #28 | definitions: pins, member lists, references (a role and a pin, as proposed in #21 and #28), object versions |
| [Object](literate/20-object.md) (`OpenSheaf/Object.lean`) | sections 7.3, 9, 11.1 | inventories name their object; document versions count the changes of content (files as a set, and the member list): description-only versions and withdrawals keep the number, new content gets the next one, and each keeps a history well formed; the choices made on issues #23 (removals) and #25 (no reinstatement) |
| [Archive](literate/30-archive.md) (`OpenSheaf/Archive.lean`) | sections 5, 10.2, 11.2, 11.3, 14 | **immutability**: once a pin resolves to a version, no deposit, new object or new archive changes that version (`Step.resolve_ok`, `Steps.resolve_ok`); a takedown makes pins of the object resolve to `removed`, and changes nothing else (`takedown_removed`, `takedown_other`) |
| [Collection](literate/40-collection.md) (`OpenSheaf/Collection.lean`) | section 10.1 | updating a **selection** leaves it unchanged (`collect_selection`); in a **catalogue**, members with `follow` move to the head, which resolves to the newest object version, and the others stay (`collect_follow`, `collect_fixed`, `headPin_resolves`); member lists obey the rules of section 10.2 (one pin per catalogue member, non-empty revision sets, no `follow` in a selection), and updating keeps them (`collect_wf`) |
| [Worlds](literate/45-worlds.md) (`OpenSheaf/Worlds.lean`) | sections 7, 7.3, 7.4, 10.2, 10.4, 11.2, 11.3 | **valid steps** (the checks of the specification on each new object and version, including member lists, followed members pinning the head, and mirrors; pins of objects taken down are carried over) keep worlds well formed (`ValidStep.wf`); in worlds built by valid steps every member is pinned and no pin dangles (`ValidSteps.members_pinned`, `ValidSteps.pins_ok`); with **takedowns** among the events, every pin held resolves or reports removed (`Events.sound`); tombstones stay, so identifiers are never reused (`Steps.tomb_stays`, `Events.tomb_stays`); objects only grow (`Steps.live_grows`) |
| [Copies](literate/48-copies.md) (`OpenSheaf/Copies.lean`) | sections 6.4, 10.3 to 10.5 | a **mirror** resolves exactly the original's pins it has copied (`mirror_agrees`, `mirror_sound`); unless the inventories collide, a pin authenticates **any copy** (`copy_authentic`), and resolution through mirrors is sound (`resolveVia_sound`); valid steps keep **mirrors** prefixes of their originals, through takedowns too, so a mirror resolves its original's pins in every world built by events (`Events.mirrorsOk`, `Events.mirror_resolves`); any two copies of an object, wherever kept, are prefixes of one another, even after the original is taken down (`Events.copiesAgree`); a mirror stands in for a lost archive when the archives listed before it fail (`resolveVia_mirror`); an **accepted copy** holds the files vetted and records its source, is a valid step (`acceptedCopy_valid`), passes the check of section 14 (`acceptedCopy_checks`), survives the original (`acceptedCopy_survives`), and, its inventories naming another object, is never taken for it (`acceptedCopy_not_mirror`) |
| [Acts](literate/49-acts.md) (`OpenSheaf/Acts.lean`) | sections 3, 7.1, 10.1, 10.2, 10.4; issue #13 | **who may act**: every change is an act of an agent who is a writer of the archive it changes; an outsider changes nothing in an archive (`Act.outsider`); every version of every object, mirrors included, was deposited by a writer of the object's own archive, so custodians cannot add versions in the authors' name (`Acts.depositors`); a selection changes only by its curator (`Acts.curated`) |
| [States](literate/50-states.md) (`OpenSheaf/States.lean`) | proposal, [#29](https://github.com/opensheaf/opensheaf.github.io/issues/29) | with drafts as a tail of the history and pins only to versions at least as fixed (draft < private < public): rewriting drafts never breaks a pin held by a sealed version (`sealed_pins_survive`), and publishing an object whose sealed versions pin only public versions keeps the rule (`publish_fixed`) |
| [Patterns](literate/60-patterns.md) (`OpenSheaf/Patterns.lean`) | the use cases | the promises of the use cases, for every world: a vetted selection verifies identically after any changes (`selection_stable`), and so do nested collections (`nested_stable`); a catalogue pins a co-author's new deposit (`follow_after_deposit`); a description-only correction is not a new document version (`correction_same_document_version`); a withdrawal keeps the vetted revision (`withdrawal_keeps_vetted`); a takedown is reported (`takedown_reported`); a withdrawal seen in both columns of the table "What happens when": followed by a catalogue, not by a selection (`withdrawal_both_columns`); the owner decides: only its writers deposit the versions of an object kept in its own archive, and nobody else changes it (`owner_controls`); a mirror is a receipt of the versions received (`mirror_receipt`); a record taken down at the end of its retention reports removed forever, and leaves the rest as it was (`record_retention`) |
| [Impossible](literate/65-impossible.md) (`OpenSheaf/Impossible.lean`) | sections 7.3, 10.2, 11.3 | breaks of the protocol shown impossible or detected: a pin cannot change its meaning (`pin_meaning_fixed`); history cannot be rewritten by any steps (`history_not_rewritten`), and rewriting it outside the protocol is detected unless the inventories collide (`tamper_detected`); tombstoned identifiers are never reused (`no_reuse`); one document version has one content and one content one document version (`one_number_one_content`, `one_content_one_number`), and numbers start at 1 with no gaps (`doc_pos`, `no_gaps`); **pins cannot form cycles** in any world built by valid steps and takedowns, whatever the digest (`no_cycles`, `no_cycles_events`); a withdrawal cannot be undone by valid steps (`ValidSteps.withdrawn_stays`, the choice on #25) |
| [Story](literate/70-story.md) (`OpenSheaf/Story.lean`) | the use cases | tests: a world built by fourteen valid steps from nothing (an author's paper, a journal issue and accepted copy, a co-author's catalogue, note and mirror), then a lost archive, a takedown and attempts to break the protocol (an author acting on the journal's issue, a version rewritten in place, a pin of a version that does not exist yet, a reinstatement, an accepted copy posing as the original, member lists that break section 10.2, a mirror that does not copy), with each verifier report checked by `decide`, and the general theorems applied to the same worlds |
| [Record](literate/75-record.md) (`OpenSheaf/Record.lean`) | the use case "A learning record" | tests: a student's thesis and the department's record of it, built by acts from nothing; the record verifies, comments stay tied to the version commented on while the thesis moves on, the record's history is kept, the owner decides, the department's mirror is a receipt that catches a rewrite of the first submission, and the record is deleted at the end of its retention without touching the thesis, each checked by `decide` and by the general theorems |
| [References](literate/80-references.md) (`OpenSheaf/References.lean`) | section 8.1; issues #21, #28 | **pinned references** between documents: they never dangle (`ValidSteps.refs_resolve`, `Events.refs_held`), and no two versions refer to each other (`no_mutual_refs`), though a pinned link back from a later version is possible; a pin fixes what its version refers to (`pin_fixes_refs`); every copy carries the references (`copy_keeps_refs`), not the versions they name; a takedown behind a reference is invisible to a verifier that knows only the core (`takedown_behind_ref`); the short account and its detailed argument, computed |

## Contents of the sheaf

| Chapter | Module | What it proves |
|---|---|---|
| [Sheaves on an order](literate-sheaf/10-order.md) | `Sheaf.Order` | the sheaf condition for sections on a preorder (`sheaf`); local conditions glue on an Alexandrov space (`glue_satisfies`) |
| [Named document versions](literate-sheaf/20-base.md) | `Sheaf.Base` | the base and the order of history; the content of a document version, as a value |
| [An object version is a section](literate-sheaf/30-object.md) | `Sheaf.Object` | its set is open, by no gaps (`held_iff`); its pieces glue, by section 7.3 (`pieces_compatible`, `objSec_glues`); immutability is restriction (`objSec_restrict`) |
| [A world is a sheaf](literate-sheaf/40-world.md) | `Sheaf.World` | with the model's `Events.copiesAgree`, the sections of a world glue, uniquely (`world_sheaf`); a new number is new content, checked piece by piece, holds of the whole (`world_newContent`) |
| [Pins and accepted copies](literate-sheaf/50-pins.md) | `Sheaf.Pins` | a pin names a section, in any world, unless inventories collide (`pin_names_section`); an accepted copy holds the vetted content at another point (`acceptedCopy_agrees`) |
| [Collections and what they pin](literate-sheaf/55-collections.md) | `Sheaf.Collections` | the pins of member lists in the order; what a world holds stays open (`heldIn_open_byPins`); below a collection version lies each member it pins, with the content its pin fixes, unless taken down (`members_below`, `collection_stalk`) |
| [A story, as a sheaf](literate-sheaf/60-story.md) | `Sheaf.Story` | the model's story as a sheaf, by computation; a forged copy and a reused number do not glue |

## Modelling choices

- **Digests.** A digest is a value of an arbitrary type `D`, and the digest
  of an inventory is `hash` applied to the versions it describes (versions
  `1` to `n`, as in OCFL), together with the archive and identifier of the
  object. No property of `hash` is assumed, except by five theorems
  (`copy_authentic`, `resolveVia_sound`, `acceptedCopy_not_mirror`,
  `tamper_detected`, `copy_keeps_refs`), which assume that the two inventories they compare do
  not collide. None assumes that `hash` is injective, which no real digest
  is.
- **Abstractions.** The description (`datacite.json`) is a string; files are
  logical paths with digests; JSON, OCFL layout, HTTP and the discovery
  document are not modelled. Pins are those of member lists and of
  references between documents.
- **Archives** are maps from identifiers to objects or tombstones, and the
  world is a map from archive identifiers to archives. Changes are steps of
  an inductive relation (`Step`), so that a theorem about all changes is a
  case analysis.

## Next

- the parts of section 7.3 not yet modelled: completion of a version
  deposited without sources, and `history` for versions deposited out of
  order;
- revisions of selections with their `documentVersion` (section 10.2);
- licences: mirrors only of objects whose licences allow redistribution
  (sections 10.4, 10.6);
- how writers are authorised and checked (keys, as proposed in PR #30), and
  transfers of an object to another writer (issue #13);
- resolution through the mirrors listed in the archive's discovery document
  (section 6.4), and what takedowns do to mirrors (issue #33);
- notices, kept unchanged in every later version (section 7.3);
- withdrawal notices and their presentation with vetted revisions;
- sealing (#29) with the rule kept, which needs collision resistance;
- the referee commitment of the peer-review use case, under hiding and
  binding assumptions;
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
