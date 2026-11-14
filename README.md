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

## Contents

| Chapter | Specification | What it proves |
|---|---|---|
| [Basic](literate/10-basic.md) (`OpenSheaf/Basic.lean`) | sections 3, 7, 9, 10 | definitions: pins, member lists, object versions |
| [Object](literate/20-object.md) (`OpenSheaf/Object.lean`) | sections 7.3, 9, 11.1 | document versions count the changes of content: description-only versions and withdrawals keep it, new content adds one, and each keeps a history well formed |
| [Archive](literate/30-archive.md) (`OpenSheaf/Archive.lean`) | sections 5, 10.2, 11.2, 11.3, 14 | **immutability**: no deposit, new object or new archive changes what a pin resolves to (`Step.resolve_ok`, `Steps.resolve_ok`); a takedown makes pins of the object resolve to `removed`, and changes nothing else (`takedown_removed`, `takedown_other`) |
| [Collection](literate/40-collection.md) (`OpenSheaf/Collection.lean`) | section 10.1 | updating a **selection** leaves it unchanged (`collect_selection`); in a **catalogue**, members with `follow` move to the head, which resolves to the newest object version, and the others stay (`collect_follow`, `collect_fixed`, `headPin_resolves`) |
| [States](literate/50-states.md) (`OpenSheaf/States.lean`) | proposal, [#29](https://github.com/opensheaf/opensheaf.github.io/issues/29) | with drafts as a tail of the history and pins only to versions at least as fixed (draft < private < public): rewriting drafts never breaks a pin held by a sealed version (`sealed_pins_survive`), and publishing an object whose sealed versions pin only public versions keeps the rule (`publish_fixed`) |
| [Patterns](literate/60-patterns.md) (`OpenSheaf/Patterns.lean`) | the use cases | the promises of the use cases, for every world: a vetted selection verifies identically after any changes (`selection_stable`), and so do nested collections (`nested_stable`); a catalogue pins a co-author's new deposit (`follow_after_deposit`); a description-only correction is not a new document version (`correction_same_document_version`); a withdrawal keeps the vetted revision (`withdrawal_keeps_vetted`); a takedown is reported (`takedown_reported`) |
| [Story](literate/70-story.md) (`OpenSheaf/Story.lean`) | the use cases | tests: a concrete world (an author, a journal issue, a co-author's catalogue) through a revision, a correction and a takedown, with each verifier report checked by `decide`, and the general theorems applied to the same worlds |

## Modelling choices

- **Digests.** A digest is a value of an arbitrary type `D`, and the digest
  of an inventory is `hash` applied to the versions it describes (versions
  `1` to `n`, as in OCFL). No property of `hash` is assumed: the theorems
  above hold for any function. Collision resistance will be needed only by
  statements of the form "a pin that resolves fixes the content", and will
  then be an explicit hypothesis.
- **Abstractions.** The description (`datacite.json`) is a string; files are
  logical paths with digests; JSON, OCFL layout, HTTP and the discovery
  document are not modelled. Pins are those of member lists.
- **Archives** are maps from identifiers to objects or tombstones, and the
  world is a map from archive identifiers to archives. Changes are steps of
  an inductive relation (`Step`), so that a theorem about all changes is a
  case analysis.

## Next

- mirrors and accepted copies (sections 10.4, 10.5): a mirror resolves the
  same pins as the original; an accepted copy is a new object;
- withdrawal notices and their presentation with vetted revisions;
- sealing (#29) with the rule kept, which needs collision resistance;
- the referee commitment of the peer-review use case, under hiding and
  binding assumptions;
- a verifier, executable, proved against this model.

## Build

Install Lean with [elan](https://github.com/leanprover/elan) and the
literate tools, then

    pip install -r requirements-literate.txt
    literate tangle      # write the Lean files from the chapters
    lake build --wfail   # check every proof

The model has no dependencies beyond Lean's standard library.

## Licence

GNU General Public License, version 3 or later (see `LICENSE`).
