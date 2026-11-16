# OpenSheaf as a sheaf

The name OpenSheaf says that archives kept and verified separately glue
into a whole, as the local pieces of a sheaf do. This literate program
makes the claim precise and proves it in [Lean 4](https://lean-lang.org/).
It is an application of the formal model of the specification,
[OpenSheaf in Lean](https://opensheaf.org/opensheaf-lean/model/), kept in
the same repository as a separate document: it adds no rule to the model,
and only reads the model's worlds as sheaves.

Like the model, it is **non-normative**. Where it and the
[specification](https://opensheaf.org/) differ, the specification holds.

## The claim

- **The base** is the set of *named document versions*: an object, named
  by its archive and identifier, and a document version number. Its open
  sets are the sets closed under earlier versions of the same object (the
  Alexandrov topology of the order of deposit).
- **The value** at a named document version is its content: its files,
  and for a collection its member list.
- **Collections.** A named document version also comes after the
  versions its member list pins, so that below a selection version lies the
  selection together with what it vetted, and the earlier versions of
  those, which its pins fix too.
- **The sections** come from object versions. Each object version, kept in
  its own archive or in a mirror, says what every document version up to
  it holds: a section over an open set.
- **The theorem.** In every world built from nothing by the events the
  specification allows, the sections of all copies of all objects are
  compatible, and glue into exactly one section: one content for each
  named document version, whichever copy and whichever object version it is
  read from.

Precisely: the sections over a set, with values in the contents, form a
sheaf for general reasons (chapter 1), whatever the protocol. What the
theorem says about OpenSheaf is that the data of a world form a compatible
family of sections. So a world defines one section of that sheaf, over the
open set of what it holds, and every copy and every object version is a
restriction of it. That is all that "a world is a sheaf" means here: the
theorems are about which sections a world gives, not about the sheaf, which
is the same for every world.

A name carries no digest, so this is not automatic. Two copies could hold
different content under the same name, and then nothing glues. The proof
shows which rules of the specification make the pieces agree:

- within one object, the rule of section 7.3, which gives each document
  version one content, and which the verifier checks (section 14): the
  pieces of an object version glue because of it, and a history that
  breaks it has pieces that do not glue;
- between copies kept in different archives, the rule that a mirror copies
  its original byte for byte (section 10.4): any two copies of an object
  have histories of which one is a prefix of the other;
- between any copies, found anywhere, a pin: two objects that resolve the
  same pin give the same section, unless digests collide (section 6.4).

## How to read it

1. [Sheaves on an order](10-order.md): the mathematics, without Mathlib:
   sections, the sheaf condition, and local conditions, which glue on an
   Alexandrov space;
2. [Named document versions](20-base.md): the base, the order of deposit,
   the content of a document version, and the rule "one number, one
   content" in both directions;
3. [An object version is a section](30-object.md): its set is open, and
   is what its pieces hold (no gaps), it glues its pieces (section 7.3),
   and a later object version restricts to an earlier one (versions are
   fixed);
4. [The sections of a world glue](40-world.md): copies agree in every world built by
   events, so the sections of a world glue, uniquely; a condition checked
   one object version at a time holds of the whole;
5. [Pins and accepted copies](50-pins.md): a pin names a section, in any
   world; an accepted copy holds the vetted content at another point, and
   every copy in a world built by events holds the files of its source;
6. [Collections and what they pin](55-collections.md): the pins of member
   lists added to the order; below a collection version lies each member
   it pins, with the content its pin fixes, unless it was taken down;
7. [The order with pins](57-acyclic.md): in every world built by events,
   the order with pins is a partial order, and later steps keep its edges;
8. [A story, as a sheaf](60-story.md): the story of the model, read as a
   sheaf and checked by computation (the journal's issue and the paper it
   vetted among them), and two broken worlds that do not glue: a forged
   copy, and a number reused;
9. [Names are eternal](70-eternal.md): a named document version keeps its
   content through every later event, and once held nowhere is never held
   again; the glued sections of a world and of any later one agree;
10. [What lies below is fixed](71-below.md): once a named document version
   is held, no later event adds anything below it in the order with pins,
   valid steps remove nothing, and the values below agree;
11. [Verification is lifting](72-lifting.md): pins are points of a sheaf of
   digests, verification lifts them to the sheaf of inventories, the lift is
   unique without collisions, and every copy gives the same verdict;
12. [Verification is local](74-local.md): restricting a world restricts its
   sheaf, and a collection verifies in its support as in the whole world;
13. [Separate worlds](76-federation.md): worlds built by events refer only
   to their own archives, so two of them on separate archives share
   nothing, glue with no condition, and each keeps its section;
14. [Descriptions are the fibres](78-fibres.md): two maps from object
   versions to named document versions; the fibres of the first are the
   contents, but it is not monotone; the second, the top, is monotone, and
   its fibres are runs of description-only versions; descriptions do not
   glue;
15. [The citable section](79-citable.md): the worlds of a run glue over time
   into one section over everything ever held; each name is held during one
   interval, after which it is reported removed.

Each chapter writes one module of the library, `Sheaf/*.lean`, which
imports the modules of the model it needs. The root of the library imports
every module:

    -- in Sheaf.lean:
    import Sheaf.Order
    import Sheaf.Base
    import Sheaf.Object
    import Sheaf.World
    import Sheaf.Pins
    import Sheaf.Collections
    import Sheaf.Acyclic
    import Sheaf.Story
    import Sheaf.Eternal
    import Sheaf.Below
    import Sheaf.Lifting
    import Sheaf.Local
    import Sheaf.Federation
    import Sheaf.Fibres
    import Sheaf.Citable

## What does not glue

**Descriptions.** Two object versions may describe the same document
version differently: a description-only version adds a DOI, corrects a
stage or a title, or adds a withdrawal (section 7.3); a notice, which the
specification also adds this way, is a file, so new content in the model
(chapter [Named document versions](20-base.md)). Their
descriptions do not agree, and are not meant to. The specification settles
them by authority, not by agreement: the head of the object describes it,
and earlier object versions keep the description as it was known when they
were made. So descriptions are values of object versions, ordered by time,
not values of named document versions, and the sheaf leaves them out.
Chapter [Descriptions are the fibres](78-fibres.md) shows where they vary,
along the fibres of the maps from object versions to named document
versions, and shows on the story that they do not glue. This
is a feature of the design: what is fixed (the content) glues, and what may
be corrected (the description) has an owner instead.

**The reading order.** The history of a document (`history` in
`object.json`) orders its document versions for readers, and a later object
version may correct it. It is not the order of the base, which is the order
of deposit, fixed by the inventories.

## What is left out

- **Worlds that refer to each other.** In the model, a pin or a mirror
  needs its target in the same world: a world built by events refers only
  to its own archives (chapter [Separate worlds](76-federation.md)). Two
  worlds built independently, with pins from one into the other checked
  only when they are combined, need a step relation across worlds, which
  the model does not have.
- **A base that does not depend on the world.** The order with pins
  (chapter 6) is defined from where pins resolve in a world: a takedown
  removes edges. A base fixed once and for all would take pins themselves
  as points, with their digests, which fix what they pin unless digests
  collide.
- **Collisions.** Theorems that need digests not to collide assume it for
  the inventories they compare, not for the digest function as a whole.

- **References of documents.** The pins of member lists are in the order
  (chapter 6): below a collection version lies what it pins. The pins of a
  document's references (issues #21 and #28 of the specification) are not:
  in the model a description-only version may change them, so they belong
  to object versions, not to document versions. They would join the order
  if references became part of the content (issue #28).
- **Completion.** A document version deposited without its sources may be
  completed later, keeping its number (section 7.3). Its content then
  grows, and the values would be partial maps from paths to digests,
  compatible when they agree where both are defined. The model does not
  represent completion, and neither does this program.
- **Branches.** The proposal of PR #30 of the specification (owners, lines,
  deep and shallow branches) would make the base of each object a tree,
  or a graph once a branch point moves: a fork of a line would be a family
  that does not glue, a shallow branch a section of the coarser sheaf of
  digests, and moving a branch point a gluing of two histories. The model
  has no lines or branches yet, so neither does this program.

## The tools

The chapters are in `literate-sheaf/`, beside the model's in `literate/`.
They are tangled into the library `Sheaf` by the
[literate tools](https://github.com/opensheaf/literate), naming the
documents, and the library is built with the model's:

```
literate tangle literate-sheaf/*.md   # write Sheaf.lean and Sheaf/*.lean
lake build --wfail                    # check every proof, of both libraries
```
