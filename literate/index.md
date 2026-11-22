# OpenSheaf in Lean

This is a formal model of the
[OpenSheaf specification](https://opensheaf.org/) (version 0.2, a draft) in
[Lean 4](https://lean-lang.org/), written as a literate program. It defines
lines and their object versions and document versions, owners and their key
logs, signatures, archives and copies, pins, catalogues and selections,
branches and drafts, and the ways archives change. It then proves the
properties that the specification states in prose: that pins, once valid,
stay valid; that a takedown is detected; that only an owner's keys add to
its lines, wherever they are kept; that whoever holds only current keys
cannot change a key log, nor block an exposure, and that a key log never
forks at its first version; that a fork freezes its owner for ever; that
copies of a line agree as long as its owner signs one history; that a
selection does not move unless its curator moves it; that drafts can be
rewritten without breaking any pin; and that a reader who checks a copy
against a copy of the owner's key log, from any host, reads the history
the owner's keys signed.

The model is **non-normative**. Where it and the specification differ, the
specification holds, and the difference is a bug of one or the other, to be
reported. Its purpose is to make the semantics precise, to find the
ambiguities and corner cases of the text, and to check design proposals
before they are written into the specification. An earlier version modelled
version 0.1 of the specification, in which archives owned their objects;
version 0.2 names works by their genesis records, makes owners keyed
identities with key logs, and lines signed versions wherever they are
stored, and the model follows.

## How to read it

The chapters build the model from the bottom up:

1. [Basic notions](10-basic.md): names, owners and lines, pins with their
   hints, member lists, keys and signature files, branch points and object
   versions;
2. [Objects and their history](20-object.md): genesis records, objects,
   inventories (exact, with the inventory chain of section 4.3), the
   environment (digests, names, which signatures verify), and the counting
   of document versions (section 4.2);
3. [Archives and pins](30-archive.md): archives and the owners they host,
   resolution at an archive and through the hints of a pin, the steps that
   change archives, immutability, and takedown;
4. [Owners and key logs](35-owners.md): pre-rotation (section 6.1): the
   rules on `keys.json`, the computed first version, rotation keys (counted
   by the digests committed), ending versions and fork records; a key log
   never forks at its first version, and current keys cannot change it;
5. [Lines and signatures](38-lines.md): signed versions, vouching, exposed
   keys, fork points and contested versions (section 7.3);
6. [Catalogues and selections](40-collection.md): what updating a
   collection does to each type;
7. [Well-formed worlds](45-worlds.md): the valid steps, the model's reading
   of what the specification allows (identity, signatures against the
   archive's copy of the key log, mirrors that only copy, branch points),
   and what they guarantee; then takedowns among the events (of lines, not
   of key logs), after which every pin held is found or reports removed;
8. [Owners sign, places host](47-acts.md): the head of every copy of every
   line is signed by its owner, every key log is valid; forgery needs an
   owner's key; mirrors only copy, a fork freezes an owner, an ended owner
   deposits nothing, and exposed keys add nothing (section 7.5); every
   copy keeps the identity of its line, so copies hold one genesis record
   unless the names of the two records collide;
9. [Copies, mirrors and branches](48-copies.md): copies of a line agree
   when its owner signs one history, and a fork of a line was signed with
   the owner's keys; a pin authenticates any copy, unless digests collide;
   resolution through hints; branches hold their parents' files, and
   accepted copies survive the parent and are never taken for it;
10. [Drafts and sealing](50-drafts.md): drafts may be rewritten or deleted,
   and nothing about any line changes;
11. [Use cases as theorems](60-patterns.md): the promises of the use cases
   (a journal issue does not change, a co-author's catalogue follows a
   paper, a withdrawal keeps what was vetted, only the owner adds to a
   member, a takedown is reported, a mirror is a receipt, a record deleted
   at the end of its retention), proved for every world;
12. [What cannot happen](65-impossible.md): breaks of the protocol, shown
   impossible or detected: a pin changing its meaning, history rewritten,
   identifiers reused, document versions ambiguous or with gaps, cycles of
   pins, a pin naming a key log, a withdrawal undone;
13. [What keys can do](66-security.md): the promises of sections 6.3 and
    15.1 about keys: only rotation keys of the version before decide a new
    version of a key log, so whoever holds current keys cannot block an
    exposure; a fork freezes the owner for ever; keys of the other side of
    a fork never count; signatures stay good and contested versions stay
    contested against a longer copy of the key log; rotation keys of the
    latest version take the owner over, and the owner's only answer is a
    fork; a retired key never exposed still signs;
14. [A story, checked by computation](70-story.md): three owners with key
   logs, a paper sealed and revised after a key rotation, a journal issue
   and accepted copy, a co-author's catalogue and mirror, a takedown and a
   draft, with the verifier's reports checked by `decide`; and attempts
   that fail: a signature that is not the owner's, a rewrite in place, a
   fresh pin into a line taken down, a reinstatement, a branch posing as
   its parent, bad member lists, a mirror that does not copy, a version
   signed with an exposed key, a key log changed with current keys, a fork
   that freezes the owner and makes contested, where it is known, the
   versions signed from the fork point on;
15. [Residual risks, checked by computation](72-risks.md): the residual
    risks of section 15.1 in the story's worlds: an archive served a key
    log without the exposure adds what the author's archive refuses; a
    thief's fork that exposes the owner's key makes the owner's own
    versions contested, and adds nothing; a retired key still signs; a
    takeover without a fork, and the owner's answering fork;
16. [A learning record, checked by computation](75-record.md): a student's
    thesis and the department's receipt of it, comments tied by a reference
    to the version commented on, a rewrite caught by the receipt, and the
    record deleted at the end of its retention;
17. [References between documents](80-references.md): pinned references
   from one document to an exact version of another (the proposals of
   issues #21 and #28): they are found and travel with copies, a pin fixes
   what its version refers to, a takedown behind a reference is invisible
   to a verifier that knows only the core; the use case of a short account
   and its detailed argument, computed;
18. [A reader's check](85-reader.md): what a reader that checks one copy of
    a line against one copy of its owner's key log knows, whatever host
    served them: the head is signed by a current key, which comes from the
    owner's genesis record through rotation keys, and the copy is the
    history the owner's keys signed, unless inventories collide: no host
    forges a version.

Each chapter writes one module of the library, `OpenSheaf/*.lean`. The code
is given in chunks, with the prose that explains it; the
[literate tools](https://github.com/opensheaf/literate) *tangle* the chunks
into the Lean files, which Lean then checks. The root of the library imports
every module:

    -- in OpenSheaf.lean:
    import OpenSheaf.Basic
    import OpenSheaf.Object
    import OpenSheaf.Archive
    import OpenSheaf.Owners
    import OpenSheaf.Lines
    import OpenSheaf.Collection
    import OpenSheaf.Worlds
    import OpenSheaf.Acts
    import OpenSheaf.Copies
    import OpenSheaf.Drafts
    import OpenSheaf.Patterns
    import OpenSheaf.Impossible
    import OpenSheaf.Security
    import OpenSheaf.Story
    import OpenSheaf.Risks
    import OpenSheaf.Record
    import OpenSheaf.References
    import OpenSheaf.Reader

## Modelling choices

The specification describes files on disk, JSON documents, signatures and
web servers. The model keeps only what the properties depend on.

- **Digests.** A digest is a value of an arbitrary type `D`, and the digest
  of an inventory is a function `hash` applied to what the inventory
  describes: the identifier and genesis record of the object, and its
  versions up to one. Most theorems hold for any function, even a constant
  one: immutability, for instance, does not rest on the strength of
  SHA-512, but on the fact that archives only ever add versions. The
  theorems about copies that come from anywhere, about tampering and about
  branches assume that the inventories they compare do not collide
  (`NoCollision`, [chapter 9](48-copies.md)); those about agreement of
  copies assume that the owner signs one history, every signature of its
  keys signing a prefix of it, and that no copy the world holds collides
  with that history (`OneHistory`). None assumes that `hash` is injective,
  which no real digest is: each assumes only that given pairs of
  inventories do not collide.
- **Signatures.** Which signature files verify is a fact of the
  environment (`Env.verifies`): a signature that verifies was made by
  someone holding its key. The model never assumes that only the owner
  holds its keys; theorems about thieves state which keys made the
  signatures that verify. Ed25519, `did:key` and the signed message are
  left out; so are timestamps, and with them the evidence that may date a
  signature before an exposure or a fork (section 7.3).
- **Names.** The names of a genesis record are given by a function of the
  environment, algorithm by algorithm (`Env.nameOf`); the model does not
  check which algorithm a branch takes after a clash (section 5.3), nor
  the rule on reused genesis records (section 5.4).
- **Choices on open questions.** Where the specification leaves a question
  open, the model makes a choice and says so: pins that must be found when they are made (or report
  `removed`, if carried over from a version already held); copies that may
  stop at any version (issue #39); branches that number their document
  versions from 1, the parent's number kept in `parent.documentVersion`
  (issue #57, departing also from the first sentence of section 9.4, which
  is not provisional); pinned references between documents (issues #21 and #28),
  which branches keep; the order in which a resolver tries the hints of a
  pin (section 12.3); a new version that keeps the branch point and the
  references of the head. Each is marked in its chapter.
- **Abstractions.** The description (`datacite.json`) is a string; files
  are pairs of a logical path and a digest; JSON, the OCFL layout, HTTP,
  the discovery document, indexes, keepers, profiles and extensions are
  left out, and so is the evidence of a branch point (section 9.2): the
  model carries the parent's signature files without checking them, and
  checks a branch point by resolving the parent, and compares branch
  points, and pins carried over, by what they name, not by their hints.
  Section 8.5's seven statuses of a member come down to four results,
  signatures being checked by the valid steps ([chapter 3](30-archive.md)).
  A valid step adds one version at a time, which must be signed directly
  (section 7.5 also lets a version vouched for by the next one come with
  it).
  The pins of the model are those of member lists, of references and of
  branch points; a pin carries its hints (`at`, `parent.url`). Revisions of
  a selection have no `documentVersion`. Returns of a line taken down
  (section 13.2) are left out, and so are takedowns of key logs (section
  13.2 allows them, of key logs other objects need only by law or at the
  keeper's request): a key log, once held, stays, and the owner's keys in a
  world are those of the key logs it holds.
- **Archives** are maps from object identifiers to objects or tombstones,
  with the owners they host, and the world is a map from locations to
  archives. Changes are the cases of one inductive relation, `Step`, so
  that a theorem about every change is a case analysis.

## An application: OpenSheaf as a sheaf

A second literate program in the same repository,
[OpenSheaf as a sheaf](https://opensheaf.org/opensheaf-lean/sheaf/), reads
the worlds of this model as sheaves: named document versions, ordered by
deposit, are the base, and each object version, wherever it is kept, is a
section. It proves that, in every world built by the events of this model,
the sections of all copies of a line glue into exactly one when its owner
signs one history, and that a fork of a line, which only the owner's keys
can make, is a failure of gluing.

## Building

Install Lean with [elan](https://github.com/leanprover/elan) and the
literate tools (`pip install -r requirements-literate.txt`), then

```
literate tangle   # write OpenSheaf/*.lean from these chapters
lake build        # check every proof
```

The model has no dependencies beyond Lean's standard library.
