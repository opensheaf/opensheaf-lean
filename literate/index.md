# OpenSheaf in Lean

This is a formal model of the
[OpenSheaf specification](https://opensheaf.org/) (version 0.1, a draft) in
[Lean 4](https://lean-lang.org/), written as a literate program. It defines
objects, object versions and document versions, archives, pins, catalogues
and selections, and the ways archives change. It then proves the properties
that the specification states in prose: that pins, once valid, stay valid;
that a takedown is detected; that a selection does not move unless its
curator moves it; and, for a proposal still under discussion, that drafts
can be rewritten without breaking any pin of a sealed version.

The model is **non-normative**. Where it and the specification differ, the
specification holds, and the difference is a bug of one or the other, to be
reported. Its purpose is to make the semantics precise, to find the
ambiguities and corner cases of the text, and to check design proposals
before they are written into the specification.

## How to read it

The chapters build the model from the bottom up:

1. [Basic notions](10-basic.md): identifiers, pins, member lists and object
   versions;
2. [Objects and their history](20-object.md): the history of an object,
   its inventories, and the counting of document versions;
3. [Archives and pins](30-archive.md): resolution of pins, the steps that
   change archives, immutability, and takedown;
4. [Catalogues and selections](40-collection.md): what updating a
   collection does to each kind;
5. [Draft, private and public](50-states.md): the proposal of issue #29,
   and what it guarantees.

Each chapter writes one module of the library, `OpenSheaf/*.lean`. The code
is given in chunks, with the prose that explains it; the
[literate tools](https://github.com/opensheaf/literate) *tangle* the chunks
into the Lean files, which Lean then checks. The root of the library imports
every module:

    -- in OpenSheaf.lean:
    import OpenSheaf.Basic
    import OpenSheaf.Object
    import OpenSheaf.Archive
    import OpenSheaf.Collection
    import OpenSheaf.States

## Modelling choices

The specification describes files on disk, JSON documents and web servers.
The model keeps only what the properties depend on.

- **Digests.** A digest is a value of an arbitrary type `D`, and the digest
  of an inventory is a function `hash` applied to the object versions it
  describes. No property of `hash` is assumed: every theorem below holds for
  any function, even a constant one. This is worth knowing. Immutability,
  for instance, does not rest on the strength of SHA-512: it rests on the
  fact that archives only ever add versions. Collision resistance is needed
  only for statements of the form "a pin that resolves fixes the content",
  and will then be an explicit hypothesis.
- **Abstractions.** The description (`datacite.json`) is a string; files
  are pairs of a logical path and a digest; JSON, the OCFL layout, HTTP and
  the discovery document are left out. The pins of the model are those of
  member lists.
- **Archives** are maps from object identifiers to objects or tombstones,
  and the world is a map from archive identifiers to archives. Changes are
  the cases of one inductive relation, `Step`, so that a theorem about every
  change is a case analysis.

## Building

Install Lean with [elan](https://github.com/leanprover/elan) and the
literate tools (`pip install -r requirements-literate.txt`), then

```
literate tangle   # write OpenSheaf/*.lean from these chapters
lake build        # check every proof
```

The model has no dependencies beyond Lean's standard library.
