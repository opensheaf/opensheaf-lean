# Instructions for agents (and people)

A formal model of the OpenSheaf specification in Lean 4, written as a
literate program. The specification and its discussion are in
[opensheaf/opensheaf.github.io](https://github.com/opensheaf/opensheaf.github.io)
(read its `AGENTS.md` and `.agents/skills/opensheaf-spec/` for the concepts).

## Two literate programs

The repository holds two documents, each a literate program:

- **the model**: chapters in `literate/`, configured by `literate.json`,
  tangled into `OpenSheaf.lean` and `OpenSheaf/*.lean`;
- **OpenSheaf as a sheaf**, an application of the model: chapters in
  `literate-sheaf/`, configured by `literate-sheaf/literate.json`, tangled
  into `Sheaf.lean` and `Sheaf/*.lean`. It adds no rule to the model and
  only reads its worlds as sheaves; facts about OpenSheaf that it needs and
  the model lacks belong in the model when they are more than lemmas.

The site (`.github/workflows/pages.yml`) weaves the model into `model/`,
the sheaf into `sheaf/`, puts `landing/index.html` (a plain file, edited
directly) at the top, and redirects the model's former page addresses to
`model/`.

The Markdown chapters are the source; the Lean files are **tangled** out of
them and must never be edited directly.

Every tangled file starts with a notice "Generated from literate/... by
opensheaf-literate"; `literate tangle --list` lists them. To change them,
edit the chapter that defines the code (`literate tangle --where FILE:LINE`
tells which chapter and line a line comes from), explaining the change in
the prose, then run

    pip install -r requirements-literate.txt   # once: the pinned literate tools
    literate tangle                            # write the model's files
    literate tangle literate-sheaf/*.md        # write the sheaf's files
    literate tangle --check                    # they are what the chapters say
    literate tangle --check literate-sheaf/*.md
    lake build --wfail                         # check every proof

Run both from the top of the repository, so that the notices name the
chapters by their paths. Weave the sheaf from its folder, which holds its
configuration: `cd literate-sheaf && literate weave --out ../site/sheaf`.

Code blocks indented by four spaces are tangled: an indented block after
prose continues the chunk of the chapter. Commands and other illustrations
go in fenced blocks.

Plain files, edited directly: `README.md`, `AGENTS.md`, `literate.json`,
`literate-sheaf/literate.json`, `landing/index.html`, `lakefile.toml`,
`lean-toolchain`, `requirements-literate.txt`, `.github/workflows/*`.

## The model

- `lake build --wfail` must succeed: no errors, no warnings, no `sorry`.
- Each definition says which section of the specification it models; each
  chapter says what it proves, and why, in prose.
- Model the specification as written. Proposals under discussion (such as
  #29) go in chapters and namespaces of their own, which say so and link the
  issue.
- Assume nothing about the digest function unless a statement needs it, and
  then as an explicit hypothesis.
- When the model shows that the specification is ambiguous or wrong, open an
  issue on the specification rather than choosing silently.
- Keep the table of the README up to date. Plain British English, as in the
  specification.
