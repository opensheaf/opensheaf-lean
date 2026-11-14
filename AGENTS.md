# Working on this repository

A formal model of the OpenSheaf specification in Lean 4. The specification
and its discussion are in
[opensheaf/opensheaf.github.io](https://github.com/opensheaf/opensheaf.github.io)
(read its `AGENTS.md` and `.agents/skills/opensheaf-spec/` for the concepts).

- `lake build` must succeed with no errors, no warnings and no `sorry`.
- Each definition says which section of the specification it models; each
  module starts with a docstring saying what it proves.
- Model the specification as written. Proposals under discussion (such as
  #29) go in modules of their own, which say so and link the issue.
- Assume nothing about the digest function unless a statement needs it, and
  then as an explicit hypothesis.
- When the model shows that the specification is ambiguous or wrong, open an
  issue on the specification rather than choosing silently.
- Keep the table of the README up to date. Plain British English, as in the
  specification.
