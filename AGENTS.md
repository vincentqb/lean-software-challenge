# Working on Lean Software Challenge

The library is the audit, the commands (`WorldClaim`, `Check`, `@[kills]`, `@[terminates]`,
`@[witness]`), the `softwareChallengeStatement` facet that `lake build` runs through the
`statement` target and that writes `comparator.json`, the lint and test drivers `lint_challenge`
and `test_challenge`, the `replay` script, and `lake exe grade`. `README.md` states what each step guarantees; keep it true, and
change it in the same commit as any behavior it describes.

In `Examples/ConstantFolding/`, the template, do not edit `Challenge.lean`, `owned.lock`,
`ConstantFolding/CoreSpec.lean`, or `ConstantFolding/WorldSpec.lean`; propose changes instead.

- An audit rule must make a guarantee in `README.md` hold, or hold more strongly. Give it a
  fixture in `SoftwareChallengeTests/` that it rejects, keep `layering_sound` proved, and validate
  with `lake test`, whose matrix in `.lake/build/grade.md` shows which step refuses each mutant. A
  mutant shows what no fixture can: a guarantee end to end, or steps that disagree.
- Each step runs only what it owns; only `grade` composes them. The audit checks structure and
  reports status; acceptance is `grade`. A challenge in progress must build: a headline the
  solution does not prove yet is reported, not an error. Never let the audit accept `sorry` or an
  axiom beyond the standard ones.
- Every message about a declaration names it with its file and line; every message says why it
  matters in one clause, gives the exact fix, and the command to run next.
- Names and structure carry the meaning. Write no comments or doc comments in Lean code, except
  each `WorldClaim`'s required doc comment and the template challenge's statement of what is and is
  not claimed.

What no audit rule can decide: a statement says what its name says and does not restate the
implementation, a headline marked `@[terminates]` states that its hole returns, and a `Check`
exercises the claim it names.
