# Working on Lean Software Challenge

The specification is Lean: the theorems in `SoftwareChallenge/` and the fixtures in
`SoftwareChallengeTests/`. README.md is only the list of steps.

In `Examples/ConstantFolding/`, the template, do not edit `Challenge.lean`, `owned.lock`,
`ConstantFolding/CoreSpec.lean`, or `ConstantFolding/WorldSpec.lean`; propose changes instead.

- Every audit rule has a fixture in `SoftwareChallengeTests/` that it rejects. Keep every theorem
  proved, and validate with `lake test`.
- Each step runs only what it owns; only `grade` composes them. A challenge in progress must build:
  a headline not proved yet is pending, not an error. Never accept `sorry` or an axiom beyond the
  standard ones.
- Every message names the declaration, file, and line, says why in one clause, gives the exact fix,
  and the command to run next.
- Names and structure carry the meaning. No comments or doc comments in Lean code, except each
  WorldClaim's doc comment and the template challenge's module doc.
