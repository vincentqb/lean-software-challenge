# Working on Lean Software Challenge

Do not edit `Challenge.lean`, `comparator.json`, `Audit.lean`,
`Examples/ConstantFolding/Spec.lean`, or `Examples/ConstantFolding/Boundary.lean`; propose
changes instead.

Add a check only if it makes a guarantee in `README.md` hold, or hold more strongly. Give it a
fixture in `SoftwareChallengeTests/` that it rejects, keep `layering_sound` proved, and validate
with `lake test`.

What no check can decide: a statement says what its name says and does not restate the
implementation, a headline listed under `terminates` states that its hole returns, and
`@[exercises]` marks only suites that exercise their claim.
