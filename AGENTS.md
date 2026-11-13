# Working on Lean Software Challenge

In `Examples/ConstantFolding/`, do not edit `Challenge.lean`, `owned.lock`,
`ConstantFolding/CoreSpec.lean`, or `ConstantFolding/WorldSpec.lean`; propose changes instead.
The build generates `comparator.json`.

Add an audit rule only if it makes a guarantee in `README.md` hold, or hold more strongly. Give
it a fixture in `SoftwareChallengeTests/` that it rejects, keep `layering_sound` proved, and
validate with `lake test`.

What no audit rule can decide: a statement says what its name says and does not restate the
implementation, a headline marked `@[terminates]` states that its hole returns, and a
`Check` exercises the claim it names.
