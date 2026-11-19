# Working on Lean Software Challenge

The specification is Lean: the definitions in `SoftwareChallenge/CoreSpec/` (each step's `Complete`
and `Clean`, and the role tables), the headlines of `SoftwareChallengeStatement/Challenge.lean`, and
the fixtures in `SoftwareChallengeTests/` and `SoftwareChallengeReadTests/`. README.md is only the
list of steps.

In `Examples/ConstantFolding/`, the template, do not edit `Challenge.lean`, `owned.lock`,
`ConstantFolding/CoreSpec.lean`, or `ConstantFolding/WorldSpec.lean`; propose changes instead. The
template requires `software_challenge` from git; to run it against this checkout, point it here
with `.lake/package-overrides.json`, as `SoftwareChallengeTests/Gate.lean` does.

- An audit rule must make a CoreSpec condition hold, or hold more strongly. Give a pure rule a facts
  value it rejects in `SoftwareChallengeTests/`, and give a new kind of fact a source fixture in
  `SoftwareChallengeReadTests/`. Keep every theorem proved, validate with
  `lake build && lake lint && lake test`, and run `lake test -- full` after landing.
- Each step runs only what it owns; only `grade` composes them. A challenge in progress must build:
  a headline not proved yet is pending, not an error. Never accept `sorry` or an axiom beyond the
  standard ones.
- Every message names the declaration, file, and line, says why in one clause, gives the exact fix,
  and the command to run next.
- Names and structure carry the meaning. No comments or doc comments in Lean code, except each
  `WorldClaim`'s required doc comment and each challenge's statement of what is and is not claimed.

What no audit rule can decide: a statement says what its name says and does not restate the
implementation, a headline marked `@[terminates]` states that its hole returns, and a `Check`
exercises the claim it names.
