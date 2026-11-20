# Working on Lean Software Challenge

- The specification is Lean: `SoftwareChallenge/CoreSpec/`, the headlines of
  `SoftwareChallengeStatement/Challenge.lean`, and the fixtures in `SoftwareChallengeTests/` and
  `SoftwareChallengeReadTests/`.
- In `Examples/ConstantFolding/`, do not edit `Challenge.lean`, `owned.lock`,
  `ConstantFolding/CoreSpec.lean`, or `ConstantFolding/WorldSpec.lean`; propose changes instead.
- Give every rule a fixture it rejects.
- Validate with `lake build && lake lint && lake test`, and run `lake test -- full` after landing.
- Every message names the declaration, file, and line, says why in one clause, gives the exact fix,
  and the command to run next.
- Names and structure carry the meaning: no comments or doc comments in Lean code, except each
  `WorldClaim`'s doc comment and each challenge's statement of what is and is not claimed.
