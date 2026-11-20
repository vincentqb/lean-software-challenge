# Working on Lean Software Challenge

- LSC guarantees five theorems about an accepted package and nothing else: T1 proved, T2 runs as
  proved, T3 assumptions named and tested, T4 meaningful, T5 statement fixed. Every line of the
  library serves one of them.
- LSC assumes well-intentioned agents, so its rules and reviews target honest mistakes, not forgery.
- In `Examples/ConstantFolding/`, do not edit `Challenge.lean`, `ConstantFolding/Expr.lean`
  or `ConstantFolding/Native.lean`;
  propose changes instead.
- Every rule is a constructor of `SoftwareChallenge.Rule` with exactly one fixture in
  `SoftwareChallengeTests/Fixtures.lean`, which it rejects with its message.
- Validate with `lake build && lake lint && lake test`.
- Every message names the declaration, file, and line, says why it matters in one clause, gives the
  exact fix, and the command to run next.
- Names and structure carry the meaning: no comments or doc comments in Lean code, except the
  challenge's module doc.
