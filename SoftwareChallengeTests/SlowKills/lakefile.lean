import Lake
open Lean Lake DSL

package «slow_kills» where
  builtinLint := true
  lintDriver := "software_challenge/lint_challenge"
  testDriver := "software_challenge/test_challenge"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.all, true⟩,
    ⟨`linter.missingDocs, false⟩,
    ⟨`linter.coreInternal, false⟩
  ]

require software_challenge from "../.."

@[default_target]
lean_lib «SlowKills» where
  roots := #[`SlowKills.Solution]
  globs := #[.submodules `SlowKills]

lean_lib «Challenge» where
  leanOptions := #[⟨`warn.sorry, false⟩]

@[default_target]
target statement pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())
