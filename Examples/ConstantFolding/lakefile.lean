import Lake
open Lean Lake DSL

package «constant_folding» where
  builtinLint := true
  testDriver := "software_challenge/test_challenge"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.all, true⟩,
    ⟨`linter.missingDocs, false⟩,
    ⟨`linter.coreInternal, false⟩
  ]

require software_challenge from "../.."

@[default_target]
lean_lib «ConstantFolding» where
  roots := #[`ConstantFolding.Solution]
  globs := #[.submodules `ConstantFolding]
  precompileModules := true

@[default_target]
lean_exe «constant_folding» where
  root := `ConstantFolding.WorldCode

lean_lib «Challenge» where
  leanOptions := #[⟨`warn.sorry, false⟩]

@[default_target]
target audit pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallenge).map (fun _ => ())
