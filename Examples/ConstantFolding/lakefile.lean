import Lake
open Lean Lake DSL

package «constant_folding» where
  lintDriver := "software_challenge/lint_challenge"
  testDriver := "software_challenge/test_challenge"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`linter.all, true⟩,
    ⟨`linter.missingDocs, false⟩,
    ⟨`linter.coreInternal, false⟩
  ]

require software_challenge from git "https://github.com/vincentqb/lean-software-challenge" @ "main"

@[default_target]
lean_lib «ConstantFolding» where
  roots := #[`ConstantFolding.Solution]
  globs := #[.submodules `ConstantFolding]

extern_lib «native» pkg := do
  let some adder ← findModule? `ConstantFolding.WorldSpec.NativeAdd
    | error "ConstantFolding.WorldSpec.NativeAdd is not a module of the package, so no library holds nativeAdd's code"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "native") #[← adder.oExport.fetch]

@[default_target]
lean_exe «constant_folding» where
  root := `ConstantFolding.WorldCode

lean_lib «Challenge» where
  leanOptions := #[⟨`warn.sorry, false⟩]

@[default_target]
target statement pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())
