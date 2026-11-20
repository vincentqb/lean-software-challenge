import Lake
open Lean Lake DSL

package «constant_folding» where
  lintDriver := "software_challenge/lint"
  testDriver := "tests"
  leanOptions := #[⟨`autoImplicit, false⟩]

require software_challenge from git "https://github.com/vincentqb/lean-software-challenge" @ "main"

@[default_target]
lean_lib «ConstantFolding» where
  roots := #[`ConstantFolding.Solution]
  globs := #[.submodules `ConstantFolding]

lean_lib «Challenge» where
  leanOptions := #[⟨`warn.sorry, false⟩]

extern_lib «native» pkg := do
  let some adder ← findModule? `ConstantFolding.Native
    | error "ConstantFolding.Native is not a module of the package, so no library holds nativeAdd's code"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "native") #[← adder.oExport.fetch]

@[default_target]
lean_exe «constant_folding» where
  root := `ConstantFolding.Main

lean_exe «tests» where
  root := `ConstantFolding.Tests

@[default_target]
target statement pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallengeStatement).map (fun _ => ())
