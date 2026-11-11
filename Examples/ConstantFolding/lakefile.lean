import Lake
open Lean Lake DSL

package «constant_folding» where
  builtinLint := true
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
  root := `ConstantFolding.Shell

lean_lib «Challenge» where
  leanOptions := #[⟨`warn.sorry, false⟩]

lean_lib «Suites» where
  precompileModules := true

@[default_target]
target audit pkg : Unit := do
  return (← pkg.fetchFacetJob `softwareChallenge).map (fun _ => ())

@[test_driver] script test do
  let lake := (← getLake).toString
  for args in [#["build"], #["lint"], #["build", "Suites"], #["comparator"]] do
    let code ← (← IO.Process.spawn { cmd := lake, args, cwd := (← getRootPackage).dir }).wait
    unless code == 0 do return code
  return 0
