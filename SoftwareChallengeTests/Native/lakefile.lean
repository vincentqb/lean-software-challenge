import Lake
open Lean Lake DSL

package «native_checks» where
  testDriver := "software_challenge/test_challenge"
  leanOptions := #[⟨`autoImplicit, false⟩]

require software_challenge from git "https://github.com/vincentqb/lean-software-challenge" @ "main"

@[default_target]
lean_lib «Native» where
  globs := #[.submodules `Native]

extern_lib «native» pkg := do
  let some twice ← findModule? `Native.WorldSpec.Twice
    | error "Native.WorldSpec.Twice is not a module of the package, so no library holds the C of Native.twice"
  let native ← buildO (pkg.buildDir / "native" / "twice.o") (← inputTextFile (pkg.dir / "c" / "twice.c")) #["-fPIC"]
    (compiler := ← getLeanCc)
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "native") #[← twice.oExport.fetch, native]
