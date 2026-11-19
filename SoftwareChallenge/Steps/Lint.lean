module

public meta import SoftwareChallenge.Read
public meta import SoftwareChallenge.CoreCode.Rules.Lint
public meta import SoftwareChallenge.Steps.Statement

public section
meta section

open Lean

namespace SoftwareChallenge.Steps.Lint

def run (lakeFile : System.FilePath) : IO UInt32 := do
  let lake ← Read.loadLake lakeFile .lint
  let result := SoftwareChallenge.Lint.run (← Read.readFacts lake .lint)
  IO.println ("\n".intercalate result.report.toList)
  return result.code

def importers (lakeFile : System.FilePath) : IO UInt32 := do
  let lake ← Read.loadLake lakeFile .lint
  let some candidate := Read.challengeOf? lake | return 3
  let facts : Facts := { (default : Facts) with lake, challenge := Read.emptyChallenge candidate.module candidate.file }
  let lines ← challengeImports lake .lint
  if lines.isEmpty then return 3
  IO.println (errorListing (lines.map fun line => Report.item ((Lint.Error.importsChallenge line).message facts))
    "lake lint" .lint)
  return 1

def textLintSection (part : String) : Bool :=
  part.startsWith "-- Text linter diagnostics" || part.startsWith "Text linter diagnostics"

def environmentLinters (lake : LakeFacts) (lakeCommand : String) (targets : List String) : IO Bool := do
  let builtin ← IO.Process.output
    { cmd := lakeCommand, args := #["lint", "--builtin-only"] ++ targets.toArray, cwd := lake.packageDir }
  let sections := (builtin.stdout.splitOn "\n-- ").filter (!textLintSection ·)
  IO.print ("\n-- ".intercalate sections)
  IO.eprint builtin.stderr
  (← IO.getStdout).flush
  return builtin.exitCode == 0 || !(builtin.stderr.contains "error" ||
    sections.any fun part => part.startsWith "Found " || part.contains "error:")

def drive (lakeFile : System.FilePath) (targets : List String) : IO UInt32 := do
  let lake ← Read.loadLake lakeFile .lint
  let lakeCommand := (← IO.getEnv "LAKE").getD "lake"
  let clean ← environmentLinters lake lakeCommand targets
  let ran := (lakeFile.parent.getD ".") / "lint.ran"
  if ← ran.pathExists then IO.FS.removeFile ran
  discard <| (← IO.Process.spawn
    { cmd := lakeCommand, args := #["build", ":softwareChallenge"], cwd := lake.packageDir }).wait
  let status := (lakeFile.parent.getD ".") / "lint.status"
  let code ← if (← ran.pathExists) && (← status.pathExists) then
      pure (((← IO.FS.readFile status).trimAscii.toString.toNat?).getD 3).toUInt32
    else do
      IO.eprintln "lake lint could not build the package's modules, as printed above, so the audit did not run. Fix \
        each error above; when the linker reports a `multiple definition`, two modules define the same name, or two \
        executables define `main`, so rename one of them. Then run `lake lint`."
      pure 1
  unless clean do
    IO.eprintln "Lean's linters report the problems `lake lint --builtin-only` printed above, so the solution is not \
      clean. Fix each at the file and line it names, then run `lake lint`."
  return if clean || code == 3 then code else 1

end SoftwareChallenge.Steps.Lint
