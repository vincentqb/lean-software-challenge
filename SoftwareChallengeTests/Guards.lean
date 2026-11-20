import Lean
import SoftwareChallengeTests.Fixtures

namespace SoftwareChallengeTests

open Lean

def lineBudget : Nat := 3000

partial def leanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  (← dir.readDir).flatMapM fun entry => do
    if ← entry.path.isDir then leanFiles entry.path
    else return if entry.path.extension == some "lean" then #[entry.path] else #[]

def libraryFiles (lsc : System.FilePath) : IO (Array System.FilePath) := do
  return #[lsc / "lakefile.lean", lsc / "SoftwareChallenge.lean", lsc / "SoftwareChallengeRun.lean"] ++
    (← leanFiles (lsc / "SoftwareChallenge"))

def lineCount (files : Array System.FilePath) : IO Nat :=
  files.foldlM (fun total file => return total + ((← IO.FS.readFile file).splitOn "\n").length - 1) 0

def withinBudget (lsc : System.FilePath) : ExceptT String IO Unit := do
  let lines ← lineCount (← libraryFiles lsc)
  unless lines ≤ lineBudget do
    throw s!"the library has {lines} lines, over the budget of {lineBudget}, so it no longer serves only T1–T5"

def isLibrary (module : Name) : Bool :=
  module.getRoot == `SoftwareChallenge || module == `SoftwareChallengeRun

def entryPoint (env : Environment) (info : ConstantInfo) : Bool :=
  info.name == `main || info.name == `SoftwareChallenge.runTests || isIOUnitInitFn env info.name ||
    (getInitFnNameFor? env info.name).isSome ||
    [``Lean.Elab.Term.TermElab, ``Lean.ParserDescr, ``Lean.TrailingParserDescr].any info.type.isConstOf

def reached (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | continue
    pending := pending ++ info.type.getUsedConstants ++
      ((info.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[] ++ (getInitFnNameFor? env name).toArray ++
      #[Compiler.mkUnsafeRecName name] ++ (Compiler.getImplementedBy? env name).toArray
    if let .inductInfo induct := info then pending := pending ++ induct.ctors
  return seen

def written (env : Environment) (name : Name) : IO Bool := do
  let rangesOf := fun (name : Name) => (findDeclarationRanges? name : CoreM _).toIO { fileName := "", fileMap := default } { env }
  let (ranges, _) ← rangesOf name
  let (parent, _) ← rangesOf name.getPrefix
  return ranges.any fun ranges => ranges.range != ranges.selectionRange && parent.all (·.range != ranges.range)

def checked (env : Environment) : ConstantInfo → Bool
  | .defnInfo info | .opaqueInfo info | .axiomInfo info | .inductInfo info | .thmInfo info =>
    !info.name.isInternalDetail && !env.isProjectionFn info.name
  | _ => false

def unreachedIn (roots : Array Name) (tests : Name → Bool) : IO (Array Name × NameSet) := do
  unsafe enableInitializersExecution
  let env ← importModules (roots.map ({ module := · })) {} (loadExts := true)
  let declared := env.constants.toList.filterMap fun (name, info) =>
    (env.getModuleIdxFor? name).bind fun index =>
      if checked env info then some (env.header.moduleNames[index.toNat]!, info) else none
  let library ← (declared.filter fun (module, _) => isLibrary module).filterM fun (_, info) => written env info.name
  let roots := env.constants.toList.filterMap fun (name, info) => (env.getModuleIdxFor? name).bind fun index =>
    let module := env.header.moduleNames[index.toNat]!
    if tests module || isLibrary module && entryPoint env info then some name else none
  let seen := reached env roots.toArray
  return ((library.filter fun (_, info) => !seen.contains info.name).map (·.2.name) |>.toArray, seen)

def noDeadCode : ExceptT String IO Unit := do
  let tests := fun (module : Name) => module.getRoot == `SoftwareChallengeTests
  let (steps, stepsSeen) ← unreachedIn #[`SoftwareChallengeRun, `SoftwareChallengeTests.Suite] tests
  let (grade, gradeSeen) ← unreachedIn #[`SoftwareChallenge.Grade] tests
  let dead := (steps.filter (!gradeSeen.contains ·)) ++ (grade.filter (!stepsSeen.contains ·))
  unless dead.isEmpty do
    throw s!"no entry point or test reaches {dead.toList}, so they serve none of T1–T5; delete them"

def onePerRule (rule : InductiveVal) : ExceptT String IO Unit := do
  let counts := (List.range rule.ctors.length).map fun index =>
    (rule.ctors[index]!, (fixtures.filter (·.rule.ctorIdx == index)).length)
  let wrong := counts.filter (·.2 != 1)
  unless wrong.isEmpty do throw s!"each rule needs exactly one fixture, but these have another count: {wrong}"

end SoftwareChallengeTests
