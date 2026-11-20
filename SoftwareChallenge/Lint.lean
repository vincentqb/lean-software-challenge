import SoftwareChallenge.Statement

namespace SoftwareChallenge

open Lean Meta

def callees (env : Environment) (info : ConstantInfo) : Array Name :=
  let compiled := if info matches .opaqueInfo _ then (env.find? (Compiler.mkUnsafeRecName info.name)).getD info else info
  ((compiled.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[] ++
    (Compiler.getImplementedBy? env info.name).toArray

def reach (plan : Plan) (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut pending := roots
  let mut reached : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    let some info := env.find? name | continue
    if reached.contains name || info.isTheorem || !plan.inPackage env name then continue
    reached := reached.insert name
    pending := pending ++ callees env info
  return reached

def isUnsafeTerm (env : Environment) (name : Name) : CoreM Bool := do
  return (env.find? name).any (· matches .opaqueInfo _) && !(← isWritten name) &&
    (Compiler.getImplementedBy? env name).any fun impl => (env.find? impl).any (·.isUnsafe)

def impurity (env : Environment) (foreign withUnsafeTerm : Array Name) (info : ConstantInfo) : Option String :=
  if isExtern env info.name then if foreign.contains info.name then none else some "@[extern]"
  else if (Compiler.getImplementedBy? env info.name).isSome then some "@[implemented_by]"
  else if info.isUnsafe || withUnsafeTerm.contains (privateToUserName info.name) then some "unsafe"
  else if info matches .opaqueInfo _ && (env.find? (Compiler.mkUnsafeRecName info.name)).any (·.isPartial) then
    some "partial"
  else none

structure Stated where
  kind : String
  info : ConstantInfo
  place : String

def lintProblem (rule : Rule) (place what why fix : String) : Problem :=
  { rule, place, what, why, fix, next := "lake lint" }

def declaredAs : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | _ => "constant"

def standing (plan : Plan) (permitted : Array Name) (stated : Stated) : MetaM (Option Problem) := do
  let name := stated.info.name
  let some found := (← getEnv).find? name | return some (lintProblem .pending stated.place
    s!"{stated.kind} {name} is not in {plan.solution} or a module it imports" "so the comparator cannot check it"
    s!"Declare {name} : `{← shown stated.info.type}` there, as {stated.place} states it")
  let place ← plan.place name
  if declaredAs found != declaredAs stated.info || found.levelParams != stated.info.levelParams ||
      Shape.ofExpr found.type != Shape.ofExpr stated.info.type then
    return some (lintProblem .pending place s!"{stated.kind} {name} is the {declaredAs found} `{← shown found.type}`"
      s!"so it is not the {declaredAs stated.info} `{← shown stated.info.type}` of {stated.place}"
      s!"State it exactly as {stated.place} does")
  if stated.info.isAxiom then return none
  let axioms ← collectAxioms name
  if axioms.contains ``sorryAx then
    return some (lintProblem .pending place s!"{stated.kind} {name} uses sorry" "so it is not proved yet"
      "Replace each sorry it relies on with a proof or a definition")
  let allowed := if stated.kind == "consistency theorem" then standardAxioms else permitted
  return (axioms.find? (!allowed.contains ·)).map fun used => lintProblem .axiomUsed place
    s!"{stated.kind} {name} uses the axiom {used}"
    (if permitted.contains used then "so it does not show that the world claims can hold without assuming them"
      else "which comparator.json does not permit, so the comparator rejects it")
    s!"Prove it without {used}, which `#print axioms {name}` traces"

def purity (plan : Plan) (challenge : Challenge) (checked : NameSet) (hole : Name) : MetaM (Array Problem × NameSet) := do
  let env ← getEnv
  unless env.contains hole do return (#[], checked)
  let reached := reach plan env #[hole]
  let withUnsafeTerm := (← reached.toArray.filterM (isUnsafeTerm env ·)).map (privateToUserName · |>.getPrefix)
  let impure ← ((reached.toArray.filter (!checked.contains ·)).qsort Name.lt).filterMapM fun name => do
    let some info := env.find? name | return none
    let some reason := impurity env challenge.foreign withUnsafeTerm info | return none
    unless ← isWritten name do return none
    return some (lintProblem .impure (← plan.place name) s!"{name}, which hole {hole} computes through, is {reason}"
      "so the program does not run the Lean definition that the proofs are about"
      s!"Define {name} in plain Lean, without {reason}")
  let checked := reached.foldl NameSet.insert checked
  unless (Elab.PartialFixpoint.eqnInfoExt.find? env hole).isSome && !challenge.terminates.any (·.2 == hole) do
    return (impure, checked)
  return (·, checked) <| impure.push <| lintProblem .fixpoint (← plan.place hole)
    s!"hole {hole} is a partial_fixpoint without a @[terminates {hole}] headline" "so nothing shows that it returns"
    s!"Define it by structural or well-founded recursion, or have Challenge state a `@[terminates {hole}]` headline"

def reachedFromMain (plan : Plan) (module : Name) : IO (Environment × NameSet) := do
  let env ← importEnv module
  return (env, reach plan env #[`main])

def unreached (plan : Plan) (challenge : Challenge) (program : Name) : IO (Array Problem) := do
  let (env, reached) ← reachedFromMain plan program
  let place ← inEnv env (plan.place `main)
  return (challenge.holes.filter (!reached.contains ·)).map fun hole => lintProblem .unreached place
    s!"the main of {program} does not reach hole {hole}" "so the program does not run the code that is proved"
    s!"Make main compute through {hole}"

def untested (plan : Plan) (claims : Array Stated) : IO (Array Problem) := do
  let tested ← match plan.tests with
    | some root => do
      let (env, reached) ← reachedFromMain plan root
      pure ((links env .tests).filter (reached.contains ·.1))
    | none => pure #[]
  let runner := (plan.tests.map toString).getD "the lean_exe that testDriver names"
  return (claims.filter fun claim => !tested.any (·.2 == claim.info.name)).map fun claim =>
    lintProblem .untested claim.place s!"world claim {claim.info.name} has no test that `lake test` runs"
      "so nothing checks that the native code satisfies it"
      s!"Add `@[tests {claim.info.name}] def … : IO Unit` to a module of {runner}, whose main is \
        `SoftwareChallenge.testsMain`"

def listing (title : String) (problems : Array Problem) : Array String :=
  if problems.isEmpty then #[] else #[s!"{title}: {problems.size}"] ++ problems.map ("  " ++ ·.render)

def lintStep (plan : Plan) : IO UInt32 := do
  let (challenge, stated) ← inEnv (← importEnv plan.challenge.module) do
    let challenge ← Challenge.read plan
    let stated := fun (kind : String) (names : Array Name) => names.mapM fun name => do
      return { kind, info := ← getConstInfo name, place := ← plan.place name : Stated }
    return (challenge, (← stated "headline" challenge.headlines) ++ (← stated "kill" (challenge.kills.map (·.1))) ++
      (← stated "witness" challenge.witnesses) ++ (← stated "consistency theorem" challenge.consistent) ++
      (← stated "hole" challenge.holes) ++ (← stated "world claim" challenge.claims))
  let (standings, impure) ← inEnv (← importEnv plan.solution) do
    let (impure, _) ← challenge.holes.foldlM (init := (#[], {})) fun (impure, checked) hole => do
      let (found, checked) ← purity plan challenge checked hole
      return (impure ++ found, checked)
    return (← stated.mapM (standing plan (standardAxioms ++ challenge.claims)), impure)
  let problems := standings.filterMap id ++ impure ++ (← plan.programs.flatMapM (unreached plan challenge)) ++
    (← untested plan (stated.filter (·.kind == "world claim")))
  let errors := problems.filter (·.rule != .pending)
  let pending := problems.filter (·.rule == .pending)
  let proved := [("headline", "headlines"), ("kill", "kills"), ("witness", "witnesses"),
    ("consistency theorem", "consistency theorems")].filterMap fun (kind, plural) =>
    let counted := (stated.zip standings).filter (·.1.kind == kind)
    if counted.isEmpty then none else some s!"{(counted.filter (·.2.isNone)).size} of {counted.size} {plural}"
  IO.println ("\n".intercalate (listing "Errors" errors ++ listing "Pending" pending ++
    #["Proved: " ++ ", ".intercalate proved]).toList)
  return if !errors.isEmpty then 1 else if !pending.isEmpty then 2 else 0

end SoftwareChallenge
