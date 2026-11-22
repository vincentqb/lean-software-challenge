import SoftwareChallenge.Plan
import SoftwareChallenge.Problem

namespace SoftwareChallenge

open Lean Meta

structure Challenge where
  holes : Array Name
  headlines : Array Name
  kills : Array (Name × Name)
  witnesses : Array (Name × Name)
  consistent : Array Name
  terminates : Array (Name × Name)
  claims : Array Name
  foreign : Array Name

def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def declaredIn (module : Name) : MetaM (Array ConstantInfo) := do
  let env ← getEnv
  let some index := env.getModuleIdx? module | return #[]
  let found := env.header.moduleData[index.toNat]!.constNames.filterMap env.find?
  let lines ← found.mapM (lineOf ·.name)
  return ((found.zip lines).qsort (·.2 < ·.2)).map (·.1)

def isHole : ConstantInfo → Bool
  | .defnInfo info => info.value.hasSorry
  | _ => false

def Challenge.read (plan : Plan) : MetaM Challenge := do
  let env ← getEnv
  let module := plan.challenge.module
  let written ← (← declaredIn module).filterM (isWritten ·.name)
  let here := fun (kind : LinkKind) => (links env kind).filter (moduleOf env ·.1 == module)
  let marked := (here .kills ++ here .witness ++ here .consistent).map (·.1)
  let owned ← (env.header.moduleNames.filter plan.owns).flatMapM declaredIn
  return {
    holes := (written.filter isHole).map (·.name)
    headlines := (written.filter fun info => info.isTheorem && !marked.contains info.name).map (·.name)
    kills := here .kills
    witnesses := here .witness
    consistent := (here .consistent).map (·.1)
    terminates := here .terminates
    claims := (owned.filter (·.isAxiom)).map (·.name)
    foreign := (owned.filter (isExtern env ·.name)).map (·.name) }

def Challenge.targets (challenge : Challenge) : Array Name :=
  challenge.headlines ++ challenge.kills.map (·.1) ++ challenge.witnesses.map (·.1) ++ challenge.consistent

def typeOf (name : Name) : MetaM Expr := return (← getConstInfo name).type

def killTemplate (holes : Array Name) (headline : Expr) : MetaM String := do
  let mut wrong := headline
  for hole in holes do
    if let some (.const _ levels) := headline.find? (·.isConstOf hole) then
      let value ← mkFreshExprMVar (← inferType (.const hole levels)) (userName := .mkSimple s!"wrong_{hole.getString!}")
      wrong := wrong.replace fun expr => if expr.isConstOf hole then some value else none
  shown (mkNot wrong)

def witnessTemplate (holes : Array Name) (headline : Expr) : MetaM (Option Expr) :=
  forallTelescope headline fun binders conclusion => do
    let hypotheses := if conclusion.isFalse then binders.pop else binders
    let aboutHoles ← hypotheses.filterM fun binder => do
      let type ← inferType binder
      return type.getUsedConstants.any holes.contains && (← isProp type)
    let some last := aboutHoles.back? | return none
    withNewBinderInfos (binders.map (·.fvarId!, .default)) do
      some <$> (binders.takeWhile (· != last)).foldrM (init := ← inferType last) fun binder body => do
        mkAppM ``Exists #[← mkLambdaFVars #[binder] body]

partial def asExported (expr : Expr) : Expr :=
  expr.replace fun
    | .mdata _ inner => some (asExported inner)
    | .letE name type value body _ => some (.letE name (asExported type) (asExported value) (asExported body) false)
    | _ => none

partial def existsModels (claims : Array Expr) : List Name → Array (Name × Expr) → MetaM Expr
  | [], bound => return mkAndN (claims.map (replaceBound bound)).toList
  | name :: rest, bound => do
    let type := replaceBound bound (asExported (← typeOf name))
    withLocalDeclD (.mkSimple name.getString!) type fun model => do
      mkAppM ``Exists #[← mkLambdaFVars #[model] (← existsModels claims rest (bound.push (name, model)))]
where
  replaceBound (bound : Array (Name × Expr)) (expr : Expr) : Expr :=
    expr.replace fun | .const name _ => (bound.find? (·.1 == name)).map (·.2) | _ => none

def Challenge.consistency (challenge : Challenge) : MetaM Expr := do
  let claims ← challenge.claims.mapM typeOf
  existsModels claims (challenge.foreign.filter fun name => claims.any (·.getUsedConstants.contains name)).toList #[]

def sameStatement (expected : Expr) (name : Name) : MetaM Bool :=
  return asExported (← typeOf name) == asExported expected

def replacements (holes : Array Name) : Expr → Expr → Array (Name × Expr) → Array (Name × Expr)
  | .const name _, value, found =>
    if holes.contains name && !value.isConstOf name && !found.any (·.1 == name) then found.push (name, value) else found
  | .app f a, .app g b, found => replacements holes a b (replacements holes f g found)
  | .lam _ t b _, .lam _ u c _, found | .forallE _ t b _, .forallE _ u c _, found =>
    replacements holes b c (replacements holes t u found)
  | .letE _ t v b _, .letE _ u w c _, found =>
    replacements holes b c (replacements holes v w (replacements holes t u found))
  | .proj _ _ v, .proj _ _ w, found => replacements holes v w found
  | _, _, found => found

def rejects (holes : Array Name) (headline kill : Expr) : MetaM Bool := do
  let headline := asExported headline
  let some rejected := (asExported kill).not? | return false
  let found := replacements holes headline rejected #[]
  if found.isEmpty || found.any (·.2.hasLooseBVars) then return false
  let wrong := headline.replace fun | .const name _ => (found.find? (·.1 == name)).map (·.2) | _ => none
  withReducible (isDefEq wrong rejected)

def statementProblems (plan : Plan) (challenge : Challenge) : MetaM (Array Problem) := do
  let problem := fun (rule : Rule) (name : Name) (what why fix : String) => do
    return { rule, place := ← plan.place name, what, why, fix, next := "lake build" : Problem }
  let mut problems := #[]
  for headline in challenge.headlines do
    unless challenge.kills.any (·.2 == headline) do
      let type ← typeOf headline
      let fix ← if type.getUsedConstants.any challenge.holes.contains then
          pure s!"Add `@[kills {headline}] theorem {headline.getString!}_rejects : \
            {← killTemplate challenge.holes type} := by sorry`, with each ?wrong_ a wrong closed term"
        else pure s!"State {headline} about a hole, since a kill replaces holes, or make it a lemma of an owned module"
      problems := problems.push (← problem .kill headline s!"headline {headline} has no kill"
        "so nothing shows that it rejects a wrong implementation" fix)
  for (kill, headline) in challenge.kills do
    unless challenge.headlines.contains headline && (← rejects challenge.holes (← typeOf headline) (← typeOf kill)) do
      let wanted ← if challenge.headlines.contains headline then killTemplate challenge.holes (← typeOf headline)
        else pure s!"¬ <a headline with its holes replaced>"
      problems := problems.push (← problem .killShape kill s!"kill {kill} does not negate headline {headline} \
        with holes replaced by closed terms" "so it does not show that the headline rejects a wrong implementation"
        s!"State it as `{wanted}`, with each ?wrong_ a wrong closed term, and name a headline in @[kills]")
  for headline in challenge.headlines do
    let some witness ← witnessTemplate challenge.holes (← typeOf headline) | continue
    unless challenge.witnesses.any (·.2 == headline) do
      problems := problems.push (← problem .witness headline s!"headline {headline} has no witness"
        "so nothing shows that its hypotheses about a hole can hold" s!"Add `@[witness {headline}] theorem \
          {headline.getString!}_applies : {← shown witness} := by sorry`")
  for (witness, headline) in challenge.witnesses do
    unless challenge.headlines.contains headline do
      problems := problems.push (← problem .witness witness s!"@[witness {headline}] marks {witness}, but \
        {headline} is not a headline" "so it shows nothing about any headline's hypotheses"
        s!"Name in @[witness] the headline whose hypotheses {witness} meets")
  if !challenge.claims.isEmpty then
    let expected ← challenge.consistency
    let wrong ← challenge.consistent.filterM fun name => return !(← sameStatement expected name)
    if challenge.consistent.isEmpty || !wrong.isEmpty then
      problems := problems.push (← problem .consistent (wrong[0]?.getD challenge.claims[0]!) s!"no @[consistent] \
        theorem states `{← shown expected}`" "so nothing shows that the world claims can hold together"
        s!"State `@[consistent] theorem world_consistent : {← shown expected} := by sorry` in place of any other \
          @[consistent] theorem")
  for (headline, hole) in challenge.terminates do
    unless challenge.headlines.contains headline && challenge.holes.contains hole &&
        (← typeOf headline).getUsedConstants.contains hole do
      problems := problems.push (← problem .terminates headline s!"@[terminates {hole}] marks {headline}, which is \
        not a headline that mentions hole {hole}" "so nothing shows that the hole returns"
        s!"Put @[terminates {hole}] on a headline of Challenge that states {hole} returns")
  return problems

def comparatorConfig (plan : Plan) (challenge : Challenge) : MetaM Json := do
  let targets ← challenge.targets.mapM fun name => return (name, ← lineOf name)
  return Json.mkObj [("challenge_module", toJson plan.challenge.module), ("solution_module", toJson plan.solution),
    ("theorem_names", toJson ((targets.qsort (·.2 < ·.2)).map (·.1))), ("definition_names", toJson challenge.holes),
    ("permitted_axioms", toJson (standardAxioms ++ challenge.claims))]

def statementStep (plan : Plan) : IO UInt32 := do
  inEnv (← importEnv plan.challenge.module) do
    let challenge ← Challenge.read plan
    let problems ← statementProblems plan challenge
    for problem in problems do IO.println problem.render
    unless problems.isEmpty do return 1
    IO.FS.writeFile (System.FilePath.mk plan.packageDir / "comparator.json") (← comparatorConfig plan challenge).pretty
    return 0

end SoftwareChallenge
