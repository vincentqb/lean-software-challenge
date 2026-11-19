module

public meta import Lean
public meta import SoftwareChallenge.Commands
public meta import SoftwareChallenge.CoreCode.Facts
public meta import SoftwareChallenge.CoreCode.Classify
public meta import SoftwareChallenge.Read.Source
public meta import SoftwareChallenge.Read.Constants
public meta import SoftwareChallenge.Read.Inventory

public section
meta section

open Lean Meta

namespace SoftwareChallenge.Read

def matchBudget : Nat := 200000

def matchWithin (budget : Nat) (expected statement : Expr) : MetaM MatchOutcome := do
  let env ← getEnv
  unless expected.getUsedConstants.all env.contains do return .differs
  withoutModifyingState <| tryCatchRuntimeEx
    (do
      let same ← withCurrHeartbeats <| withTheReader Core.Context ({ · with maxHeartbeats := budget * 1000 }) <|
        isDefEq expected statement
      return if same then .matched else .differs)
    fun _ => pure .undecided

def catalogEvidence (modules : Array CatalogModule) : MetaM (Array (Evidence × CheckFact)) := do
  let env ← getEnv
  modules.flatMapM fun module =>
    (PersistentEnvExtension.getModuleEntries evidenceExt env module.index).mapM fun evidence => do
      return (evidence, { claim := evidence.claim, statement := ← shown evidence.statement
                          place := { file := module.file, line := evidence.line } })

def claimUses (challenge : ChallengeFacts) (evidence : Array (Evidence × CheckFact)) (budget : Nat := matchBudget) :
    MetaM (Array ClaimUse) :=
  challenge.headlines.flatMapM fun headline => do
    let claimed := headline.claimed challenge
    if claimed.isEmpty then return #[]
    let levels ← mkFreshLevelMVars headline.target.constant.levels.length
    let type := (exprOf headline.target.constant.type).instantiateLevelParams headline.target.constant.levels levels
    let (patterns, _, _) ← forallMetaTelescope (← Telescope.unfolded type)
    claimed.mapM fun (index, claim, _) => do
      let statement := ((headline.telescope[index]?).map (·.conclusion)).getD (toString claim)
      let checks ← match patterns[index]? with
        | some pattern => do
          let (_, _, expected) ← forallMetaTelescope (← Telescope.unfolded (← inferType pattern))
          (evidence.filter (·.1.claim == claim)).mapM fun (found, check) => do
            return (check, ← matchWithin budget expected found.statement)
        | none => pure #[]
      return { headline := headline.target.constant.name, binder := index, claim, statement, checks }

end SoftwareChallenge.Read
