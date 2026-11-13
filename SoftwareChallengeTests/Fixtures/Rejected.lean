module

public import SoftwareChallengeTests.Fixtures.CoreCode
public import SoftwareChallengeTests.Fixtures.WorldSpec
meta import SoftwareChallenge.Commands

public section

namespace SoftwareChallengeTests.Fixtures.Rejected

private unsafe def hiddenUnsafe (n : Nat) : Nat := n + 1

partial def diverging (n : Nat) : Nat := diverging n

abbrev Effect := IO Nat

def hiddenEffect : Effect := pure 0

structure EffectBox where
  action : IO Nat

def packagedEffect : EffectBox := ⟨pure 0⟩

initialize startup : Nat ← pure 0

@[extern "lean_nat_succ"] def bound (n : Nat) : Nat := n + 1

@[extern "lean_nat_succ"] opaque foreign : @& Nat → Nat

def fast (n : Nat) : Nat := n + 1

@[implemented_by fast] def replaced (n : Nat) : Nat := n + 1

def traced (n : Nat) : Nat := dbgTrace "side effect" fun _ => n

def traceValue (n : Nat) : Nat := dbgTraceVal n

axiom raw : False

private theorem viaRaw : False := raw

private theorem chained : 1 = 2 := viaRaw.elim

theorem hole : Identity identity := by sorry

run_cmd Lean.modifyEnv (SoftwareChallenge.claimsExt.addEntry · `SoftwareChallengeTests.Fixtures.Identity)

end SoftwareChallengeTests.Fixtures.Rejected
