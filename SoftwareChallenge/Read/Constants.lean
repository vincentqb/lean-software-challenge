module

public meta import Lean
public meta import SoftwareChallenge.CoreSpec.Facts
public meta import SoftwareChallenge.CoreCode.OfExpr
public meta import SoftwareChallenge.Read.Source

public section
meta section

open Lean Meta

namespace SoftwareChallenge.Read

def safetyOf : DefinitionSafety → Safety
  | .safe => .safe
  | .unsafe => .«unsafe»
  | .partial => .«partial»

def kindOf : ConstantInfo → ConstantKind
  | .axiomInfo _ => .assumed
  | .defnInfo info => .defined (safetyOf info.safety)
  | .thmInfo _ => .proved
  | .opaqueInfo _ => .opaqueConstant
  | .quotInfo _ => .quotient
  | .inductInfo _ => .inductiveType
  | .ctorInfo _ => .constructor
  | .recInfo _ => .recursor

def hintsOf : ConstantInfo → String
  | .defnInfo info => match info.hints with
    | .opaque => "opaque"
    | .abbrev => "abbrev"
    | .regular height => s!"regular {height}"
  | _ => ""

def constantFact (info : ConstantInfo) : ConstantFact := {
  name := info.name
  kind := kindOf info
  levels := info.levelParams
  type := Shape.ofExpr info.type
  value? := (info.value? (allowOpaque := true)).map Shape.ofExpr
  hints := hintsOf info
  mutualBlock := info.all
  isPrivate := isPrivateName info.name }

def shown (expr : Expr) : MetaM String := return oneLine (toString (← ppExpr expr))

def render (expr : Expr) : MetaM (String × String) := do
  let shownWith := fun (explicit : Bool) => withOptions (fun options => ((options.setBool `pp.proofs true).setBool
    `pp.explicit explicit).setBool `pp.universes explicit) (shown expr)
  return (← shownWith false, ← shownWith true)

def levelOf : Universe → Level
  | .zero => .zero
  | .succ level => .succ (levelOf level)
  | .max left right => .max (levelOf left) (levelOf right)
  | .imax left right => .imax (levelOf left) (levelOf right)
  | .param name => .param name
  | .mvar name => .mvar ⟨name⟩

def exprOf : Shape → Expr
  | .bvar index => .bvar index
  | .fvar name => .fvar ⟨name⟩
  | .mvar name => .mvar ⟨name⟩
  | .sort level => .sort (levelOf level)
  | .const name levels => .const name (levels.map levelOf)
  | .app function argument => .app (exprOf function) (exprOf argument)
  | .lam type body => .lam `x (exprOf type) (exprOf body) .default
  | .forallE type body => .forallE `x (exprOf type) (exprOf body) .default
  | .letE type value body => .letE `x (exprOf type) (exprOf value) (exprOf body) false
  | .natLit value => .lit (.natVal value)
  | .strLit value => .lit (.strVal value)
  | .proj structureName index value => .proj structureName index (exprOf value)

end SoftwareChallenge.Read
