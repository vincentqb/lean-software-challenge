module

public import Lean.Expr

@[expose] public section

namespace SoftwareChallenge

open Lean

inductive ExprSimilar : Expr → Expr → Prop where
  | refl (expr : Expr) : ExprSimilar expr expr
  | app {leftFunction rightFunction leftArgument rightArgument : Expr} :
      ExprSimilar leftFunction rightFunction → ExprSimilar leftArgument rightArgument →
      ExprSimilar (.app leftFunction leftArgument) (.app rightFunction rightArgument)
  | lam {leftName rightName : Name} {leftType rightType leftBody rightBody : Expr}
      {leftInfo rightInfo : BinderInfo} :
      ExprSimilar leftType rightType → ExprSimilar leftBody rightBody →
      ExprSimilar (.lam leftName leftType leftBody leftInfo) (.lam rightName rightType rightBody rightInfo)
  | forallE {leftName rightName : Name} {leftType rightType leftBody rightBody : Expr}
      {leftInfo rightInfo : BinderInfo} :
      ExprSimilar leftType rightType → ExprSimilar leftBody rightBody →
      ExprSimilar (.forallE leftName leftType leftBody leftInfo) (.forallE rightName rightType rightBody rightInfo)
  | letE {leftName rightName : Name} {leftType rightType leftValue rightValue leftBody rightBody : Expr}
      {leftNonDep rightNonDep : Bool} :
      ExprSimilar leftType rightType → ExprSimilar leftValue rightValue → ExprSimilar leftBody rightBody →
      ExprSimilar (.letE leftName leftType leftValue leftBody leftNonDep)
        (.letE rightName rightType rightValue rightBody rightNonDep)
  | proj {structureName : Name} {index : Nat} {left right : Expr} :
      ExprSimilar left right → ExprSimilar (.proj structureName index left) (.proj structureName index right)
  | mdataLeft {data : MData} {left right : Expr} : ExprSimilar left right → ExprSimilar (.mdata data left) right
  | mdataRight {data : MData} {left right : Expr} : ExprSimilar left right → ExprSimilar left (.mdata data right)

end SoftwareChallenge
