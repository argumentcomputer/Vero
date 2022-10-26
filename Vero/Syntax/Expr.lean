namespace Vero.Syntax

inductive BinOp
  | add | mul

inductive Expr
  | var : String → Expr
  | num : Nat → Expr
  | binOp : BinOp → Expr → Expr → Expr
  | letIn : String → Expr → Expr → Expr

end Vero.Syntax
