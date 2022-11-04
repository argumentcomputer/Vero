import Lean

namespace Vero.Syntax

inductive BinOp
  | add | mul
  deriving Ord

inductive Expr
  | num : Nat → Expr
  | var : String → Expr
  | binOp : BinOp → Expr → Expr → Expr
  | letIn : String → Expr → Expr → Expr
  | lam : String → Expr → Expr
  | app : Expr → Expr → Expr
  deriving Ord, Inhabited

def Expr.getAddLeaves (acc : Std.RBTree Expr compare := default) :
    Expr → Option (Std.RBTree Expr compare)
  | e@(var _)
  | e@(num _) => acc.insert e
  | binOp .add e₁ e₂ => do e₂.getAddLeaves (← e₁.getAddLeaves acc)
  | _ => none

def Expr.getMulLeaves (acc : Std.RBTree Expr compare := default) :
    Expr → Option (Std.RBTree Expr compare)
  | e@(var _)
  | e@(num _) => acc.insert e
  | binOp .mul e₁ e₂ => do e₂.getMulLeaves (← e₁.getMulLeaves acc)
  | _ => none

def Expr.normalize : Expr → Expr
  | e@(var _)
  | e@(num _) => e
  | e@(binOp .add e₁ e₂) => match e.getAddLeaves with
    | some leaves => match leaves.toList with
      | h :: t => t.foldl (init := h) fun acc e => .binOp .add acc e
      | [] => unreachable!
    | none => binOp .add e₁.normalize e₂.normalize
  | e@(binOp .mul e₁ e₂) => match e.getMulLeaves with
    | some leaves => match leaves.toList with
      | h :: t => t.foldl (init := h) fun acc e => .binOp .mul acc e
      | [] => unreachable!
    | none => binOp .mul e₁.normalize e₂.normalize
  | letIn s v b => letIn s v.normalize b.normalize
  | lam s b => lam s b.normalize
  | app f a => app f.normalize a.normalize

end Vero.Syntax
