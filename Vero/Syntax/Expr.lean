import Std.Data.RBMap

namespace Vero.Syntax

/-- Inductive enumerating unary operators -/
inductive UnOp
  | neg | not
  deriving Ord, Repr

/-- Inductive enumerating binary operators -/
inductive BinOp
  | add | mul | eq | le | and | or
  deriving Ord, Repr

/-- Inductive enumerating the primitive types -/
inductive Prim
  | bool (_ : Bool)
  | num  (_ : Nat)
  | char (_ : Char)
  deriving Ord, Inhabited, Repr

/-- Inductive describing the Vero AST -/
inductive Expr
  | lit : Prim → Expr
  | var : String → Expr
  | unOp : UnOp → Expr → Expr 
  | binOp : BinOp → Expr → Expr → Expr
  | letIn : String → Expr → Expr → Expr
  | lam : String → Expr → Expr
  | app : Expr → Expr → Expr
  | ite : Expr → Expr → Expr → Expr
  | loop : Expr → Expr → Expr
  deriving Ord, Inhabited, Repr

/-- 
Calculates the set of leaves appearing in the given sub-expressions which consists entirely of
additions

TODO : Do we still need this?
-/
def Expr.getAddLeaves (acc : Std.RBSet Expr compare := default) :
    Expr → Option (Std.RBSet Expr compare)
  | e@(var _)
  | e@(.lit $ .num _) => acc.insert e
  | binOp .add e₁ e₂ => do e₂.getAddLeaves (← e₁.getAddLeaves acc)
  | _ => none

/-- 
Calculates the set of leaves appearing in the given sub-expressions consisting entirely of
multiplications

TODO : Do we still need this?
-/
def Expr.getMulLeaves (acc : Std.RBSet Expr compare := default) :
    Expr → Option (Std.RBSet Expr compare)
  | e@(var _)
  | e@(.lit $ .num _) => acc.insert e
  | binOp .mul e₁ e₂ => do e₂.getMulLeaves (← e₁.getMulLeaves acc)
  | _ => none

/--
Minimizes the number of binary addition and multiplication operations in an expression to optimize
the circuit

TODO : Do we still need this?
-/
def Expr.normalize : Expr → Expr
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
  | ite c t f => ite c.normalize t.normalize f.normalize
  | loop c b => loop c.normalize b.normalize
  | e => e

end Vero.Syntax
