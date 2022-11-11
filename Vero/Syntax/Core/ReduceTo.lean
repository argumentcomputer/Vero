import Vero.Syntax.Core.Expr

namespace Vero.Syntax.Core

inductive ValType
  | nat | bool
  deriving Repr

inductive Value
  | nat : Nat → Value
  | bool : Bool → Value
  | expr : Expr → Value
  | error : String → Value
  deriving Repr

namespace Expr

def toNat (e : Expr) : Except Expr Nat :=
  let rec countApps : Expr → Except Expr Nat
    | var 0 => return 0
    | app (var 1) x => return 1 + (← countApps x)
    | x => throw x
  match e with
  | lam (lam x) => countApps x
  | x => throw x

def toBool : Expr → Except Expr Bool
  | lam (lam (var 0)) => return false
  | lam (lam (var 1)) => return true
  | x => throw x

end Expr

namespace AST

/--
Tries to reduce an AST to a certain type. Returns `.expr` or `.error` in case of
failure.
-/
def reduce (x : AST) (to : ValType) : Value :=
  match x.toExpr with
  | .error err => .error err
  | .ok expr =>
    let expr := expr.reduce
    match to with
    | .nat => match expr.toNat with
      | .ok n => .nat n
      | .error e => .expr e
    | .bool =>  match expr.toBool with
      | .ok b => .bool b
      | .error e => .expr e

end Vero.Syntax.Core.AST
