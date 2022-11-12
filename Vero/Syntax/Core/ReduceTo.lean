import Vero.Syntax.Core.Expr
import Vero.Syntax.Core.Data

namespace Vero.Syntax.Core

inductive ValType
  | any
  | nat
  | bool
  | pair : ValType → ValType → ValType
  | int
  deriving Repr

inductive Value
  | expr : Expr → Value
  | nat  : Nat → Value
  | bool : Bool → Value
  | pair : Value → Value → Value
  | int  : Int → Value
  deriving Repr, Inhabited

protected def Value.toString : Value → String
  | .expr e => toString e
  | .nat  n => toString n
  | .bool b => toString b
  | .pair f s => s!"({f.toString} . {s.toString})"
  | .int  i => toString i

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

mutual

  partial def ofType (e : Expr) : ValType → Value
    | .any => .expr e
    | .nat => match e.toNat with
      | .ok n => .nat n
      | .error e => .expr e
    | .bool => match e.toBool with
      | .ok b => .bool b
      | .error e => .expr e
    | .pair t₁ t₂ => match e.toPair t₁ t₂ with
      | .ok (f, s) => .pair f s
      | .error e => .expr e
    | .int => match e.toInt with
      | .ok i => .int i
      | .error e => .expr e

  partial def toPair (a b : ValType) : Expr → Except Expr (Value × Value)
    | lam (app (app (var 0) x) (y)) =>
      let t₁ : Value := x.ofType a
      let t₂ : Value := y.ofType b
      return (t₁, t₂)
    | x => throw x
  
  partial def toInt (e : Expr) : Except Expr Int :=
    match e.toPair .bool .nat with
    | .ok (.bool b, .nat n) => match b with
      | false => return .ofNat n
      | true  => return .negSucc (n - 1)
    | .ok _
    | .error e => throw e

end

end Expr

namespace AST

/--
Tries to reduce an AST to a certain type. Returns `.expr` in case of failure.
-/
def reduceTo (x : AST) (type : ValType) : Except String Value :=
  match x.toExpr with
  | .error err => throw err
  | .ok expr => return expr.reduce.ofType type

def reduceToPP (x : AST) (type : ValType) : String :=
  match x.reduceTo type with
  | .error err => err
  | .ok v => v.toString

end Vero.Syntax.Core.AST
