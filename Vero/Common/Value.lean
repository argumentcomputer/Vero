import Vero.Common.Expr
import Vero.Common.Typ

namespace Vero

inductive Value
  | expr : Expr → Value
  | nat  : Nat → Value
  | bool : Bool → Value
  | pair : Value → Value → Value
  deriving Inhabited, BEq

protected def Value.toString : Value → String
  | .expr e => toString e
  | .nat  n => toString n
  | .bool b => toString b
  | .pair f s => s!"({f.toString} . {s.toString})"

instance : ToString Value := ⟨Value.toString⟩

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

  /--
  Tries to convert an Expr to a certain type. Results in `.expr` in case of
  failure.
  -/
  partial def toValueOf (e : Expr) : Typ → Value
    | .hole
    | .pi .. => .expr e
    | .nat => match e.toNat with
      | .ok n => .nat n
      | .error e => .expr e
    | .bool => match e.toBool with
      | .ok b => .bool b
      | .error e => .expr e
    | .pair t₁ t₂ => match e.toPair t₁ t₂ with
      | .ok (f, s) => .pair f s
      | .error e => .expr e

  partial def toPair (a b : Typ) : Expr → Except Expr (Value × Value)
    | lam (app (app (var 0) x) (y)) => return (x.toValueOf a, y.toValueOf b)
    | x => throw x
  
  partial def toInt (e : Expr) : Except Expr Int :=
    match e.toPair .bool .nat with
    | .ok (.bool b, .nat n) => match b with
      | false => return .ofNat n
      | true  => return .negSucc (n - 1)
    | .ok _
    | .error e => throw e

end

end Vero.Expr
