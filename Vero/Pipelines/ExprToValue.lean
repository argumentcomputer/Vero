import Vero.Frontend.Typ
import Vero.Core.Reduction.Value

namespace Vero.Core.Expr

open Frontend (Typ) in
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
    | .pair t₁ t₂ => match toPair t₁ t₂ e with
      | .ok (f, s) => .pair f s
      | .error e => .expr e

  partial def toPair (a b : Typ) : Expr → Except Expr (Value × Value)
    | .lam (.app (.app (.var 0) x) (y)) =>
      return (x.toValueOf a, y.toValueOf b)
    | x => throw x
  
  partial def toInt (e : Expr) : Except Expr Int :=
    match toPair .bool .nat e with
    | .ok (.bool b, .nat n) => match b with
      | false => return .ofNat n
      | true  => return .negSucc (n - 1)
    | .ok _
    | .error e => throw e

end

end Vero.Core.Expr
