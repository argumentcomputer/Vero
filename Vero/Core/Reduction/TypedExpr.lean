import Vero.Frontend.Lam.Lam
import Vero.Frontend.Syn.Syn
import Vero.Frontend.Syn.TypeInference
import Vero.Frontend.SynToLam
import Vero.Core.Expr
import Vero.Core.Reduction.Value
import Vero.Core.Scalar.Encoding
import Vero.Core.Scalar.Decoding
import Vero.Core.Reduction.Direct
import Vero.Core.Reduction.Scalar

namespace Vero.Core

open Frontend

structure TypedExpr where
  syn  : Syn
  typ  : Typ
  lam  : Lam
  expr : Expr
  equivCore : lam = syn.toLam
  equivExpr : lam.toExpr = .ok expr
  wellTyped : syn.inferTyp = .ok typ

def TypedExpr.ofSyn (syn : Syn) : Except String TypedExpr :=
  let lam := syn.toLam
  match h : lam.toExpr with
  | .ok expr => match h' : syn.inferTyp with
    | .ok typ => return ⟨syn, typ, lam, expr, rfl, h, h'⟩
    | .error err => throw err
  | .error err => throw err

def TypedExpr.directReduce (te : TypedExpr) : Value :=
  .ofExprWithTyp te.expr.reduce te.typ

def TypedExpr.scalarReduce (te : TypedExpr) : Except String Value := do
  let (ptr, store) := te.expr.encode
  let (ptr, store) ← Scalar.reduce ptr store
  let e ← Scalar.decode ptr store
  return .ofExprWithTyp e te.typ

end Vero.Core
