import Vero.Pipelines.SynToLam
import Vero.Pipelines.LamToExpr
import Vero.Pipelines.ExprToValue
import Vero.Frontend.Syn.TypeInference
import Vero.Core.Reduction.Scalar.Encoding
import Vero.Core.Reduction.Scalar.Decoding
import Vero.Core.Reduction.Direct
import Vero.Core.Reduction.Scalar.Reduce

namespace Vero.Pipelines

open Frontend Core

structure Input where
  syn  : Syn
  typ  : Typ
  lam  : Lam
  expr : Expr
  equivCore : lam = syn.toLam
  equivExpr : lam.toExpr = .ok expr
  wellTyped : syn.inferTyp = .ok typ

namespace Input

def ofSyn (syn : Syn) : Except String Input :=
  let lam := syn.toLam
  match h : lam.toExpr with
  | .ok expr => match h' : syn.inferTyp with
    | .ok typ => return ⟨syn, typ, lam, expr, rfl, h, h'⟩
    | .error err => throw err
  | .error err => throw err

def reduceDirect (inp : Input) : Value :=
  inp.expr.reduce.toValueOf inp.typ

def reduceScalar (inp : Input) : Except String Value := do
  let (ptr, store) := inp.expr.encode
  let (ptr, store) ← Scalar.reduce ptr store
  return (← Scalar.decode ptr store).toValueOf inp.typ

end Input

end Vero.Pipelines
