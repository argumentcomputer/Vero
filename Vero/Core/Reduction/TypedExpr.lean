import Vero.Frontend.Lam.Lam
import Vero.Frontend.Syn.Syn
import Vero.Frontend.SynToLam
import Vero.Core.Expr
-- import Vero.Frontend.ToCore
-- import Vero.Frontend.TypeInference
-- import Vero.Common.Value
-- import Vero.Scalar.Encoding
-- import Vero.Scalar.Decoding
-- import Vero.Reduction.Direct
-- import Vero.Reduction.Scalar

namespace Vero.Core

structure TypedExpr where
  syn  : Frontend.Syn
  lam  : Frontend.Lam
  typ  : Frontend.Typ
  expr : Expr
  equivCore : lam = syn.toLam
  equivExpr : core.toExpr = .ok expr
  wellTyped : ast.inferTyp = .ok typ

def TypedExpr.ofAST (ast : Frontend.AST) : Except String TypedExpr :=
  let core := ast.toCore
  match h : core.toExpr with
  | .ok expr => match h' : ast.inferTyp with
    | .ok typ => return ⟨ast, core, expr, typ, by eq_refl, h, h'⟩
    | .error err => throw err
  | .error err => throw err

def TypedExpr.directReduce (te : TypedExpr) : Value :=
  te.expr.reduce.toValueOf te.typ

def TypedExpr.scalarReduce (te : TypedExpr) : Except String Value := do
  let (ptr, store) := te.expr.encode
  let (ptr, store) ← Scalar.reduce ptr store
  let e ← Scalar.decode ptr store
  return e.toValueOf te.typ

end Vero.Reduction
