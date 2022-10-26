import Lean
import Vero.Syntax.Expr

namespace Vero.Syntax.DSL

open Lean Elab Meta Term

declare_syntax_cat    bin_op
scoped syntax " + " : bin_op
scoped syntax " * " : bin_op

def elabBinOp : TSyntax `bin_op → TermElabM Lean.Expr
  | `(bin_op| +)  => return mkConst ``Vero.Syntax.BinOp.add
  | `(bin_op| *)  => return mkConst ``Vero.Syntax.BinOp.mul
  | _ => throwUnsupportedSyntax

declare_syntax_cat    expr
scoped syntax ident : expr
scoped syntax num   : expr
scoped syntax expr bin_op expr : expr
scoped syntax withPosition(ident colGe " := " colGe expr colGe expr) : expr
scoped syntax "(" expr ")" : expr

partial def elabExpr : TSyntax `expr → TermElabM Lean.Expr
  | `(expr| $i:ident) => do
    mkAppM ``Vero.Syntax.Expr.var #[mkStrLit (i.getId.toString false)]
  | `(expr| $n:num) => mkAppM ``Vero.Syntax.Expr.num #[mkNatLit n.getNat]
  | `(expr| $e₁ $op:bin_op $e₂) => do
    mkAppM ``Vero.Syntax.Expr.binOp #[← elabBinOp op, ← elabExpr e₁, ← elabExpr e₂]
  | `(expr| $i:ident := $v:expr $b:expr) => do
    mkAppM ``Vero.Syntax.Expr.letIn
      #[mkStrLit (i.getId.toString false), ← elabExpr v, ← elabExpr b]
  | `(expr| ($e)) => elabExpr e
  | _ => throwUnsupportedSyntax

elab "⟦ " e:expr " ⟧" : term =>
  elabExpr e

end Vero.Syntax.DSL
