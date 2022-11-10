import Lean
import Vero.Syntax.Expr

/-!
# Vero DSL

This module defines the DSL to write Vero expressions inside a Lean file

## Unimplemented Syntax:
* UnOp
* BinOp `eq`, `le`, `and`, `or`
* `char`s
* `ite`
* `loop`
-/

namespace Vero.Syntax.DSL

open Lean Elab Meta Term

declare_syntax_cat prim
scoped syntax num : prim
scoped syntax "tt":prim
scoped syntax "ff":prim

partial def elabPrim : TSyntax `prim → TermElabM Lean.Expr
  | `(prim| tt) => mkAppM ``Vero.Syntax.Prim.bool #[mkConst ``true] 
  | `(prim| ff) => mkAppM ``Vero.Syntax.Prim.bool #[mkConst ``false]
  | `(prim| $n:num) => mkAppM ``Vero.Syntax.Prim.num #[mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax

declare_syntax_cat    expr
scoped syntax ident : expr
scoped syntax prim  : expr
scoped syntax:50 expr:50 " + " expr:51 : expr
scoped syntax:60 expr:60 " * " expr:61 : expr
scoped syntax withPosition(ident+ colGt " := " colGt expr colGt " ; " colGe expr) : expr
scoped syntax:49 expr (colGt expr:50)+ : expr
scoped syntax "(" expr ")" : expr

def elabStr (i : TSyntax `ident) : Lean.Expr :=
  mkStrLit (i.getId.toString false)

partial def elabExpr : TSyntax `expr → TermElabM Lean.Expr
  | `(expr| $i:ident) => mkAppM ``Vero.Syntax.Expr.var #[elabStr i]
  | `(expr| $p:prim) => return ← mkAppM ``Vero.Syntax.Expr.lit #[← elabPrim p]
  | `(expr| $e₁ + $e₂) => do
    mkAppM ``Vero.Syntax.Expr.binOp #[mkConst ``BinOp.add, ← elabExpr e₁, ← elabExpr e₂]
  | `(expr| $e₁ * $e₂) => do
    mkAppM ``Vero.Syntax.Expr.binOp #[mkConst ``BinOp.mul, ← elabExpr e₁, ← elabExpr e₂]
  | `(expr| $f:expr $[$as:expr]*) => do
    as.foldlM (init := ← elabExpr f) fun acc a => do
      mkAppM ``Vero.Syntax.Expr.app #[acc, ← elabExpr a]
  | `(expr| $i:ident $is:ident* := $v:expr; $b:expr) => do
    let lam ← is.foldrM (init := ← elabExpr v) fun i acc => do
      mkAppM ``Vero.Syntax.Expr.lam #[elabStr i, acc]
    mkAppM ``Vero.Syntax.Expr.letIn #[elabStr i, lam, ← elabExpr b]
  | `(expr| ($e)) => elabExpr e
  | _ => throwUnsupportedSyntax

elab "⟦ " e:expr " ⟧" : term =>
  elabExpr e

end Vero.Syntax.DSL
