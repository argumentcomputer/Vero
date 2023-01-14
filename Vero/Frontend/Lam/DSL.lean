import Lean
import Vero.Frontend.Lam.Lam

namespace Vero.Frontend.Lam.DSL

open Lean Elab Meta Term

declare_syntax_cat                  lam
scoped syntax ident               : lam
scoped syntax:50 lam lam:51       : lam
scoped syntax "λ" ident+ ". " lam : lam
scoped syntax "(" lam ")"         : lam

def elabStr (i : TSyntax `ident) : Lean.Expr :=
  mkStrLit (i.getId.toString false)

partial def elabExpr : TSyntax `lam → TermElabM Lean.Expr
  | `(lam| $i:ident) => mkAppM ``Lam.var #[elabStr i]
  | `(lam| $f:lam $a:lam) => do
    mkAppM ``Lam.app #[← elabExpr f, ← elabExpr a]
  | `(lam| λ $is:ident*. $b:lam) => do
    is.foldrM (init := ← elabExpr b) fun i acc => do
      mkAppM ``Lam.lam #[elabStr i, acc]
  | `(lam| ($e)) => elabExpr e
  | `(lam| $x) => do
    if x.raw.isAntiquot then
      let stx := x.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      trace[debug] e
      mkAppM ``toLam #[e]
    else throwUnsupportedSyntax

elab "⟦ " e:lam " ⟧" : term =>
  elabExpr e

end Vero.Frontend.Lam.DSL
