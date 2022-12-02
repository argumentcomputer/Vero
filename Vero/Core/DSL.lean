import Lean
import Vero.Core.AST

namespace Vero.Core.DSL

open Lean Elab Meta Term

declare_syntax_cat                       core_ast
scoped syntax ident                    : core_ast
scoped syntax:50 core_ast core_ast:51  : core_ast
scoped syntax "λ" ident+ ". " core_ast : core_ast
scoped syntax "(" core_ast ")"         : core_ast

def elabStr (i : TSyntax `ident) : Lean.Expr :=
  mkStrLit (i.getId.toString false)

partial def elabExpr : TSyntax `core_ast → TermElabM Lean.Expr
  | `(core_ast| $i:ident) => mkAppM ``AST.var #[elabStr i]
  | `(core_ast| $f:core_ast $a:core_ast) => do
    mkAppM ``AST.app #[← elabExpr f, ← elabExpr a]
  | `(core_ast| λ $is:ident*. $b:core_ast) => do
    is.foldrM (init := ← elabExpr b) fun i acc => do
      mkAppM ``AST.lam #[elabStr i, acc]
  | `(core_ast| ($e)) => elabExpr e
  | `(core_ast| $x) => do
    if x.raw.isAntiquot then
      let stx := x.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      trace[debug] e
      mkAppM ``toAST #[e]
    else throwUnsupportedSyntax

elab "⟦ " e:core_ast " ⟧" : term =>
  elabExpr e

end Vero.Core.DSL
