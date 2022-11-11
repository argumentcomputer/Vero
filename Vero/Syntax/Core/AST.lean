import Lean

namespace Vero.Syntax.Core

inductive AST
  | var : String → AST
  | lam : String → AST → AST
  | app : AST → AST → AST
  deriving Ord, Inhabited, Repr

def nApp (f a : AST) : Nat → AST
  | 0 => a
  | n + 1 => .app f (nApp f a n)

class ToAST (α : Type _) where
  toAST : α → AST

export ToAST (toAST)

instance : ToAST AST := ⟨id⟩

mutual 
  def AST.toString : AST → String
    | .var n => n
    | .lam n b => s!"(λ {n} {b.lamsToString})"
    | .app (.lam n b) y => s!"(λ {n} {b.lamsToString}) {y.toString}"
    | .app x y@(.app ..) => s!"{x.toString} ({y.toString})"
    | .app x@(.app ..) y => s!"{x.toString} {y.toString}"
    | .app x y => s!"{x.toString} {y.toString}"

  def AST.lamsToString : AST → String
    | .lam n b@(.lam ..) => s!"{n} {b.lamsToString}"
    | .lam n b => s!"{n}. {b.toString}"
    | x => s!"{x.toString}"
end

instance : ToString AST where 
  toString := AST.toString

def AST.freeVars :=
  let rec aux (ctx fs : List String) : AST → List String
  | var n => if !ctx.contains n && !fs.contains n then n::fs else fs
  | lam n b => aux (n::ctx) fs b
  | app x y => aux ctx (aux ctx fs x) y
  aux [] []

section DSL

open Lean Elab Meta Term

declare_syntax_cat    core_ast
scoped syntax ident : core_ast
scoped syntax:30 core_ast (colGt core_ast:31)+ : core_ast
scoped syntax "(" core_ast ")" : core_ast
scoped syntax:49 "λ" ident* ". " core_ast:29 : core_ast

def elabStr (i : TSyntax `ident) : Lean.Expr :=
  mkStrLit (i.getId.toString false)

partial def elabExpr : TSyntax `core_ast → TermElabM Lean.Expr
  | `(core_ast| $i:ident) => mkAppM ``Vero.Syntax.Core.AST.var #[elabStr i]
  | `(core_ast| $f:core_ast $[$as:core_ast]*) => do
    as.foldlM (init := ← elabExpr f) fun acc a => do
      mkAppM ``Vero.Syntax.Core.AST.app #[acc, ← elabExpr a]
  | `(core_ast| λ $is:ident* . $b:core_ast) => do
    is.foldrM (init := ← elabExpr b) fun i acc => do
      mkAppM ``Vero.Syntax.Core.AST.lam #[elabStr i, acc]
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

end DSL

end Vero.Syntax.Core
