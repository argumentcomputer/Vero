import Lean
import Vero.Syntax.AST

/-!
# Vero DSL

This module defines the DSL to write Vero AST's inside a Lean file
-/

namespace Vero.Syntax.DSL

open Lean Elab Meta Term

declare_syntax_cat           lit
scoped syntax "tt"         : lit
scoped syntax "ff"         : lit
scoped syntax num          : lit
scoped syntax "-" noWs num : lit
scoped syntax char         : lit
scoped syntax str          : lit

def mkApp' (name : Name) (e : Expr) : Expr :=
  mkApp (mkConst name) e

partial def elabLit : TSyntax `lit → TermElabM Lean.Expr
  | `(lit| tt) => mkAppM ``Lit.bool #[mkConst ``true] 
  | `(lit| ff) => mkAppM ``Lit.bool #[mkConst ``false]
  | `(lit| $n:num) => mkAppM ``Lit.int #[mkApp' ``Int.ofNat (mkNatLit n.getNat)]
  | `(lit| -$n:num) =>
    mkAppM ``Lit.int $ match n.getNat with
      | 0       => #[mkApp' ``Int.ofNat (mkConst ``Nat.zero)]
      | (n + 1) => #[mkApp' ``Int.negSucc (mkNatLit n)]
  | `(lit| $c:char) => do
    mkAppM ``Lit.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
  | `(lit| $s:str) => mkAppM ``Lit.str #[mkStrLit s.getString]
  | _ => throwUnsupportedSyntax

declare_syntax_cat    expr
scoped syntax ident : expr
scoped syntax lit  : expr
scoped syntax:50 expr:50 " + " expr:51 : expr
scoped syntax:60 expr:60 " * " expr:61 : expr
scoped syntax withPosition(ident+ colGt " := " colGt expr colGt " ; " colGe expr) : expr
scoped syntax:49 expr (colGt expr:50)+ : expr
scoped syntax "(" expr ")" : expr

def elabStr (i : TSyntax `ident) : Lean.Expr :=
  mkStrLit (i.getId.toString false)

/-- TODO: binary and unary operators, if and while -/
partial def elabAST : TSyntax `expr → TermElabM Lean.Expr
  | `(expr| $i:ident) => mkAppM ``AST.var #[elabStr i]
  | `(expr| $p:lit) => return ← mkAppM ``AST.lit #[← elabLit p]
  | `(expr| $e₁ + $e₂) => do
    mkAppM ``AST.binOp #[mkConst ``BinOp.add, ← elabAST e₁, ← elabAST e₂]
  | `(expr| $e₁ * $e₂) => do
    mkAppM ``AST.binOp #[mkConst ``BinOp.mul, ← elabAST e₁, ← elabAST e₂]
  | `(expr| $f:expr $[$as:expr]*) => do
    as.foldlM (init := ← elabAST f) fun acc a => do
      mkAppM ``AST.app #[acc, ← elabAST a]
  | `(expr| $i:ident $is:ident* := $v:expr; $b:expr) => do
    let lam ← is.foldrM (init := ← elabAST v) fun i acc => do
      mkAppM ``AST.lam #[elabStr i, acc]
    mkAppM ``AST.letIn #[elabStr i, lam, ← elabAST b]
  | `(expr| ($e)) => elabAST e
  | _ => throwUnsupportedSyntax

elab "⟦ " e:expr " ⟧" : term =>
  elabAST e

end Vero.Syntax.DSL
