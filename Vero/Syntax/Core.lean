import Lean

namespace Vero.Syntax.Core

inductive Expr
  | var : Nat → Expr
  | lam : Expr → Expr
  | app : Expr → Expr → Expr
  deriving BEq, Inhabited, Repr

mutual 
  def Expr.toString : Expr → String
  | .var i => s!"{i}"
  | .lam b => s!"(λ {b.lamsToString})"
  | .app (.lam b) y => s!"(λ {b.lamsToString}) {y.toString}"
  | .app x y@(.app _ _) => s!"{x.toString} ({y.toString})"
  | .app x@(.app _ _) y => s!"{x.toString} {y.toString}"
  | .app x y => s!"{x.toString} {y.toString}"

  def Expr.lamsToString : Expr → String
  | .lam b@(.lam _) => s!"λ {b.lamsToString}"
  | .lam b => s!"λ {b.toString}"
  | x => s!"{x.toString}"
end


instance : ToString Expr where 
  toString := Expr.toString

inductive AST
  | var : String -> AST
  | lam : String -> AST → AST
  | app : AST → AST → AST
  deriving Ord, Inhabited, Repr

mutual 
  def AST.toString : AST → String
  | .var n => n
  | .lam n b => s!"(λ{n} {b.lamsToString})"
  | .app (.lam n b) y => s!"(λ {n} {b.lamsToString}) {y.toString}"
  | .app x y@(.app _ _) => s!"{x.toString} ({y.toString})"
  | .app x@(.app _ _) y => s!"{x.toString} {y.toString}"
  | .app x y => s!"{x.toString} {y.toString}"

  def AST.lamsToString : AST → String
  | .lam n b@(.lam _ _) => s!"{n} {b.lamsToString}"
  | .lam n b => s!"{n}. {b.toString}"
  | x => s!"{x.toString}"
end


instance : ToString AST where 
  toString := AST.toString

def idx' (i: Nat) (nam: String)  : List String → Option Nat
| n::ns => if n == nam then .some i else idx' (i+1) nam ns
| [] => .none

def idx := idx' 0

def AST.freeVars' (ctx: List String) (fs : List String) : AST → List String
| var n => if !ctx.contains n && !fs.contains n then n::fs else fs
| lam n b => AST.freeVars' (n::ctx) fs b
| app x y => AST.freeVars' ctx (AST.freeVars' ctx fs x) y

def AST.freeVars := AST.freeVars' [] []

def AST.toExpr' (ctx : List String) (fs: List String) : AST → Expr
| var n => match idx n ctx with
  | some i => .var i
  | none => match idx' ctx.length n fs with | some i => .var i | none => panic! ""
| lam n b => .lam (AST.toExpr' (n::ctx) fs b)
| app x y => .app (AST.toExpr' ctx fs x) (AST.toExpr' ctx fs y)

def AST.toExpr (x : AST) : Expr := AST.toExpr' [] x.freeVars x

open Lean Elab Meta Term

declare_syntax_cat    expr
scoped syntax ident : expr
scoped syntax:30 expr (colGt expr:31)+ : expr
scoped syntax "(" expr ")" : expr
scoped syntax:49 "λ" ident* ". " expr:29 : expr

def elabStr (i : TSyntax `ident) : Lean.Expr :=
  mkStrLit (i.getId.toString false)

partial def elabExpr : TSyntax `expr → TermElabM Lean.Expr
  | `(expr| $i:ident) => mkAppM ``Vero.Syntax.Core.AST.var #[elabStr i]
  | `(expr| $f:expr $[$as:expr]*) => do
    as.foldlM (init := ← elabExpr f) fun acc a => do
      mkAppM ``Vero.Syntax.Core.AST.app #[acc, ← elabExpr a]
  | `(expr| λ $is:ident* . $b:expr) => do
    is.foldrM (init := ← elabExpr b) fun i acc => do
      mkAppM ``Vero.Syntax.Core.AST.lam #[elabStr i, acc]
  | `(expr| ($e)) => elabExpr e
  | _ => throwUnsupportedSyntax

elab "⟦ " e:expr " ⟧" : term =>
  elabExpr e

def Expr.shift (dep: Nat) (inc: Nat) : Expr → Expr
| .var n => if n > dep then .var (n + inc) else .var n
| .lam b => .lam (shift (dep + 1) inc b)
| .app x y => .app (shift dep inc x) (shift dep inc y)

def Expr.subst (dep: Nat) (arg: Expr) : Expr → Expr
| .var n => match compare n dep with
  | .lt => .var n
  | .eq => shift 0 (dep - 1) arg
  | .gt => .var (n - 1)
| .lam b => .lam (subst (dep+1) arg b)
| .app x y => .app (subst dep arg x) (subst dep arg y)

def Expr.reduce: Expr -> Expr
| .app (.lam bod) arg => subst 0 arg bod
| .app x y => .app (reduce x) y
| x => x

-- #eval ⟦ a b c d e⟧.toString
-- #eval ⟦ (λx y. x y x) (λx y. x) (λx y. y)⟧.toExpr.toString
-- #eval ⟦ (λx y. x y x) (λx y. x) (λx y. y)⟧.toExpr.reduce.toString

end Vero.Syntax.Core





