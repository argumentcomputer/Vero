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

def idx' (i : Nat) (nam : String) : List String → Option Nat
| n::ns => if n == nam then .some i else idx' (i+1) nam ns
| [] => .none

def idx := idx' 0

def AST.freeVars :=
  let rec aux (ctx : List String) (fs : List String) : AST → List String
  | var n => if !ctx.contains n && !fs.contains n then n::fs else fs
  | lam n b => aux (n::ctx) fs b
  | app x y => aux ctx (aux ctx fs x) y
  aux [] []

def AST.toExpr (x : AST) : Except String Expr :=
  let rec aux (ctx : List String) (fs: List String) : AST → Except String Expr
  | var n => match idx n ctx with
    | some i => return .var i
    | none => match idx' ctx.length n fs with
      | some i => return .var i
      | none => throw s!"{n} not found in free variables {fs}"
  | lam n b => return .lam (← aux (n::ctx) fs b)
  | app x y => return .app (← aux ctx fs x) (← aux ctx fs y)
  aux [] x.freeVars x

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
  | _ => throwUnsupportedSyntax

elab "⟦ " e:core_ast " ⟧" : term =>
  elabExpr e

end DSL

def Expr.shift (dep : Nat) (inc : Nat) : Expr → Expr
| .var n => if n >= dep then .var (n + inc) else .var n
| .lam b => .lam (shift (dep + 1) inc b)
| .app x y => .app (shift dep inc x) (shift dep inc y)

def Expr.subst (dep : Nat) (arg : Expr) : Expr → Expr
| .var n => match compare n dep with
  | .lt => .var n
  | .eq => shift 0 dep arg
  | .gt => .var (n - 1)
| .lam b => .lam (subst (dep+1) arg b)
| .app x y => .app (subst dep arg x) (subst dep arg y)

def Expr.reduce : Expr → Expr
| .app fnc arg => match reduce fnc with
  | .lam bod => subst 0 arg bod
  | fnc' => .app fnc' arg
| x => x

def AST.ppReduce (x : AST) : String :=
  match x.toExpr with
  | .ok expr => expr.reduce.toString
  | .error err => err

-- #eval ⟦a b c d e⟧.toString
-- #eval toString ⟦(λx y. x y x) (λx y. x) (λx y. y)⟧.toExpr
-- #eval ⟦(λx y. x y x) (λx y. x) (λx y. y)⟧.ppReduce

end Vero.Syntax.Core
