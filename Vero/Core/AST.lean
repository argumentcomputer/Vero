import Vero.Common.Expr

namespace Vero.Core

inductive AST
  | var : String → AST
  | lam : String → AST → AST
  | app : AST → AST → AST
  deriving Ord, Inhabited

def nApp (f a : AST) : Nat → AST
  | 0 => a
  | n + 1 => .app f (nApp f a n)

class ToAST (α : Type _) where
  toAST : α → AST

export ToAST (toAST)

instance : ToAST AST := ⟨id⟩

namespace AST

def telescopeLam (acc : Array String) : AST → (Array String) × AST
  | .lam n b => b.telescopeLam $ acc.push n
  | x => (acc, x)

def telescopeApp (acc : List AST) : AST → List AST
  | .app f a => f.telescopeApp (a :: acc)
  | x => x :: acc

partial def toString : AST → String
  | .var n => n
  | .lam n b =>
    let (ns, b) := b.telescopeLam #[n]
    s!"(λ {" ".intercalate ns.data}. {b.toString})"
  | .app f a@(.app ..) => s!"{f.toString} ({a.toString})"
  | .app f a =>
    let as := f.telescopeApp [a]
    s!"{" ".intercalate (as.map toString)}"

instance : ToString AST where 
  toString := AST.toString

def freeVars : AST → List String :=
  let rec aux (ctx fs : List String) : AST → List String
  | var n => if !ctx.contains n && !fs.contains n then n::fs else fs
  | lam n b => aux (n::ctx) fs b
  | app x y => aux ctx (aux ctx fs x) y
  aux [] []

private def idxFrom (i : Nat) (nam : String) : List String → Option Nat
  | n::ns => if n == nam then .some i else idxFrom (i + 1) nam ns
  | [] => .none

def toExpr (x : AST) : Except String Expr :=
  let rec aux (ctx fs : List String) : AST → Except String Expr
  | var n => match idxFrom 0 n ctx with
    | some i => return .var i
    | none => match idxFrom ctx.length n fs with
      | some i => return .var i
      | none => throw s!"{n} not found in free variables {fs}"
  | lam n b => return .lam (← aux (n::ctx) fs b)
  | app x y => return .app (← aux ctx fs x) (← aux ctx fs y)
  aux [] x.freeVars x

end AST

end Vero.Core
