import Vero.Core.Expr

namespace Vero.Frontend

inductive Lam
  | var : String → Lam
  | lam : String → Lam → Lam
  | app : Lam → Lam → Lam
  deriving Ord, Inhabited

class ToLam (α : Type _) where
  toLam : α → Lam

export ToLam (toLam)

instance : ToLam Lam := ⟨id⟩

namespace Lam

def telescopeLam (acc : Array String) : Lam → (Array String) × Lam
  | .lam n b => b.telescopeLam $ acc.push n
  | x => (acc, x)

def telescopeApp (acc : List Lam) : Lam → List Lam
  | .app f a => f.telescopeApp (a :: acc)
  | x => x :: acc

partial def toString : Lam → String
  | .var n => n
  | .lam n b =>
    let (ns, b) := b.telescopeLam #[n]
    s!"(λ {" ".intercalate ns.data}. {b.toString})"
  | .app f a@(.app ..) => s!"{f.toString} ({a.toString})"
  | .app f a =>
    let as := f.telescopeApp [a]
    s!"({" ".intercalate (as.map toString)})"

instance : ToString Lam where 
  toString := Lam.toString

def freeVars : Lam → List String :=
  let rec aux (ctx fs : List String) : Lam → List String
  | var n => if !ctx.contains n && !fs.contains n then n::fs else fs
  | lam n b => aux (n::ctx) fs b
  | app x y => aux ctx (aux ctx fs x) y
  aux [] []

def idxFrom (i : Nat) (nam : String) : List String → Option Nat
  | n::ns => if n == nam then .some i else idxFrom (i + 1) nam ns
  | [] => .none

open Core (Expr) in
def toExpr (x : Lam) : Except String Expr :=
  let rec aux (ctx fs : List String) : Lam → Except String Expr
  | var n => match idxFrom 0 n ctx with
    | some i => return .var i
    | none => match idxFrom ctx.length n fs with
      | some i => return .var i
      | none => throw s!"{n} not found in free variables {fs}"
  | lam n b => return .lam (← aux (n::ctx) fs b)
  | app x y => return .app (← aux ctx fs x) (← aux ctx fs y)
  aux [] x.freeVars x

end Lam

end Vero.Frontend
