import Vero.Frontend.Lam.Lam

namespace Vero.Frontend.Lam

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

end Vero.Frontend.Lam
