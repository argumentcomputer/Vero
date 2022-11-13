import Vero.Syntax.Core.AST

namespace Vero.Reduce

inductive Expr
  | var : Nat → Expr
  | lam : Expr → Expr
  | app : Expr → Expr → Expr
  deriving BEq, Ord, Inhabited

namespace Expr

mutual 
  def toString : Expr → String
    | .var i => s!"{i}"
    | .lam b => s!"(λ {b.lamsToString})"
    | .app (.lam b) y => s!"(λ {b.lamsToString}) {y.toString}"
    | .app x y@(.app ..) => s!"{x.toString} ({y.toString})"
    | .app x@(.app ..) y => s!"{x.toString} {y.toString}"
    | .app x y => s!"{x.toString} {y.toString}"

  def lamsToString : Expr → String
    | .lam b@(.lam _) => s!"λ {b.lamsToString}"
    | .lam b => s!"λ {b.toString}"
    | x => s!"{x.toString}"
end

instance : ToString Expr where 
  toString := Expr.toString

end Reduce.Expr

namespace Syntax.Core

def idxFrom (i : Nat) (nam : String) : List String → Option Nat
  | n::ns => if n == nam then .some i else idxFrom (i + 1) nam ns
  | [] => .none

def idx := idxFrom 0

open Reduce in
def AST.toExpr (x : AST) : Except String Expr :=
  let rec aux (ctx fs : List String) : AST → Except String Expr
  | var n => match idx n ctx with
    | some i => return .var i
    | none => match idxFrom ctx.length n fs with
      | some i => return .var i
      | none => throw s!"{n} not found in free variables {fs}"
  | lam n b => return .lam (← aux (n::ctx) fs b)
  | app x y => return .app (← aux ctx fs x) (← aux ctx fs y)
  aux [] x.freeVars x

end Vero.Syntax.Core
