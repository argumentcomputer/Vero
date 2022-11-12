import Vero.Syntax.Core.AST

namespace Vero.Reduce

inductive Expr
  | var : Nat → Expr
  | lam : Expr → Expr
  | app : Expr → Expr → Expr
  deriving BEq, Inhabited

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

def shift (dep inc : Nat) : Expr → Expr
  | .var n => if n >= dep then .var (n + inc) else .var n
  | .lam b => .lam (shift (dep + 1) inc b)
  | .app x y => .app (shift dep inc x) (shift dep inc y)

def subst (dep : Nat) (arg : Expr) : Expr → Expr
  | .var n => match compare n dep with
    | .lt => .var n
    | .eq => shift 0 dep arg
    | .gt => .var (n - 1)
  | .lam b => .lam (subst (dep + 1) arg b)
  | .app x y => .app (subst dep arg x) (subst dep arg y)

partial def reduce : Expr → Expr
  | .app fnc arg => match reduce fnc with
    | .lam bod => reduce (subst 0 arg.reduce bod)
    | fnc' => .app fnc' arg.reduce
  | .lam b => .lam $ reduce b
  | x => x

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
