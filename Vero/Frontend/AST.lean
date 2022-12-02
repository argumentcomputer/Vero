import Vero.Common.Typ
import YatimaStdLib.Ord
import Std.Data.RBMap

namespace Vero.Frontend

/-- Inductive enumerating unary operators -/
inductive UnOp
  | not
  deriving Ord, BEq

def UnOp.toString : UnOp → String
  | .not => "not"

/-- Inductive enumerating binary operators -/
inductive BinOp
  | add | mul | sub | div | eq | neq | lt | le | gt | ge | and | or
  deriving Ord, BEq

def BinOp.toString : BinOp → String
  | .add => "+"
  | .mul => "*"
  | .sub => "-"
  | .div => "/"
  | .eq  => "="
  | .neq => "!="
  | .lt  => "<"
  | .le  => "<="
  | .gt  => ">"
  | .ge  => ">="
  | .and => "&"
  | .or  => "|"

/-- Inductive enumerating the primitive types -/
inductive Lit
  | nat  : Nat  → Lit
  | bool : Bool → Lit
  deriving Ord, Inhabited, BEq

def Lit.typ : Lit → Typ
  | .nat  _ => .nat
  | .bool _ => .bool

structure Var where
  name : String
  typ : Typ
  deriving Ord, Inhabited, BEq

def Var.toString : Var → String
  | ⟨name, .hole⟩ => name
  | ⟨name, typ⟩ => s!"({name} : {typ})"

inductive AST
  | lit : Lit → AST
  | var : Var → AST
  | unOp : UnOp → AST → AST
  | binOp : BinOp → AST → AST → AST
  | fork : AST → AST → AST → AST
  | lam : Var → AST → AST
  | app : AST → AST → AST
  | rc : Var → AST → AST → AST
  deriving Ord, Inhabited, BEq

namespace AST

def hasFreeVar (s : String) : AST → Bool
  | .lit _ => false
  | .var ⟨s', _⟩ => s == s'
  | .unOp _ x => x.hasFreeVar s
  | .binOp _ x y => x.hasFreeVar s || y.hasFreeVar s
  | .fork x y z => x.hasFreeVar s || y.hasFreeVar s || z.hasFreeVar s
  | .lam ⟨s', _⟩ b => if s == s' then false else b.hasFreeVar s
  | .app x y => x.hasFreeVar s || y.hasFreeVar s
  | .rc ⟨s', _⟩ v b => if s == s' then false else v.hasFreeVar s || b.hasFreeVar s

def telescopeLam (acc : Array Var) : AST → (Array Var) × AST
  | .lam v b => b.telescopeLam $ acc.push v
  | x => (acc, x)

def telescopeApp (acc : List AST) : AST → List AST
  | .app f a => f.telescopeApp (a :: acc)
  | x => x :: acc

partial def toString : AST → String
  | .lit $ .nat n => ToString.toString n
  | .lit $ .bool true  => "tt"
  | .lit $ .bool false => "ff"
  | .var        v => v.toString
  | .unOp .not  x => s!"! {x.toString}"
  | .binOp op x y => s!"({x.toString} {op.toString} {y.toString})"
  | .fork  a  b c => s!"if {a.toString} then {b.toString} else {c.toString}"
  | .lam v b =>
    let (vs, b) := b.telescopeLam #[v]
    s!"(fun {" ".intercalate $ vs.data.map Var.toString} => {b.toString})"
  | .app f a@(.app ..) => s!"{f.toString} ({a.toString})"
  | .app f a =>
    let as := f.telescopeApp [a]
    s!"({" ".intercalate (as.map toString)})"
  | .rc v val b => s!"rec {v.toString} := {val.toString}; {b.toString}"

instance : ToString AST := ⟨AST.toString⟩

end AST

end Vero.Frontend
