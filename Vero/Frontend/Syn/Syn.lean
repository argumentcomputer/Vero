import YatimaStdLib.Ord
import Std.Data.RBMap
import Vero.Frontend.Typ

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

inductive Syn
  | lit : Lit → Syn
  | var : Var → Syn
  | unOp : UnOp → Syn → Syn
  | binOp : BinOp → Syn → Syn → Syn
  | fork : Syn → Syn → Syn → Syn
  | lam : Var → Syn → Syn
  | app : Syn → Syn → Syn
  | lt : Var → Syn → Syn → Syn
  | rc : Var → Syn → Syn → Syn
  deriving Ord, Inhabited, BEq

namespace Syn

def hasFreeVar (s : String) : Syn → Bool
  | .lit _ => false
  | .var ⟨s', _⟩ => s == s'
  | .unOp _ x => x.hasFreeVar s
  | .binOp _ x y => x.hasFreeVar s || y.hasFreeVar s
  | .fork x y z => x.hasFreeVar s || y.hasFreeVar s || z.hasFreeVar s
  | .lam ⟨s', _⟩ b => s != s' && b.hasFreeVar s
  | .app x y => x.hasFreeVar s || y.hasFreeVar s
  | .lt ⟨s', _⟩ v b => v.hasFreeVar s || (s != s' && b.hasFreeVar s)
  | .rc ⟨s', _⟩ v b => s == s' && (v.hasFreeVar s || b.hasFreeVar s)

def telescopeLam (acc : Array Var) : Syn → (Array Var) × Syn
  | .lam v b => b.telescopeLam $ acc.push v
  | x => (acc, x)

def telescopeApp (acc : List Syn) : Syn → List Syn
  | .app f a => f.telescopeApp (a :: acc)
  | x => x :: acc

partial def toString : Syn → String
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
  | .lt v val b => s!"let {v.toString} := {val.toString}; {b.toString}"
  | .rc v val b => s!"rec {v.toString} := {val.toString}; {b.toString}"

instance : ToString Syn := ⟨Syn.toString⟩

end Syn

end Vero.Frontend
