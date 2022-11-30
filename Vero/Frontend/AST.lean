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
  deriving Ord, Inhabited, BEq

def AST.telescopeLam (acc : Array Var) : AST → (Array Var) × AST
  | .lam v b => b.telescopeLam $ acc.push v
  | x => (acc, x)

def AST.telescopeApp (acc : List AST) : AST → List AST
  | .app f a => f.telescopeApp (a :: acc)
  | x => x :: acc

partial def AST.toString : AST → String
  | .lit $ .nat n => ToString.toString n
  | .lit $ .bool true  => "tt"
  | .lit $ .bool false => "ff"
  | .var        v => v.toString
  | .unOp .not  x => s!"! {x.toString}"
  | .binOp op x y => s!"({x.toString} {op.toString} {y.toString})"
  | .fork  a  b c => s!"if {a.toString} then {b.toString} else {c.toString}"
  | .lam v b =>
    let (vs, b) := b.telescopeLam #[v]
    s!"fun {" ".intercalate $ vs.data.map Var.toString} => {b.toString}"
  | .app f a =>
    let as := f.telescopeApp [a]
    s!"({" ".intercalate (as.map toString)})"

instance : ToString AST := ⟨AST.toString⟩

end Vero.Frontend
