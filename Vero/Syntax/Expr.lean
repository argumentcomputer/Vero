import Std.Data.RBMap

namespace Vero.Syntax

/-- Inductive enumerating unary operators -/
inductive UnOp
  | neg | not
  deriving Ord, Repr

/-- Inductive enumerating binary operators -/
inductive BinOp
  | add | mul | sub | div | eq | neq | lt | le | gt | ge | and | or
  deriving Ord, Repr

/-- Inductive enumerating the primitive types -/
inductive Lit
  | bool : Bool   → Lit
  | int  : Int    → Lit
  | char : Char   → Lit
  | str  : String → Lit
  deriving Ord, Inhabited, Repr

/-- Inductive describing the Vero Expr -/
inductive Expr
  | lit : Lit → Expr
  | var : String → Expr
  | unOp : UnOp → Expr → Expr
  | binOp : BinOp → Expr → Expr → Expr
  | letIn : String → Expr → Expr → Expr
  | lam : String → Expr → Expr
  | app : Expr → Expr → Expr
  | fork : Expr → Expr → Expr → Expr
  | loop : Expr → Expr → Expr
  deriving Ord, Inhabited, Repr

end Vero.Syntax
