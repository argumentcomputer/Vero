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

/-- Inductive describing the Vero AST -/
inductive AST
  | lit : Lit → AST
  | var : String → AST
  | unOp : UnOp → AST → AST
  | binOp : BinOp → AST → AST → AST
  | letIn : String → AST → AST → AST
  | lam : String → AST → AST
  | app : AST → AST → AST
  | fork : AST → AST → AST → AST
  | loop : AST → AST → AST
  deriving Ord, Inhabited, Repr

end Vero.Syntax
