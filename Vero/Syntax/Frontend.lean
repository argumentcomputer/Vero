import Std.Data.RBMap

namespace Vero.Syntax.Frontend

/-- Inductive enumerating unary operators -/
inductive UnOp
  | neg | not
  deriving Ord, Repr

/-- Inductive enumerating binary operators -/
inductive BinOp
  | add | mul | sub | div | eq | neq | lt | le | gt | ge | and | or | apd
  deriving Ord, Repr

/-- Inductive enumerating the primitive types -/
inductive Lit
  | bool : Bool   → Lit
  | int  : Int    → Lit
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

namespace DSL

open Lean Elab Meta Term

declare_syntax_cat           lit
scoped syntax "tt"         : lit
scoped syntax "ff"         : lit
scoped syntax num          : lit
scoped syntax "-" noWs num : lit
scoped syntax str          : lit

def mkApp' (name : Name) (e : Lean.Expr) : Lean.Expr :=
  mkApp (mkConst name) e

partial def elabLit : TSyntax `lit → TermElabM Lean.Expr
  | `(lit| tt) => mkAppM ``Lit.bool #[mkConst ``true] 
  | `(lit| ff) => mkAppM ``Lit.bool #[mkConst ``false]
  | `(lit| $n:num) => mkAppM ``Lit.int #[mkApp' ``Int.ofNat (mkNatLit n.getNat)]
  | `(lit| -$n:num) =>
    mkAppM ``Lit.int $ match n.getNat with
      | 0       => #[mkApp' ``Int.ofNat (mkConst ``Nat.zero)]
      | (n + 1) => #[mkApp' ``Int.negSucc (mkNatLit n)]
  | `(lit| $s:str) => mkAppM ``Lit.str #[mkStrLit s.getString]
  | _ => throwUnsupportedSyntax

declare_syntax_cat    ast
scoped syntax ident : ast
scoped syntax lit   : ast
scoped syntax " - " ws ast : ast
scoped syntax " ! " ast : ast
scoped syntax:50 ast:50 " + "  ast:51 : ast
scoped syntax:60 ast:60 " * "  ast:61 : ast
scoped syntax:50 ast:50 " - "  ast:51 : ast
scoped syntax:60 ast:60 " / "  ast:61 : ast
scoped syntax:70 ast:70 " = "  ast:71 : ast
scoped syntax:70 ast:70 " != " ast:71 : ast
scoped syntax:70 ast:70 " < "  ast:71 : ast
scoped syntax:70 ast:70 " <= " ast:71 : ast
scoped syntax:70 ast:70 " > "  ast:71 : ast
scoped syntax:70 ast:70 " >= " ast:71 : ast
scoped syntax:65 ast:65 " & "  ast:66 : ast
scoped syntax:65 ast:65 " | "  ast:66 : ast
scoped syntax:50 ast:50 " ++ " ast:51 : ast

-- assignment
scoped syntax withPosition(
  ident+ colGt " := " colGt ast colGt " ; "
  colGe ast) : ast

-- anonymous lambda
scoped syntax withPosition(ident+ colGt " => " colGt ast) : ast

-- application
scoped syntax:49 ast (colGt ast:50)+ : ast

-- forks
scoped syntax withPosition(
  "if " colGt ast colGt " then "
    colGt ast colGe
  " else "
    colGt ast) : ast

-- loops
scoped syntax withPosition(
  "while " colGt ast colGt " do "
    colGt ast) : ast

-- explicit parsing priority
scoped syntax "(" ast ")" : ast

def elabStr (i : TSyntax `ident) : Expr :=
  mkStrLit (i.getId.toString false)

def elabBinOp (a b : Expr) : BinOp → TermElabM Expr
  | .add => mkAppM ``AST.binOp #[mkConst ``BinOp.add, a, b]
  | .mul => mkAppM ``AST.binOp #[mkConst ``BinOp.mul, a, b]
  | .sub => mkAppM ``AST.binOp #[mkConst ``BinOp.sub, a, b]
  | .div => mkAppM ``AST.binOp #[mkConst ``BinOp.div, a, b]
  | .eq  => mkAppM ``AST.binOp #[mkConst ``BinOp.eq , a, b]
  | .neq => mkAppM ``AST.binOp #[mkConst ``BinOp.neq, a, b]
  | .lt  => mkAppM ``AST.binOp #[mkConst ``BinOp.lt , a, b]
  | .le  => mkAppM ``AST.binOp #[mkConst ``BinOp.le , a, b]
  | .gt  => mkAppM ``AST.binOp #[mkConst ``BinOp.gt , a, b]
  | .ge  => mkAppM ``AST.binOp #[mkConst ``BinOp.ge , a, b]
  | .and => mkAppM ``AST.binOp #[mkConst ``BinOp.and, a, b]
  | .or  => mkAppM ``AST.binOp #[mkConst ``BinOp.or , a, b]
  | .apd => mkAppM ``AST.binOp #[mkConst ``BinOp.apd, a, b]

partial def elabAST : TSyntax `ast → TermElabM Expr
  | `(ast| $i:ident) => mkAppM ``AST.var #[elabStr i]
  | `(ast| $p:lit) => return ← mkAppM ``AST.lit #[← elabLit p]
  | `(ast| - $x) => do mkAppM ``AST.unOp #[mkConst ``UnOp.neg , ← elabAST x]
  | `(ast| ! $x) => do mkAppM ``AST.unOp #[mkConst ``UnOp.not , ← elabAST x]
  | `(ast| $a + $b)  => do elabBinOp (← elabAST a) (← elabAST b) .add
  | `(ast| $a * $b)  => do elabBinOp (← elabAST a) (← elabAST b) .mul
  | `(ast| $a - $b)  => do elabBinOp (← elabAST a) (← elabAST b) .sub
  | `(ast| $a / $b)  => do elabBinOp (← elabAST a) (← elabAST b) .div
  | `(ast| $a = $b)  => do elabBinOp (← elabAST a) (← elabAST b) .eq
  | `(ast| $a != $b) => do elabBinOp (← elabAST a) (← elabAST b) .neq
  | `(ast| $a < $b)  => do elabBinOp (← elabAST a) (← elabAST b) .lt
  | `(ast| $a <= $b) => do elabBinOp (← elabAST a) (← elabAST b) .le
  | `(ast| $a > $b)  => do elabBinOp (← elabAST a) (← elabAST b) .gt
  | `(ast| $a >= $b) => do elabBinOp (← elabAST a) (← elabAST b) .ge
  | `(ast| $a & $b)  => do elabBinOp (← elabAST a) (← elabAST b) .and
  | `(ast| $a | $b)  => do elabBinOp (← elabAST a) (← elabAST b) .or
  | `(ast| $a ++ $b) => do elabBinOp (← elabAST a) (← elabAST b) .apd
  | `(ast| $f:ast $[$as:ast]*) => do
    as.foldlM (init := ← elabAST f) fun acc a => do
      mkAppM ``AST.app #[acc, ← elabAST a]
  | `(ast| $is:ident* $i:ident => $b:ast) => do
    let init ← mkAppM ``AST.lam #[elabStr i, ← elabAST b]
    is.foldrM (init := init) fun i acc => do
      mkAppM ``AST.lam #[elabStr i, acc]
  | `(ast| $i:ident $is:ident* := $v:ast; $b:ast) => do
    let lam ← is.foldrM (init := ← elabAST v) fun i acc => do
      mkAppM ``AST.lam #[elabStr i, acc]
    mkAppM ``AST.letIn #[elabStr i, lam, ← elabAST b]
  | `(ast| if $a:ast then $b:ast else $c:ast) => do
    mkAppM ``AST.fork #[← elabAST a, ← elabAST b, ← elabAST c]
  | `(ast| while $a:ast do $b:ast) => do
    mkAppM ``AST.loop #[← elabAST a, ← elabAST b]
  | `(ast| ($e)) => elabAST e
  | _ => throwUnsupportedSyntax

elab "⟦ " e:ast " ⟧" : term =>
  elabAST e

end DSL

end Vero.Syntax.Frontend
