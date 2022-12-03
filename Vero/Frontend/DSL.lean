import Vero.Frontend.AST

namespace Vero.Frontend.DSL

open Lean Elab Meta Term

declare_syntax_cat           lit
scoped syntax "tt"         : lit
scoped syntax "ff"         : lit
scoped syntax num          : lit

def elabLit : TSyntax `lit → TermElabM Lean.Expr
  | `(lit| tt) => mkAppM ``Lit.bool #[mkConst ``true]
  | `(lit| ff) => mkAppM ``Lit.bool #[mkConst ``false]
  | `(lit| $n:num) => mkAppM ``Lit.nat #[mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax

declare_syntax_cat             typ
scoped syntax "_"            : typ
scoped syntax "nat"          : typ
scoped syntax "bool"         : typ
scoped syntax typ " . "  typ : typ
scoped syntax typ " -> " typ : typ
scoped syntax "(" typ ")"    : typ

partial def elabTyp : TSyntax `typ → TermElabM Lean.Expr
  | `(typ| _)    => mkConst ``Typ.hole
  | `(typ| nat)  => mkConst ``Typ.nat
  | `(typ| bool) => mkConst ``Typ.bool
  | `(typ| $t₁:typ . $t₂:typ) => do
    mkAppM ``Typ.pair #[← elabTyp t₁, ← elabTyp t₂]
  | `(typ| $t₁:typ -> $t₂:typ) => do
    mkAppM ``Typ.pi #[← elabTyp t₁, ← elabTyp t₂]
  | `(typ| ($t:typ)) => elabTyp t
  | _ => throwUnsupportedSyntax

elab "⟪" x:typ "⟫" : term =>
  elabTyp x

declare_syntax_cat var
scoped syntax ident (":" typ)? : var
scoped syntax "(" var ")" : var

def elabStr (i : TSyntax `ident) : Expr :=
  mkStrLit (i.getId.toString false)

partial def elabVar : TSyntax `var → TermElabM Lean.Expr
  | `(var| $i:ident) => do mkAppM ``Var.mk #[elabStr i, mkConst ``Typ.hole]
  | `(var| $i:ident : $t:typ) => do mkAppM ``Var.mk #[elabStr i, ← elabTyp t]
  | `(var| ($v:var)) => elabVar v
  | _ => throwUnsupportedSyntax

declare_syntax_cat  ast
scoped syntax var : ast
scoped syntax lit : ast
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

-- assignment
scoped syntax withPosition(
  "let" var+ colGt " := " colGt ast colGt ";"
  colGe ast) : ast

-- recursive assignment
scoped syntax withPosition(
  "rec" var+ colGt " := " colGt ast colGt ";"
  colGe ast) : ast

-- anonymous lambda
scoped syntax withPosition("fun" var+ colGt " => " colGt ast) : ast

-- application
scoped syntax:50 ast ast:51 : ast

-- forks
scoped syntax withPosition(
  "if " colGt ast colGt " then "
    colGt ast colGe
  " else "
    colGt ast) : ast

-- explicit parsing priority
scoped syntax "(" ast ")" : ast

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

partial def elabAST : TSyntax `ast → TermElabM Expr
  | `(ast| ($v:var))
  | `(ast| $v:var) => do mkAppM ``AST.var #[← elabVar v]
  | `(ast| $p:lit) => return ← mkAppM ``AST.lit #[← elabLit p]
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
  | `(ast| if $a:ast then $b:ast else $c:ast) => do
    mkAppM ``AST.fork #[← elabAST a, ← elabAST b, ← elabAST c]
  | `(ast| $f:ast $a:ast) => do mkAppM ``AST.app #[← elabAST f, ← elabAST a]
  | `(ast| fun $vs:var* => $b:ast) => do
    vs.foldrM (init := ← elabAST b) fun v acc => do
      mkAppM ``AST.lam #[← elabVar v, acc]
  | `(ast| let $v:var $vs:var* := $val:ast; $b:ast) => do
    let lam ← vs.foldrM (init := ← elabAST val) fun v acc => do
      mkAppM ``AST.lam #[← elabVar v, acc]
    mkAppM ``AST.lt #[← elabVar v, lam, ← elabAST b]
  | `(ast| rec $v:var $vs:var* := $val:ast; $b:ast) => do
    let lam ← vs.foldrM (init := ← elabAST val) fun v acc => do
      mkAppM ``AST.lam #[← elabVar v, acc]
    mkAppM ``AST.rc #[← elabVar v, lam, ← elabAST b]
  | `(ast| ($x:ast)) => elabAST x
  | _ => throwUnsupportedSyntax

elab "⟦" x:ast "⟧" : term =>
  elabAST x

end Vero.Frontend.DSL
