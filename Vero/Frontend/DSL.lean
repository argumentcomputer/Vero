import Vero.Frontend.AST

namespace Vero.Frontend.DSL

open Lean Elab Meta Term

declare_syntax_cat           lit
scoped syntax "tt"         : lit
scoped syntax "ff"         : lit
scoped syntax num          : lit
scoped syntax "+" noWs num : lit
scoped syntax "-" noWs num : lit

def mkApp' (name : Name) (e : Lean.Expr) : Lean.Expr :=
  mkApp (mkConst name) e

def elabLit : TSyntax `lit → TermElabM Lean.Expr
  | `(lit| tt) => mkAppM ``Lit.bool #[mkConst ``true]
  | `(lit| ff) => mkAppM ``Lit.bool #[mkConst ``false]
  | `(lit| $n:num) => mkAppM ``Lit.nat #[mkNatLit n.getNat]
  | `(lit| +$n:num) =>
    mkAppM ``Lit.int #[mkApp' ``Int.ofNat (mkNatLit n.getNat)]
  | `(lit| -$n:num) => mkAppM ``Lit.int $ match n.getNat with
    | 0       => #[mkApp' ``Int.ofNat (mkConst ``Nat.zero)]
    | (n + 1) => #[mkApp' ``Int.negSucc (mkNatLit n)]
  | _ => throwUnsupportedSyntax

declare_syntax_cat               type
scoped syntax "nat"            : type
scoped syntax "int"            : type
scoped syntax "bool"           : type
scoped syntax type " . "  type : type
scoped syntax type " -> " type : type
scoped syntax "(" type ")"     : type

partial def elabType : TSyntax `type → TermElabM Lean.Expr
  | `(type| nat)  => mkConst ``Typ.nat
  | `(type| int)  => mkConst ``Typ.int
  | `(type| bool) => mkConst ``Typ.bool
  | `(type| $t₁:type . $t₂:type) => do
    mkAppM ``Typ.pair #[← elabType t₁, ← elabType t₂]
  | `(type| $t₁:type -> $t₂:type) => do
    mkAppM ``Typ.pi #[← elabType t₁, ← elabType t₂]
  | `(type| ($t:type)) => elabType t
  | _ => throwUnsupportedSyntax

declare_syntax_cat var
scoped syntax ident (":" type)? : var
scoped syntax "(" var ")" : var

def mkVarNone (n : String) : Var :=
  ⟨n, none⟩

def mkVarSome (n : String) (typ : Typ) : Var :=
  ⟨n, some typ⟩

def elabStr (i : TSyntax `ident) : Expr :=
  mkStrLit (i.getId.toString false)

partial def elabVar : TSyntax `var → TermElabM Lean.Expr
  | `(var| $i:ident) => return mkApp' ``mkVarNone (elabStr i)
  | `(var| $i:ident : $t:type) => do
    mkAppM ``mkVarSome #[elabStr i, ← elabType t]
  | `(var| ($v:var)) => elabVar v
  | _ => throwUnsupportedSyntax

declare_syntax_cat  ast
scoped syntax var : ast
scoped syntax lit : ast
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

-- assignment
scoped syntax withPosition(
  var+ colGt " := " colGt ast colGt ";"
  colGe ast) : ast

-- anonymous lambda
scoped syntax withPosition(var+ colGt " => " colGt ast) : ast

-- application
scoped syntax:49 ast (colGt ast:50)+ : ast

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
  | `(ast| $f:ast $[$as:ast]*) => do
    as.foldlM (init := ← elabAST f) fun acc a => do
      mkAppM ``AST.app #[acc, ← elabAST a]
  | `(ast| $vs:var* $v:var => $b:ast) => do
    let init ← mkAppM ``AST.lam #[← elabVar v, ← elabAST b]
    vs.foldrM (init := init) fun v acc => do
      mkAppM ``AST.lam #[← elabVar v, acc]
  | `(ast| $v:var $vs:var* := $val:ast; $b:ast) => do
    let lam ← vs.foldrM (init := ← elabAST val) fun v acc => do
      mkAppM ``AST.lam #[← elabVar v, acc]
    mkAppM ``AST.letIn #[← elabVar v, lam, ← elabAST b]
  | `(ast| if $a:ast then $b:ast else $c:ast) => do
    mkAppM ``AST.fork #[← elabAST a, ← elabAST b, ← elabAST c]
  | `(ast| ($x:ast)) => elabAST x
  | _ => throwUnsupportedSyntax

elab "⟦ " x:ast " ⟧" : term =>
  elabAST x

end Vero.Frontend.DSL
