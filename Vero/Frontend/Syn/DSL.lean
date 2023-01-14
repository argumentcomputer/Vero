import Vero.Frontend.Syn.Syn

namespace Vero.Frontend.Syn.DSL

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

declare_syntax_cat  syn
scoped syntax var : syn
scoped syntax lit : syn
scoped syntax " ! " syn : syn
scoped syntax:50 syn:50 " + "  syn:51 : syn
scoped syntax:60 syn:60 " * "  syn:61 : syn
scoped syntax:50 syn:50 " - "  syn:51 : syn
scoped syntax:60 syn:60 " / "  syn:61 : syn
scoped syntax:70 syn:70 " = "  syn:71 : syn
scoped syntax:70 syn:70 " != " syn:71 : syn
scoped syntax:70 syn:70 " < "  syn:71 : syn
scoped syntax:70 syn:70 " <= " syn:71 : syn
scoped syntax:70 syn:70 " > "  syn:71 : syn
scoped syntax:70 syn:70 " >= " syn:71 : syn
scoped syntax:65 syn:65 " & "  syn:66 : syn
scoped syntax:65 syn:65 " | "  syn:66 : syn

-- assignment
scoped syntax withPosition(
  "let" var+ colGt " := " colGt syn colGt ";"
  colGe syn) : syn

-- recursive assignment
scoped syntax withPosition(
  "rec" var+ colGt " := " colGt syn colGt ";"
  colGe syn) : syn

-- anonymous lambda
scoped syntax withPosition("fun" var+ colGt " => " colGt syn) : syn

-- application
scoped syntax:50 syn syn:51 : syn

-- forks
scoped syntax withPosition(
  "if " colGt syn colGt " then "
    colGt syn colGe
  " else "
    colGt syn) : syn

-- explicit parsing priority
scoped syntax "(" syn ")" : syn

def elabBinOp (a b : Expr) : BinOp → TermElabM Expr
  | .add => mkAppM ``Syn.binOp #[mkConst ``BinOp.add, a, b]
  | .mul => mkAppM ``Syn.binOp #[mkConst ``BinOp.mul, a, b]
  | .sub => mkAppM ``Syn.binOp #[mkConst ``BinOp.sub, a, b]
  | .div => mkAppM ``Syn.binOp #[mkConst ``BinOp.div, a, b]
  | .eq  => mkAppM ``Syn.binOp #[mkConst ``BinOp.eq , a, b]
  | .neq => mkAppM ``Syn.binOp #[mkConst ``BinOp.neq, a, b]
  | .lt  => mkAppM ``Syn.binOp #[mkConst ``BinOp.lt , a, b]
  | .le  => mkAppM ``Syn.binOp #[mkConst ``BinOp.le , a, b]
  | .gt  => mkAppM ``Syn.binOp #[mkConst ``BinOp.gt , a, b]
  | .ge  => mkAppM ``Syn.binOp #[mkConst ``BinOp.ge , a, b]
  | .and => mkAppM ``Syn.binOp #[mkConst ``BinOp.and, a, b]
  | .or  => mkAppM ``Syn.binOp #[mkConst ``BinOp.or , a, b]

partial def elabSyn : TSyntax `syn → TermElabM Expr
  | `(syn| ($v:var))
  | `(syn| $v:var) => do mkAppM ``Syn.var #[← elabVar v]
  | `(syn| $p:lit) => return ← mkAppM ``Syn.lit #[← elabLit p]
  | `(syn| ! $x) => do mkAppM ``Syn.unOp #[mkConst ``UnOp.not , ← elabSyn x]
  | `(syn| $a + $b)  => do elabBinOp (← elabSyn a) (← elabSyn b) .add
  | `(syn| $a * $b)  => do elabBinOp (← elabSyn a) (← elabSyn b) .mul
  | `(syn| $a - $b)  => do elabBinOp (← elabSyn a) (← elabSyn b) .sub
  | `(syn| $a / $b)  => do elabBinOp (← elabSyn a) (← elabSyn b) .div
  | `(syn| $a = $b)  => do elabBinOp (← elabSyn a) (← elabSyn b) .eq
  | `(syn| $a != $b) => do elabBinOp (← elabSyn a) (← elabSyn b) .neq
  | `(syn| $a < $b)  => do elabBinOp (← elabSyn a) (← elabSyn b) .lt
  | `(syn| $a <= $b) => do elabBinOp (← elabSyn a) (← elabSyn b) .le
  | `(syn| $a > $b)  => do elabBinOp (← elabSyn a) (← elabSyn b) .gt
  | `(syn| $a >= $b) => do elabBinOp (← elabSyn a) (← elabSyn b) .ge
  | `(syn| $a & $b)  => do elabBinOp (← elabSyn a) (← elabSyn b) .and
  | `(syn| $a | $b)  => do elabBinOp (← elabSyn a) (← elabSyn b) .or
  | `(syn| if $a:syn then $b:syn else $c:syn) => do
    mkAppM ``Syn.fork #[← elabSyn a, ← elabSyn b, ← elabSyn c]
  | `(syn| $f:syn $a:syn) => do mkAppM ``Syn.app #[← elabSyn f, ← elabSyn a]
  | `(syn| fun $vs:var* => $b:syn) => do
    vs.foldrM (init := ← elabSyn b) fun v acc => do
      mkAppM ``Syn.lam #[← elabVar v, acc]
  | `(syn| let $v:var $vs:var* := $val:syn; $b:syn) => do
    let lam ← vs.foldrM (init := ← elabSyn val) fun v acc => do
      mkAppM ``Syn.lam #[← elabVar v, acc]
    mkAppM ``Syn.lt #[← elabVar v, lam, ← elabSyn b]
  | `(syn| rec $v:var $vs:var* := $val:syn; $b:syn) => do
    let lam ← vs.foldrM (init := ← elabSyn val) fun v acc => do
      mkAppM ``Syn.lam #[← elabVar v, acc]
    mkAppM ``Syn.rc #[← elabVar v, lam, ← elabSyn b]
  | `(syn| ($x:syn)) => elabSyn x
  | _ => throwUnsupportedSyntax

elab "⟦" x:syn "⟧" : term =>
  elabSyn x

end Vero.Frontend.Syn.DSL
