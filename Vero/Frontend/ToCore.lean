import Vero.Frontend.AST
import Vero.Core.Data

namespace Vero.Frontend

open Core.Data Core.DSL in
def AST.toCore : AST → Core.AST
  | .lit $ .nat n => NAT n
  | .lit $ .bool true  => BOOL.TT
  | .lit $ .bool false => BOOL.FF
  | .var v => .var v.name
  | .unOp .not x => ⟦$BOOL.NOT $x.toCore⟧
  | .binOp .add (.lit $ .nat x) (.lit $ .nat y) => NAT (x + y)
  | .binOp .mul (.lit $ .nat x) (.lit $ .nat y) => NAT (x * y)
  | .binOp .sub (.lit $ .nat x) (.lit $ .nat y) => NAT (x - y)
  | .binOp .div (.lit $ .nat x) (.lit $ .nat y) => NAT (x / y)
  -- neutral arithmetics
  | .binOp .add (.lit $ .nat 0) x
  | .binOp .add x (.lit $ .nat 0)
  | .binOp .mul (.lit $ .nat 1) x
  | .binOp .mul x (.lit $ .nat 1)
  | .binOp .div x (.lit $ .nat 1)
  | .binOp .sub (.lit $ .nat 0) x
  | .binOp .sub x (.lit $ .nat 0) => x.toCore
  -- neighbors arithmetics
  | .binOp .add (.lit $ .nat 1) x
  | .binOp .add x (.lit $ .nat 1) => ⟦$NAT.SUCC $x.toCore⟧
  | .binOp .sub x (.lit $ .nat 1) => ⟦$NAT.PRED $x.toCore⟧
  -- always zero
  | .binOp .div (.lit $ .nat 0) _
  | .binOp .div _ (.lit $ .nat 0) -- trash value
  | .binOp .mul (.lit $ .nat 0) _
  | .binOp .mul _ (.lit $ .nat 0) => NAT.ZERO
  | .binOp .sub x y =>
    if x == y then NAT.ZERO else ⟦$NAT.SUB $x.toCore $y.toCore⟧
  | .binOp op x y =>
    let (x, y) := (x.toCore, y.toCore)
    match op with
    | .add => ⟦$NAT.ADD  $x $y⟧
    | .mul => ⟦$NAT.MUL  $x $y⟧
    | .sub => unreachable!
    | .div => .app (.app NAT.DIV x) y--⟦$NAT.DIV  $x $y⟧
    | .eq  => ⟦$BOOL.EQ  $x $y⟧
    | .neq => ⟦$BOOL.NEQ $x $y⟧
    | .lt  => ⟦$BOOL.LT  $x $y⟧
    | .le  => ⟦$BOOL.LE  $x $y⟧
    | .gt  => ⟦$BOOL.LT  $y $x⟧
    | .ge  => ⟦$BOOL.LE  $y $x⟧
    | .and => ⟦$BOOL.AND $x $y⟧
    | .or  => ⟦$BOOL.OR  $x $y⟧
  | .fork a b c =>
    let b := Core.AST.lam "ζ" b.toCore
    let c := Core.AST.lam "ζ" c.toCore
    .app ⟦$FLOW.FORK $a.toCore $b $c⟧ (.var "ζ")
  | .lam v b => .lam v.name b.toCore
  | .app (.lam ⟨s, _⟩ (.var ⟨s', _⟩)) x => if s == s' then x.toCore else .var s'
  | .app f a => .app f.toCore a.toCore
  | .lt ⟨s, _⟩ v (.var ⟨s', _⟩) => if s == s' then v.toCore else .var s'
  | .lt ⟨s, _⟩ v b => .app (.lam s b.toCore) v.toCore
  | .rc ⟨s, _⟩ v b =>
    if v.hasFreeVar s then .app (.lam s b.toCore) (FIX $ .lam s v.toCore)
    else .app (.lam s b.toCore) v.toCore

end Vero.Frontend
