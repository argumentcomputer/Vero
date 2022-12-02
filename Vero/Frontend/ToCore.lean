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
  | .binOp .add (.lit $ .nat 0) x
  | .binOp .add x (.lit $ .nat 0)
  | .binOp .sub (.lit $ .nat 0) x
  | .binOp .sub x (.lit $ .nat 0) => x.toCore
  | .binOp .add (.lit $ .nat 1) x
  | .binOp .add x (.lit $ .nat 1) => ⟦$NAT.SUCC $x.toCore⟧
  | .binOp .sub x (.lit $ .nat 1) => ⟦$NAT.PRED $x.toCore⟧
  | .binOp .mul (.lit $ .nat 0) _
  | .binOp .mul _ (.lit $ .nat 0) => NAT.ZERO
  | .binOp op x y =>
    let (x, y) := (x.toCore, y.toCore)
    match op with
    | .add => ⟦$NAT.ADD  $x $y⟧
    | .mul => ⟦$NAT.MUL  $x $y⟧
    | .sub => ⟦$NAT.SUB  $x $y⟧
    | .div => ⟦$NAT.DIV  $x $y⟧
    | .eq  => ⟦$BOOL.EQ  $x $y⟧
    | .neq => ⟦$BOOL.NEQ $x $y⟧
    | .lt  => ⟦$BOOL.LT  $x $y⟧
    | .le  => ⟦$BOOL.LE  $x $y⟧
    | .gt  => ⟦$BOOL.LT  $y $x⟧
    | .ge  => ⟦$BOOL.LE  $y $x⟧
    | .and => ⟦$BOOL.AND $x $y⟧
    | .or  => ⟦$BOOL.OR  $x $y⟧
  | .fork a b c =>
    let b := Core.AST.lam "$" b.toCore
    let c := Core.AST.lam "$" c.toCore
    .app ⟦$FLOW.FORK $a.toCore $b $c⟧ (.var "$")
  | .lam v b => .lam v.name b.toCore
  | .app f a => .app f.toCore a.toCore
  | .rc ⟨s, _⟩ v b =>
    if v.hasFreeVar s then .app (.lam s b.toCore) (FIX $ .lam s v.toCore)
    else .app (.lam s b.toCore) v.toCore

end Vero.Frontend
