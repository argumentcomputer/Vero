import Vero.Frontend.AST
import Vero.Core.Data

namespace Vero.Frontend

open Core.Data Core.DSL in
def AST.toCore : AST → Core.AST
  | .lit $ .nat n => NAT n
  | .lit $ .bool true  => BOOL.TRUE
  | .lit $ .bool false => BOOL.FALSE
  | .var v => .var v.name
  | .unOp .not x => ⟦$BOOL.NOT $x.toCore⟧
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
    if v.hasFreeVar s then .app (.lam s b.toCore) (.app FIX.Z (.lam s v.toCore))
    else .app (.lam s b.toCore) v.toCore

end Vero.Frontend
