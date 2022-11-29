import Vero.Frontend.TypeInference
import Vero.Core.Data

namespace Vero.Frontend

open Core.Data Core.DSL in
def AST.toCore : AST → Core.AST
  | .lit $ .nat n => NAT n
  | .lit $ .int i => INT i
  | .lit $ .bool true  => BOOL.TRUE
  | .lit $ .bool false => BOOL.FALSE
  | .var v => .var v.1
  | .unOp .neg x => ⟦$INT.NEG  $x.toCore⟧
  | .unOp .not x => ⟦$BOOL.NOT $x.toCore⟧
  | .binOp .. => sorry -- nat vs int issue; maybe ditch one of them
  | .fork a b c => ⟦$FLOW.FORK $a.toCore $b.toCore $c.toCore⟧
  | .lam v b => .lam v.1 b.toCore
  | .app f a => .app f.toCore a.toCore

end Vero.Frontend
