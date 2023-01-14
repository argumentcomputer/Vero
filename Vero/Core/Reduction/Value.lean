import Vero.Core.Expr
import Vero.Frontend.Typ

namespace Vero.Core

inductive Value
  | expr : Expr → Value
  | nat  : Nat → Value
  | bool : Bool → Value
  | pair : Value → Value → Value
  deriving Inhabited, BEq

namespace Value

protected def toString : Value → String
  | .expr e => toString e
  | .nat  n => toString n
  | .bool b => toString b
  | .pair f s => s!"({f.toString} . {s.toString})"

instance : ToString Value := ⟨Value.toString⟩

end Vero.Core.Value
