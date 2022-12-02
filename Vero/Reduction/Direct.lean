import Vero.Common.Typ
import Vero.Common.Expr

namespace Vero.Expr

def shift (dep inc : Nat) : Expr → Expr
  | .var n => if n >= dep then .var (n + inc) else .var n
  | .lam b => .lam (shift (dep + 1) inc b)
  | .app x y => .app (shift dep inc x) (shift dep inc y)

def subst (dep : Nat) (arg : Expr) : Expr → Expr
  | .var n => match compare n dep with
    | .lt => .var n
    | .eq => shift 0 dep arg
    | .gt => .var (n - 1)
  | .lam b => .lam (subst (dep + 1) arg b)
  | .app x y => .app (subst dep arg x) (subst dep arg y)

partial def reduce : Expr → Expr
  | .app fnc arg => match reduce fnc with
    | .lam bod => reduce (subst 0 arg.reduce bod)
    | fnc' => .app fnc' arg.reduce
  -- | .lam b => .lam $ reduce b
  | x => x

end Vero.Expr
