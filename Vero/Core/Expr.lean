namespace Vero.Core

inductive Expr
  | var : Nat → Expr
  | lam : Expr → Expr
  | app : Expr → Expr → Expr
  deriving BEq, Ord, Inhabited

namespace Expr

mutual 
  def toString : Expr → String
    | .var i => s!"^{i}"
    | .lam b => s!"(λ {b.lamsToString})"
    | .app x y@(.app ..) => s!"{x.toString} ({y.toString})"
    | .app x y => s!"{x.toString} {y.toString}"

  def lamsToString : Expr → String
    | .lam b@(.lam _) => s!"λ {b.lamsToString}"
    | .lam b => s!"λ {b.toString}"
    | x => s!"{x.toString}"
end

instance : ToString Expr where 
  toString := Expr.toString

def toNat (e : Expr) : Except Expr Nat :=
  let rec aux (n : Nat) : Expr → Except Expr Nat
    | .lam (.lam (.var 1)) => return n
    | .lam (.lam (.app (.var 0) x)) => aux n.succ x
    | x => throw x
  aux 0 e

def toBool : Expr → Except Expr Bool
  | .lam (.lam (.var 0)) => return false
  | .lam (.lam (.var 1)) => return true
  | x => throw x

end Expr

end Vero.Core
