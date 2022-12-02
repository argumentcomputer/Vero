namespace Vero

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

end Vero.Expr
