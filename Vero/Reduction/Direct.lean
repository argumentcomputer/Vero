import Vero.Common.Typ
import Vero.Common.Expr

namespace Vero

inductive Norm where
  | lam : Expr → List Norm → Norm
  | neu : Nat  → List Norm → Norm
  deriving Inhabited

namespace Expr

mutual

  partial def eval (env : List Norm) : Expr → Norm
    | .var j => env.getD j $ .neu (j - env.length) []
    | .lam bod => .lam bod env
    | .app fnc arg => apply (fnc.eval env) (arg.eval env)

  partial def apply (fnc arg : Norm) : Norm :=
    match fnc with
    | .lam bod env => bod.eval (arg :: env)
    | .neu hd args => .neu hd (arg :: args)

end

mutual

  partial def quote (val : Norm) (shift : Nat) : Expr := match val with
    | .lam bod env => .lam $ bod.inst env 1 shift
    | .neu hd args =>
      args.foldr (fun a f => .app f $ quote a shift) (.var (hd + shift))

  partial def inst (env : List Norm) (dep shift : Nat) : Expr → Expr
    | .app fnc arg => .app (fnc.inst env dep shift) (arg.inst env dep shift)
    | .lam bod => .lam $ bod.inst env dep.succ shift
    | t@(.var j) =>
      if j < dep then t else
      match env.get? (j - dep) with
      | some val => quote val (shift + dep)
      | none     => .var (j - dep - env.length)

end

def reduce (e : Expr) : Expr :=
  quote (e.eval []) 0

end Vero.Expr
