import Vero.Common.Typ
import Vero.Common.Expr

/-- Tries to get the `n`-th item of a list. Also returns its explored length -/
def List.get?Len (l : List α) (n : Nat) : (Option α) × Nat :=
  let rec aux (acc : Nat) : List α → Nat → (Option α) × Nat
    | [], _ => (none, acc)
    | h :: _, 0 => (some h, acc)
    | _ :: t, n + 1 => aux acc.succ t n
  aux 0 l n

namespace Vero

inductive Norm where
  | lam : Expr → List Norm → Norm
  | neu : Nat  → List Norm → Norm
  deriving Inhabited

namespace Expr

mutual

  partial def eval (env : List Norm) : Expr → Norm
    | .var j => match env.get?Len j with
      | (some norm, _) => norm
      | (none, len) => .neu (j - len) []
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
      let j := j - dep
      match env.get?Len j with
      | (some val, _) => quote val (shift + dep)
      | (none, len) => .var (j - len)

end

def reduce (e : Expr) : Expr :=
  quote (e.eval []) 0

end Vero.Expr
