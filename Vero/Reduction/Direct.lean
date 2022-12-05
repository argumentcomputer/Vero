import Vero.Common.Typ
import Vero.Common.Expr

namespace Vero.Expr

def shift (dep inc : Nat) : Expr → Expr
  | t@(.var n) => if n >= dep then .var (n + inc) else t
  | .lam b => .lam (shift (dep + 1) inc b)
  | .app x y => .app (shift dep inc x) (shift dep inc y)

def subst (dep : Nat) (arg : Expr) : Expr → Expr
  | t@(.var n) => match compare n dep with
    | .lt => t
    | .eq => shift 0 dep arg
    | .gt => .var (n - 1)
  | .lam b => .lam (subst (dep + 1) arg b)
  | .app x y => .app (subst dep arg x) (subst dep arg y)

partial def reduce : Expr → Expr
  | .app fnc arg =>
    let arg := arg.reduce
    match reduce fnc with
    | .lam bod => reduce (subst 0 arg bod)
    | fnc' => .app fnc' arg
  | x => x

end Vero.Expr

-- Eval apply reduction style, strict version
namespace Vero.Strict

inductive Value where
  | lam : Expr → List Value → Value
  | neu : Nat  → List Value → Value
  deriving Inhabited

mutual
  partial def eval (term : Expr) (env : List Value) : Value := match term with
    | Expr.app fnc arg => apply (eval fnc env) (eval arg env)
    | Expr.lam bod => .lam bod env
    | Expr.var j =>
      match env.get? j with
      | some val => val
      | none => .neu (j-env.length) []

  partial def apply (fnc : Value) (arg : Value) : Value := match fnc with
    | .lam bod env => eval bod (arg :: env)
    | .neu hd args => .neu hd (arg :: args)
end

mutual
  partial def quote (val : Value) (shift : Nat) : Expr := match val with
  | .lam bod env => .lam $ instantiate bod env 1 shift
  | .neu hd args => args.foldr (fun a f => .app f $ quote a shift) (.var (hd+shift))

  partial def instantiate (term : Expr) (env : List Value) (dep : Nat) (shift : Nat) : Expr := match term with
  | Expr.app fnc arg => Expr.app (instantiate fnc env dep shift) (instantiate arg env dep shift)
  | Expr.lam bod => Expr.lam (instantiate bod env (dep+1) shift)
  | t@(Expr.var j) =>
    if j < dep then t else
    match env.get? (j-dep) with
    | some val =>
      quote val (shift+dep)
    | none   => .var (j-dep-env.length)
end

end Vero.Strict

-- Eval apply reduction style, non-strict version. It's not lazy because it doesn't update the thunks
namespace Vero.NonStrict

mutual
  inductive Value where
    | lam : Expr → List Thunk → Value
    | neu : Nat  → List Thunk → Value
    deriving Inhabited

  inductive Thunk where
    | freeze (expr : Expr) (env  : List Thunk)
    deriving Inhabited
end

def Thunk.thawWith (thunk : Thunk) (thaw : Expr → List Thunk → A) : A :=
  match thunk with
  | .freeze expr env => thaw expr env

mutual
  partial def eval (term : Expr) (env : List Thunk) : Value :=
    match term with
    | Expr.app fnc arg => apply (eval fnc env) (.freeze arg env)
    | Expr.lam bod => .lam bod env
    | Expr.var j =>
      match env.get? j with
      | some val => val.thawWith eval
      | none => .neu (j-env.length) []

  partial def apply (fnc : Value) (arg : Thunk) : Value := match fnc with
    | .lam bod env => eval bod (arg :: env)
    | .neu hd args => .neu hd (arg :: args)
end

mutual
  partial def quote (val : Value) (shift : Nat) : Expr :=
    match val with
    | .lam bod env => .lam $ instantiate bod env 1 shift
    | .neu hd args => args.foldr (fun a f => .app f $ a.thawWith (instantiate · · 0 shift)) (.var (hd+shift))

  partial def instantiate (term : Expr) (env : List Thunk) (dep : Nat) (shift : Nat) : Expr :=
    match term with
    | Expr.app fnc arg => Expr.app (instantiate fnc env dep shift) (instantiate arg env dep shift)
    | Expr.lam bod => Expr.lam (instantiate bod env (dep+1) shift)
    | t@(Expr.var j) =>
      if j < dep then t else
      match env.get? (j-dep) with
      | some thunk =>
        thunk.thawWith (instantiate · · 0 (shift+dep))
      | none   => .var (j-dep-env.length)
end

end Vero.NonStrict
