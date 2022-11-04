import Vero.Syntax.Expr
import Vero.Circuit.Optimization

namespace Vero.Circuit.Transformer

open Circuit

abbrev CompileM := ReaderT (Std.RBMap String Circuit compare) $ ExceptT String Id

def withVar (s : String) (c : Circuit) : CompileM α → CompileM α :=
  withReader fun e => e.insert s c

def transform : Syntax.Expr → CompileM Circuit
  | .var s => return match (← read).find? s with
    | some i => .uno (.inner i)
    | none => .uno (.outer s)
  | .num n => return .uno (.const n)
  | .binOp op e₁ e₂ => do
    let g₁ ← transform e₁
    let g₂ ← transform e₂
    let op := match op with | .add => .add | .mul => .mul
    return .duo op (.inner g₁) (.inner g₂)
  | .letIn s v b => do
    let gᵥ ← transform v
    let gₛ := .uno (.inner gᵥ)
    withVar s gₛ $ transform b
  | .lam a b => do
    let gₐ := .uno (.outer a)
    withVar a gₐ $ transform b
  | .app f a => do match (← transform f).optimize with -- is this correct?
    | .uno (.outer _) => return .uno (.inner $ ← transform a)
    | .duo op (.outer _) i => return .duo op (.inner $ ← transform a) i
    | .duo op i (.outer _) => return .duo op i (.inner $ ← transform a)
    | _ => throw "Application on a circuit that doesn't allow outer input"

end Circuit.Transformer

def Syntax.Expr.toCircuit (e : Syntax.Expr) : Except String Circuit :=
  match (ReaderT.run (Circuit.Transformer.transform e.normalize) default) with
  | .error err => throw err
  | .ok c => return c.optimize

end Vero
