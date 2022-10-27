import Vero.Syntax.Expr
import Vero.Circuit.Optimization

namespace Vero.Circuit.Transformer

open Circuit

abbrev CompileM := ReaderT (Std.RBMap String Circuit compare) Id

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

end Circuit.Transformer

def Syntax.Expr.toCircuit (e : Syntax.Expr) : Circuit :=
  (ReaderT.run (Circuit.Transformer.transform e.normalize) default).optimize

end Vero
