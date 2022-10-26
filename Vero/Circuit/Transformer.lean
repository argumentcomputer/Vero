import Vero.Syntax.Expr
import Vero.Circuit.Optimization

namespace Vero

namespace Compiler

open Circuit

abbrev CompileM := ReaderT (Std.RBMap String Circuit compare) Id

def withVar (s : String) (c : Circuit) : CompileM α → CompileM α :=
  withReader fun e => e.insert s c

def compile : Syntax.Expr → CompileM Circuit
  | .var s => return match (← read).find? s with
    | some i => .uno (.inner i)
    | none => .uno (.outer s)
  | .num n => return .uno (.const n)
  | .binOp op e₁ e₂ => do
    let g₁ ← compile e₁
    let g₂ ← compile e₂
    return match op with
    | .add => .add (.inner g₁) (.inner g₂)
    | .mul => .mul (.inner g₁) (.inner g₂)
  | .letIn s v b => do
    let gᵥ ← compile v
    let gₛ := .uno (.inner gᵥ)
    withVar s gₛ $ compile b

end Compiler

def Syntax.Expr.toCircuit (e : Syntax.Expr) : Circuit :=
  (ReaderT.run (Compiler.compile e.normalize) default).optimize
