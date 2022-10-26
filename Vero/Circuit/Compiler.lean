import Vero.Circuit.Types
import Vero.Syntax.Expr

namespace Vero

namespace Compiler

open Circuit

abbrev CompileM := ReaderT (Std.RBMap String Gate compare) Id

def withVar (s : String) (g : Gate) : CompileM α → CompileM α :=
  withReader fun e => e.insert s g

def compile : Syntax.Expr → CompileM Gate
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

def Syntax.Expr.compile (e : Syntax.Expr) : Circuit.Gate :=
  (ReaderT.run (Compiler.compile e.normalize) default).optimize
