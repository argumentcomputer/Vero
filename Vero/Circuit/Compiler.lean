import Vero.Circuit.Types
import Vero.Syntax.Expr

namespace Vero

namespace Compiler

abbrev Context := Std.RBMap String Nat compare

abbrev CompileM := ReaderT Context $ StateM Circuit

def addGate (g : Circuit.Gate) : CompileM Nat :=
  modifyGet fun c => (c.size, c.push g)

def withVar (s : String) (i : Nat) : CompileM α → CompileM α :=
  withReader fun e => e.insert s i

def compile : Syntax.Expr → CompileM Nat
  | .var s => do match (← read).find? s with
    | some i => addGate $ .uno (.inner i)
    | none => addGate $ .uno (.outer s)
  | .num n => addGate $ .uno (.const n)
  | .binOp op e₁ e₂ => do
    let i₁ ← compile e₁
    let i₂ ← compile e₂
    match op with
    | .add => addGate $ .add (.inner i₁) (.inner i₂)
    | .mul => addGate $ .mul (.inner i₁) (.inner i₂)
  | .letIn s v b => do
    let iᵥ ← compile v
    let iₛ ← addGate $ .uno (.inner iᵥ)
    withVar s iₛ $ compile b

end Compiler

def Syntax.Expr.compile (e : Syntax.Expr) : Circuit :=
  (StateT.run (ReaderT.run (Compiler.compile e.normalize) default) default).2.optimize
