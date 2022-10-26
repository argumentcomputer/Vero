import Vero.Circuit.Types
import Vero.Syntax.Expr

namespace Vero

namespace Compiler

abbrev Context := Std.RBMap String Nat compare

abbrev CompileM := ReaderT Context $ ExceptT String $ StateM Circuit

def addGate (g : Circuit.Gate) : CompileM Nat :=
  modifyGet fun c => (c.size, c.push g)

def withVar (s : String) (i : Nat) : CompileM α → CompileM α :=
  withReader fun e => e.insert s i

def compile : Syntax.Expr → CompileM Nat
  | .var s => do match (← read).find? s with
    | some i => addGate $ .eqId (.var i)
    | none => throw s!"Unseen variable: {s}"
  | .num n => addGate $ .eqId (.num n)
  | .binOp op e₁ e₂ => do
    let i₁ ← compile e₁
    let i₂ ← compile e₂
    let op := match op with | .add => .add | .mul => .mul
    addGate $ .eqOp op (.var i₁) (.var i₂)
  | .letIn s v b => do
    let iᵥ ← compile v
    let iₛ ← addGate $ .eqId (.var iᵥ)
    withVar s iₛ $ compile b

end Compiler

def Syntax.Expr.compile (e : Syntax.Expr) : Except String Circuit := Id.run do
  match ← StateT.run (ReaderT.run (Compiler.compile e) default) default with
  | (.error err, _) => .error err
  | (.ok _,      c) => .ok c
