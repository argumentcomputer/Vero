import Vero.Syntax.Expr
import Vero.Circuit.Optimization

namespace Vero.Circuit.Transformer

open Circuit Syntax

abbrev CompileM := ReaderT (Lean.RBMap String Expr compare) $ ExceptT String Id

def withVar (s : String) (e : Expr) : CompileM α → CompileM α :=
  withReader fun ctx => ctx.insert s e

partial def transform : Syntax.Expr → CompileM Circuit
  | .var s => do match (← read).find? s with
    | some e => return .uno (.inner (← transform e))
    | none => return .uno (.outer s)
  | .lit $ .num n => return .uno (.const n)
  | .binOp (.add) e₁ e₂ => do
    let c₁ ← transform e₁
    let c₂ ← transform e₂
    return .duo .add (.inner c₁) (.inner c₂)
  | .binOp (.mul) e₁ e₂ => do
    let c₁ ← transform e₁
    let c₂ ← transform e₂
    return .duo .mul (.inner c₁) (.inner c₂)
  | .letIn s v b => withVar s v $ transform b
  | .lam a b => withVar a (.var a) $ transform b
  | _ => throw "TODO"

end Circuit.Transformer

def Syntax.Expr.toCircuit (e : Syntax.Expr) : Except String Circuit :=
  match (ReaderT.run (Circuit.Transformer.transform e.normalize) default) with
  | .error err => throw err
  | .ok c => return c.optimize

end Vero
