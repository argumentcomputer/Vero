import Vero.Hashing.Datatypes

namespace Vero.Hashing

open Reduce (Expr)

open Std (RBMap) in
abbrev EvalM := ReaderT StoreF $ ExceptT String $ StateM (RBMap Ptr Expr compare)

def getExpr (ptr : Ptr) : EvalM ExprF := do
  match (← read).exprs.find? ptr with
  | some e => pure e
  | none => throw s!"pointer not found in the store: {ptr}"

partial def eval (ptr : Ptr) : EvalM Expr := do
  match (← get).find? ptr with
  | some e => pure e
  | none =>
    let e ← match ptr with
      | ⟨.var, n⟩ => pure $ .var n.val
      | ⟨.lam, _⟩ => match ← getExpr ptr with
        | _ => sorry
      | _ => sorry
    modifyGet fun cache => (e, cache.insert ptr e)

end Vero.Hashing
