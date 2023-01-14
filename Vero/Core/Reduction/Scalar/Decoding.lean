import Vero.Core.Expr
import Vero.Core.Reduction.Scalar.Datatypes

namespace Vero.Core.Scalar

open Expr

structure DecodeContext where
  store : StoreF
  visit : Std.RBSet Ptr compare

abbrev DecodeM := ReaderT DecodeContext $ ExceptT String $
  StateM (Std.RBMap Ptr Expr compare)

def withVisiting (ptr : Ptr) : DecodeM α → DecodeM α :=
  withReader fun ctx => { ctx with visit := ctx.visit.insert ptr }

partial def decodeExpr (ptr : Ptr) : DecodeM Expr := do
  match (← get).find? ptr with
  | some ast => pure ast
  | none =>
    if (← read).visit.contains ptr then throw "Cycle of pointers detected"
    else withVisiting ptr do
      let ast ← match ptr.tag with
        | .var => pure $ .var ptr.val.val
        | _ => match (← read).store.find? ptr with
          | none => throw s!"Pointer not found in the store: {ptr}"
          | some eF => match (ptr.tag, eF) with
            | (.lam, .lam b) => pure $ .lam (← decodeExpr b)
            | (.app, .app f a) => pure $ .app (← decodeExpr f) (← decodeExpr a)
            | _ => throw s!"Tag {ptr.tag} incompatible with expression {eF}"
      modifyGet fun stt => (ast, stt.insert ptr ast)

def decode (ptr : Ptr) (store : StoreF) : Except String Expr :=
  (StateT.run (ReaderT.run (decodeExpr ptr) ⟨store, default⟩) default).1

end Vero.Core.Scalar
