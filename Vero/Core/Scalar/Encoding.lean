import Vero.Core.Scalar.Utils
import Vero.Core.Expr

namespace Vero.Core.Scalar

open Expr

open Std (RBMap) in
structure EncodeState where
  store : StoreF
  cache : RBMap Expr Ptr compare
  deriving Inhabited

abbrev EncodeM := StateM EncodeState

def EncodeM.addExprHash (ptr : Ptr) (expr : ExprF) : EncodeM Ptr :=
  modifyGet fun stt => (ptr, { stt with store := stt.store.insert ptr expr })

open EncodeM in
def encodeExpr (e : Expr) : EncodeM Ptr := do
  match (← get).cache.find? e with
  | some ptr => pure ptr
  | none =>
    let ptr ← match e with
      | .var n => let n := .ofNat n; addExprHash ⟨.var, n⟩ (.var n)
      | .lam b => do
        let bPtr ← encodeExpr b
        addExprHash ⟨.lam, hashPtr bPtr⟩ (.lam bPtr)
      | .app f a => do
        let fPtr ← encodeExpr f
        let aPtr ← encodeExpr a
        addExprHash ⟨.app, hashPtrPair fPtr aPtr⟩ (.app fPtr aPtr)
    modifyGet fun stt =>
      (ptr, { stt with cache := stt.cache.insert e ptr })

end Scalar

namespace Expr

open Scalar

def encode (e : Expr) : Ptr × StoreF :=
  match StateT.run (encodeExpr e) default with
  | (ptr, stt) => (ptr, stt.store)

def encode' (e : Expr) (stt : EncodeState := default) : Ptr × EncodeState :=
  StateT.run (encodeExpr e) stt

end Vero.Core.Expr
