import Vero.Scalar.Datatypes
import Vero.Scalar.Utils
import YatimaStdLib.Ord

namespace Vero.Scalar

structure EvalState where
  store : StoreF
  evalCache  : Std.RBMap (Ptr × Ptr) Ptr compare
  applyCache : Std.RBMap (Ptr × Ptr) Ptr compare
  deriving Inhabited

abbrev ReduceM := ExceptT String $ StateM EvalState

def getExpr (ptr : Ptr) : ReduceM ExprF := do
  match (← get).store.find? ptr with
  | some e => pure e
  | none => throw s!"pointer not found in the store: {ptr}"

def getLamBody (ptr : Ptr) : ReduceM Ptr := do
  match ← getExpr ptr with
  | .lam b => pure b
  | x => throw s!"expected a lam expression but got {x}"

def getAppFncArg (ptr : Ptr) : ReduceM (Ptr × Ptr) := do
  match ← getExpr ptr with
  | .app f a => pure (f, a)
  | x => throw s!"expected an app expression but got {x}"

def getNormLamBodyEnv (ptr : Ptr) : ReduceM (Ptr × Ptr) := do
  match ← getExpr ptr with
  | .normLam b e => pure (b, e)
  | x => throw s!"expected a normLam expression but got {x}"

def getNormNeuFncArgs (ptr : Ptr) : ReduceM (F × Ptr) := do
  match ← getExpr ptr with
  | .normNeu v a => pure (v, a)
  | x => throw s!"expected a normLam expression but got {x}"

def ReduceM.addExprF (ptr : Ptr) (exprF : ExprF) : ReduceM Ptr :=
  modifyGet fun stt => (ptr, { stt with store := stt.store.insert ptr exprF })

mutual

open ReduceM (addExprF)

partial def evalM (exprPtr envPtr : Ptr) : ReduceM Ptr := do
  match (← get).evalCache.find? (exprPtr, envPtr) with
  | some normPtr => pure normPtr
  | none =>
    let normPtr ← match exprPtr.tag with
      | .var => sorry
      | .lam =>
        let bodPtr ← getLamBody exprPtr
        addExprF ⟨.normLam, hashPtrPair bodPtr envPtr⟩ (.normLam bodPtr envPtr)
      | .app =>
        let (fncPtr, argPtr) ← getAppFncArg exprPtr
        applyM (← evalM fncPtr envPtr) (← evalM argPtr envPtr)
      | _ => throw s!"invalid pointer for evaluation: {exprPtr}"
    modifyGet fun stt => (normPtr, { stt with
      evalCache := stt.evalCache.insert (exprPtr, envPtr) normPtr })

partial def applyM (fncPtr argPtr : Ptr) : ReduceM Ptr := do
  match (← get).applyCache.find? (fncPtr, argPtr) with
  | some normPtr => pure normPtr
  | none =>
    let normPtr ← match fncPtr.tag with
      | .normLam => sorry
      | .normNeu => sorry
      | _ => throw s!"invalid pointer for application function: {fncPtr}"
    modifyGet fun stt => (normPtr, { stt with
      evalCache := stt.evalCache.insert (fncPtr, argPtr) normPtr })

end

mutual

partial def quoteM (normPtr : Ptr) (shift : Nat) : ReduceM Ptr := sorry

partial def instM (exprPtr envPtr : Ptr) (dep shift : Nat) : ReduceM Ptr := sorry

end

def reduceM (ptr : Ptr) : ReduceM Ptr := do
  quoteM (← evalM ptr ⟨.envNil, .zero⟩) 0

def reduce (ptr : Ptr) (store : StoreF) : Except String (Ptr × StoreF) :=
  match StateT.run (reduceM ptr) ⟨store, default, default⟩ with
  | (.error err, _) => .error err
  | (.ok ptr, ⟨store, _, _⟩) => .ok (ptr, store)

end Vero.Scalar
