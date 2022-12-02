import Vero.Scalar.Datatypes
import Vero.Scalar.Utils

namespace Vero.Scalar

structure EvalState where
  store : StoreF
  cache : Std.RBMap Ptr Ptr compare

abbrev ReduceM := ExceptT String $ StateM EvalState

def getExpr (ptr : Ptr) : ReduceM ExprF := do
  match (← get).store.find? ptr with
  | some e => pure e
  | none => throw s!"pointer not found in the store: {ptr}"

def getLamBody (ptr : Ptr) : ReduceM Ptr := do
  match ← getExpr ptr with
  | .lam b => pure b
  | x => throw s!"expected a lam expression but got {x}"

def getAppFunArg (ptr : Ptr) : ReduceM (Ptr × Ptr) := do
  match ← getExpr ptr with
  | .app f a => pure (f, a)
  | x => throw s!"expected an app expression but got {x}"

def ReduceM.addExprHash (ptr : Ptr) (expr : ExprF) : ReduceM Ptr :=
  modifyGet fun stt => (ptr, { stt with store := stt.store.insert ptr expr })

open ReduceM

partial def shiftM (dep inc : F) (ptr : Ptr) : ReduceM Ptr :=
  match ptr.tag with
  | .var =>
    if ptr.val >= dep then
      let n := ptr.val + inc
      addExprHash ⟨.var, n⟩ (.var n)
    else return ptr
  | .lam => do
    let b ← getLamBody ptr
    let b ← shiftM dep.succ inc b
    addExprHash ⟨.lam, hashPtr b⟩ (.lam b)
  | .app => do
    let (f, a) ← getAppFunArg ptr
    let f ← shiftM dep inc f
    let a ← shiftM dep inc a
    addExprHash ⟨.app, hashPtrPair f a⟩ (.app f a)

partial def substM (dep : F) (arg target : Ptr) : ReduceM Ptr :=
  match target.tag with
  | .var => match compare target.val dep with
    | .lt => pure target
    | .eq => shiftM F.zero dep arg
    | .gt => let n := target.val.pred; addExprHash ⟨.var, n⟩ (.var n)
  | .lam => do
    let b ← getLamBody target
    let b ← substM dep.succ arg b
    addExprHash ⟨.lam, hashPtr b⟩ (.lam b)
  | .app => do
    let (f, a) ← getAppFunArg target
    let f ← substM dep arg f
    let a ← substM dep arg a
    addExprHash ⟨.app, hashPtrPair f a⟩ (.app f a)

partial def reduceM (ptr : Ptr) : ReduceM Ptr := do
  match (← get).cache.find? ptr with
  | some ptr => pure ptr
  | none =>
    let ptr' ← match ptr.tag with
      | .var
      | .lam => pure ptr
      | .app =>
        let (f, a) ← getAppFunArg ptr
        let f ← reduceM f
        match f.tag with
        | .lam => reduceM $ ← substM F.zero (← reduceM a) (← getLamBody f)
        | _ => let a ← reduceM a; addExprHash ⟨.app, hashPtrPair f a⟩ (.app f a)
    modifyGet fun stt => (ptr', { stt with cache := stt.cache.insert ptr ptr' })

def reduce (ptr : Ptr) (store : StoreF) : Except String (Ptr × StoreF) :=
  match StateT.run (reduceM ptr) ⟨store, default⟩ with
  | (.error err, _) => .error err
  | (.ok ptr, ⟨store, _⟩) => .ok (ptr, store)

end Vero.Scalar
