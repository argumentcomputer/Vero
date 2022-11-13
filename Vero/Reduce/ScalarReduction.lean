import Vero.Hashing.Datatypes
import Vero.Hashing.Utils

namespace Vero.Hashing

structure EvalState where
  store : Std.RBMap Ptr ExprF compare
  cache : Std.RBMap Ptr Ptr   compare

open Std (RBMap) in
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

def addExprHash (ptr : Ptr) (expr : ExprF) : ReduceM Ptr :=
  modifyGet fun stt => (ptr, { stt with store := stt.store.insert ptr expr })

partial def shift (dep inc : F) (ptr : Ptr) : ReduceM Ptr :=
  match ptr.tag with
  | .var =>
    if ptr.val >= dep then
      let n := ptr.val + inc
      addExprHash ⟨.var, n⟩ (.var n)
    else return ptr
  | .lam => do
    let b ← getLamBody ptr
    let b ← shift dep.succ inc b
    addExprHash ⟨.lam, hashPtr b⟩ (.lam b)
  | .app => do
    let (f, a) ← getAppFunArg ptr
    let f ← shift dep inc f
    let a ← shift dep inc a
    addExprHash ⟨.app, hashPtrPair f a⟩ (.app f a)

partial def subst (dep : F) (arg target : Ptr) : ReduceM Ptr :=
  match target.tag with
  | .var => match compare target.val dep with
    | .lt => pure target
    | .eq => shift F.zero dep arg
    | .gt => let n := target.val.pred; addExprHash ⟨.var, n⟩ (.var n)
  | .lam => do
    let b ← getLamBody target
    let b ← subst dep.succ arg b
    addExprHash ⟨.lam, hashPtr b⟩ (.lam b)
  | .app => do
    let (f, a) ← getAppFunArg target
    let f ← subst dep arg f
    let a ← subst dep arg a
    addExprHash ⟨.app, hashPtrPair f a⟩ (.app f a)

partial def reduce (ptr : Ptr) : ReduceM Ptr := do
  match (← get).cache.find? ptr with
  | some ptr => pure ptr
  | none =>
    let ptr' ← match ptr.tag with
      | .var => pure ptr
      | .lam =>
        let b ← getLamBody ptr
        let b ← reduce b
        addExprHash ⟨.lam, hashPtr b⟩ (.lam b)
      | .app =>
        let (f, a) ← getAppFunArg ptr
        let f ← reduce f
        match f.tag with
        | .lam => match ← getExpr f with
          | .lam b => reduce $ ← subst F.zero (← reduce a) b
          | x => throw s!"expected a lam pointer but got {x}"
        | _ =>
          let a ← reduce a
          addExprHash ⟨.app, hashPtrPair f a⟩ (.app f a)
    modifyGet fun stt => (ptr', { stt with cache := stt.cache.insert ptr ptr' })

end Vero.Hashing
