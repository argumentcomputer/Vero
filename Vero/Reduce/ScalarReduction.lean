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

def addExprHash (ptr : Ptr) (expr : ExprF) : ReduceM Ptr :=
  modifyGet fun stt => (ptr, { stt with store := stt.store.insert ptr expr })

partial def shift (dep inc : Nat) (ptr : Ptr) : ReduceM Ptr :=
  match ptr.tag with
  | .var =>
    let n := ptr.val.val
    if n >= dep then
      let n := .ofNat (n + inc)
      addExprHash ⟨.var, n⟩ (.var n)
    else return ptr
  | .lam => do match ← getExpr ptr with
    | .lam b =>
      let b ← shift (dep + 1) inc b
      addExprHash ⟨.lam, hashPtr b⟩ (.lam b)
    | x => throw s!"expected a lam pointer but got {x}"
  | .app => do match ← getExpr ptr with
    | .app f a =>
      let f ← shift dep inc f
      let a ← shift dep inc a
      addExprHash ⟨.app, hashPtrPair f a⟩ (.app f a)
    | x => throw s!"expected an app pointer but got {x}"

def subst (dep : Nat) (arg : Ptr) : Ptr → ReduceM Ptr := sorry

partial def reduce (ptr : Ptr) : ReduceM Ptr := do
  match (← get).cache.find? ptr with
  | some ptr => pure ptr
  | none =>
    let ptr' ← match ptr.tag with
      | .var => pure ptr
      | .lam => match ← getExpr ptr with
        | .lam b =>
          let b ← reduce b
          addExprHash ⟨.lam, hashPtr b⟩ (.lam b)
        | x => throw s!"expected a lam pointer but got {x}"
      | .app => match ← getExpr ptr with
        | .app f a =>
          let f ← reduce f
          match f.tag with
          | .lam =>
            match ← getExpr f with
            | .lam b => reduce $ ← subst 0 (← reduce a) b
            | x => throw s!"expected a lam pointer but got {x}"
          | _ =>
            let a ← reduce a
            addExprHash ⟨.app, hashPtrPair f a⟩ (.app f a)
        | x => throw s!"expected an app pointer but got {x}"
    modifyGet fun stt => (ptr', { stt with cache := stt.cache.insert ptr ptr' })

end Vero.Hashing
