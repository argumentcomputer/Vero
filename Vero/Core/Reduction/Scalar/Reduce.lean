import Vero.Core.Reduction.Scalar.Datatypes
import Vero.Core.Reduction.Scalar.Utils
import YatimaStdLib.Ord

namespace Vero.Core.Scalar

structure EvalState where
  store : StoreF
  evalCache  : Std.RBMap (Ptr × Ptr) Ptr compare
  applyCache : Std.RBMap (Ptr × Ptr) Ptr compare
  deriving Inhabited

abbrev ReduceM := ExceptT String $ StateM EvalState

def getExprF (ptr : Ptr) : ReduceM ExprF := do
  match (← get).store.find? ptr with
  | some e => pure e
  | none => throw s!"pointer not found in the store: {ptr}"

def getLamBody (ptr : Ptr) : ReduceM Ptr := do
  match ← getExprF ptr with
  | .lam b => pure b
  | x => throw s!"expected a lam expression but got {x}"

def getAppFncArg (ptr : Ptr) : ReduceM $ Ptr × Ptr := do
  match ← getExprF ptr with
  | .app f a => pure (f, a)
  | x => throw s!"expected an app expression but got {x}"

def getNormLamBodyEnv (ptr : Ptr) : ReduceM $ Ptr × Ptr := do
  match ← getExprF ptr with
  | .normLam b e => pure (b, e)
  | x => throw s!"expected a normLam expression but got {x}"

def getNormNeuHeadArgs (ptr : Ptr) : ReduceM $ F × Ptr := do
  match ← getExprF ptr with
  | .normNeu h a => pure (h, a)
  | x => throw s!"expected a normNeu expression but got {x}"

def getEnvHeadTail (ptr : Ptr) : ReduceM $ Ptr × Ptr := do
  match ← getExprF ptr with
  | .envCons h t => pure (h, t)
  | x => throw s!"expected an envCons expression but got {x}"

def findInEnvN (ptr : Ptr) (n : F) : ReduceM $ Ptr × F :=
  let rec aux (ptr : Ptr) (acc : F) (n : Nat) : ReduceM (Ptr × F) :=
    match ptr.tag with
    | .envNil => pure (⟨.envNil, .zero⟩, acc)
    | .envCons => match n with
      | 0 => return ((← getEnvHeadTail ptr).1, acc)
      | n + 1 => do aux (← getEnvHeadTail ptr).2 acc.succ n
    | _ => throw s!"expected a envNil or envCons pointer but got {ptr}"
  aux ptr .zero n.val

partial def unfoldEnv (ptr : Ptr) (acc : Array Ptr := #[]) : ReduceM $ Array Ptr :=
  match ptr.tag with
  | .envNil => pure acc
  | _ => do let (h, t) ← getEnvHeadTail ptr; unfoldEnv t (acc.push h)

def ReduceM.addExprF (ptr : Ptr) (exprF : ExprF) : ReduceM Ptr :=
  modifyGet fun stt => (ptr, { stt with store := stt.store.insert ptr exprF })

open ReduceM (addExprF)

mutual

partial def evalM (exprPtr envPtr : Ptr) : ReduceM Ptr := do
  match (← get).evalCache.find? (exprPtr, envPtr) with
  | some normPtr => pure normPtr
  | none =>
    let normPtr ← match exprPtr.tag with
      | .var =>
        let j := exprPtr.val
        let (ptr, len) ← findInEnvN envPtr j
        match ptr.tag with
        | .envNil =>
          let var := j - len
          let envPtr := ⟨.envNil, .zero⟩
          addExprF ⟨.normNeu, hashFPtr var envPtr⟩ (.normNeu var envPtr)
        | _ => pure ptr
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
      | .normLam =>
        let (bodPtr, envPtr) ← getNormLamBodyEnv fncPtr
        let envPtr ← addExprF ⟨.envCons, hashPtrPair argPtr envPtr⟩
          (.envCons argPtr envPtr)
        evalM bodPtr envPtr
      | .normNeu =>
        let (hdPtr, argsPtr) ← getNormNeuHeadArgs fncPtr
        let envPtr ← addExprF ⟨.envCons, hashPtrPair argPtr argsPtr⟩
          (.envCons argPtr argsPtr)
        addExprF ⟨.normNeu, hashFPtr hdPtr envPtr⟩ (.normNeu hdPtr envPtr)
      | _ => throw s!"invalid pointer for application function: {fncPtr}"
    modifyGet fun stt => (normPtr, { stt with
      applyCache := stt.applyCache.insert (fncPtr, argPtr) normPtr })

end

mutual

partial def quoteM (normPtr : Ptr) (shift : F) : ReduceM Ptr :=
  match normPtr.tag with
  | .normLam => do
    let (bodPtr, envPtr) ← getNormLamBodyEnv normPtr
    let bodPtr ← instM bodPtr envPtr .one shift
    addExprF ⟨.lam, hashPtr bodPtr⟩ (.lam bodPtr)
  | .normNeu => do
    let (hdPtr, argsPtr) ← getNormNeuHeadArgs normPtr
    let argsPtrs ← unfoldEnv argsPtr
    let varIdx := hdPtr + shift
    let varPtr ← addExprF ⟨.var, varIdx⟩ (.var varIdx)
    argsPtrs.foldrM (init := varPtr) fun a f => do
      let a ← quoteM a shift
      addExprF ⟨.app, hashPtrPair f a⟩ (.app f a)
  | _ => throw s!"expected a normLam or normNeu pointer but got {normPtr}"

partial def instM (exprPtr envPtr : Ptr) (dep shift : F) : ReduceM Ptr :=
  match exprPtr.tag with
  | .app => do
    let (fncPtr, argPtr) ← getAppFncArg exprPtr
    let fncPtr ← instM fncPtr envPtr dep shift
    let argPtr ← instM argPtr envPtr dep shift
    addExprF ⟨.app, hashPtrPair fncPtr argPtr⟩ (.app fncPtr argPtr)
  | .lam => do
    let bodyPtr ← getLamBody exprPtr
    let lamPtr ← instM bodyPtr envPtr dep.succ shift
    addExprF ⟨.lam, hashPtr lamPtr⟩ (.lam lamPtr)
  | .var =>
    let j := exprPtr.val
    if j < dep then pure exprPtr else do
    let j := j - dep
    let (ptr, len) ← findInEnvN envPtr j
    match ptr.tag with
    | .envNil => let j := j - len; addExprF ⟨.var, j⟩ (.var j)
    | _ => quoteM ptr (shift + dep)
  | _ => throw s!"invalid pointer for instantiation: {exprPtr}"

end

def reduceM (ptr : Ptr) : ReduceM Ptr := do
  let env ← addExprF ⟨.envNil, .zero⟩ .envNil
  quoteM (← evalM ptr env) .zero

def reduce (ptr : Ptr) (store : StoreF) : Except String (Ptr × StoreF) :=
  match StateT.run (reduceM ptr) ⟨store, default, default⟩ with
  | (.error err, _) => .error err
  | (.ok ptr, ⟨store, _, _⟩) => .ok (ptr, store)

end Vero.Core.Scalar
