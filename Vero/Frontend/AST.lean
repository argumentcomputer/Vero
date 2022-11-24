import Vero.Common.Typ
import YatimaStdLib.Ord
import Std.Data.RBMap

namespace Vero.Frontend

/-- Inductive enumerating unary operators -/
inductive UnOp
  | neg | not
  deriving Ord, Repr

/-- Inductive enumerating binary operators -/
inductive BinOp
  | add | mul | sub | div | eq | neq | lt | le | gt | ge | and | or
  deriving Ord, Repr

/-- Inductive enumerating the primitive types -/
inductive Lit
  | nat  : Nat  → Lit
  | int  : Int  → Lit
  | bool : Bool → Lit
  deriving Ord, Inhabited, Repr

structure Var where
  name : String
  type : Typ
  deriving Ord, Inhabited, Repr

inductive AST
  | lit : Lit → AST
  | var : Var → AST
  | unOp : UnOp → AST → AST
  | binOp : BinOp → AST → AST → AST
  | letIn : Var → AST → AST → AST
  | lam : Var → AST → AST
  | app : AST → AST → AST
  | fork : AST → AST → AST → AST
  deriving Ord, Inhabited, Repr

def unify2 : Typ → Typ → Except String Typ
  | .hole, typ
  | typ, .hole => pure typ
  | .pi i₁ o₁, .pi i₂ o₂ => return .pi (← unify2 i₁ i₂) (← unify2 o₁ o₂)
  | .pair x₁ y₁, .pair x₂ y₂ => return .pair (← unify2 x₁ x₂) (← unify2 y₁ y₂)
  | x, y => if x == y then pure x else throw s!"Can't unify {x} and {y}"

@[inline] def unify3 (a b c : Typ) : Except String Typ := do
  unify2 (← unify2 a b) c

@[inline] def unify4 (a b c d : Typ) : Except String Typ := do
  unify2 (← unify2 (← unify2 a b) c) d

def AST.getVarTyp (s : String) : AST → Except String Typ
  | .var ⟨s', typ⟩ => if s == s' then pure typ else pure .hole
  | .lit .. => pure .hole
  | .unOp _ x => x.getVarTyp s
  | .binOp _ x y => do unify2 (← x.getVarTyp s) (← y.getVarTyp s)
  | .letIn ⟨s', _⟩ v b =>
    if s == s' then pure .hole
    else do unify2 (← v.getVarTyp s) (← b.getVarTyp s)
  | .lam ⟨s', _⟩ b => if s == s' then pure .hole else b.getVarTyp s
  | .app f a => do unify2 (← f.getVarTyp s) (← a.getVarTyp s)
  | .fork a b c => do unify3 (← a.getVarTyp s) (← b.getVarTyp s) (← c.getVarTyp s)

def AST.inferTyp (ctx : Std.RBMap String Typ compare := default) :
    AST → Except String Typ
  | .lit l => match l with
    | .nat  _ => return .nat
    | .int  _ => return .int
    | .bool _ => return .bool
  | .var ⟨s, sTyp⟩ => unify2 sTyp (ctx.find? s)
  | .unOp .neg x => do match ← x.inferTyp ctx with
    | .hole | .int => return .int
    | x => throw s!"Expected type int but got {x}"
  | .unOp .not x => do match ← x.inferTyp ctx with
    | .hole | .bool => return .bool
    | x => throw s!"Expected type bool but got {x}"
  | .binOp .add x y
  | .binOp .mul x y
  | .binOp .sub x y
  | .binOp .div x y => do match (← x.inferTyp ctx, ← y.inferTyp ctx) with
    | (.hole, .nat)
    | (.nat, .hole)
    | (.nat, .nat) => return .nat
    | (.hole, .int)
    | (.int, .hole)
    | (.int, .int) => return .int
    | x => throw s!"Expected a pair of nats or ints but got {x}"
  | .binOp .lt x y
  | .binOp .le x y
  | .binOp .gt x y
  | .binOp .ge x y => do match (← x.inferTyp ctx, ← y.inferTyp ctx) with
    | (.hole, .nat)
    | (.nat, .hole)
    | (.nat, .nat)
    | (.hole, .int)
    | (.int, .hole)
    | (.int, .int) => return .bool
    | x => throw s!"Expected a pair of nats or ints but got {x}"
  | .binOp .eq x y
  | .binOp .neq x y => do match (← x.inferTyp ctx, ← y.inferTyp ctx) with
    | (_, .hole)
    | (.hole, _) => return .bool
    | (xTyp, yTyp) =>
      if xTyp == yTyp then return .bool
      else throw s!"Expected the same types but got {xTyp} and {yTyp}"
  | .binOp .and x y
  | .binOp .or x y => do match (← x.inferTyp ctx, ← y.inferTyp ctx) with
    | (.hole, .bool)
    | (.bool, .hole)
    | (.bool, .bool) => return .bool
    | x => throw s!"Expected a pair of bools but got {x}"
  | .letIn ⟨s, sTyp⟩ v b => do
    let sTyp ← unify4 sTyp (← v.inferTyp ctx) (← v.getVarTyp s) (← b.getVarTyp s)
    b.inferTyp $ ctx.insert s sTyp
  | .lam ⟨s, sTyp⟩ b => do
    let sTyp ← unify2 sTyp (← b.getVarTyp s)
    let bTyp ← b.inferTyp $ ctx.insert s sTyp
    return .pi sTyp bTyp
  | .app f a => do match (← f.inferTyp ctx, ← a.inferTyp ctx) with
    | (.hole, _)
    | (.pi _ .hole, _) => pure .hole
    | (.pi .hole o, _)
    | (.pi _ o, .hole) => pure o
    | pi@(.pi iTyp oTyp, aTyp) =>
      if iTyp == aTyp then return oTyp
      else throw s!"Type mismatch when applying {aTyp} to pi type {pi}"
    | (x, _) => throw s!"Expected a pi type but got {x}"
  | .fork x a b => do match ← x.inferTyp ctx with
    | .hole | .bool => unify2 (← a.inferTyp ctx) (← b.inferTyp ctx)
    | xTyp => throw s!"Expected bool type but got {xTyp}"

end Vero.Frontend
