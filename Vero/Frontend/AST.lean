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

def unify : Typ → Typ → Except String Typ
  | .hole, typ
  | typ, .hole => pure typ
  | .pi i₁ o₁, .pi i₂ o₂ => return .pi (← unify i₁ i₂) (← unify o₁ o₂)
  | .pair x₁ y₁, .pair x₂ y₂ => return .pair (← unify x₁ x₂) (← unify y₁ y₂)
  | x, y => if x == y then pure x else throw s!"Can't unify {x} and {y}"

def unify' (t : Typ) : List Typ → Except String Typ
  | [] => pure t
  | a :: as => do unify' (← unify t a) as

def AST.getVarTyp (s : String) : AST → Except String Typ
  | .var ⟨s', typ⟩ => if s == s' then pure typ else pure .hole
  | .lit .. => pure .hole
  | .unOp _ x => x.getVarTyp s
  | .binOp _ x y => do unify (← x.getVarTyp s) (← y.getVarTyp s)
  | .letIn ⟨s', _⟩ v b =>
    if s == s' then pure .hole
    else do unify (← v.getVarTyp s) (← b.getVarTyp s)
  | .lam ⟨s', _⟩ b => if s == s' then pure .hole else b.getVarTyp s
  | .app f a => do unify (← f.getVarTyp s) (← a.getVarTyp s)
  | .fork a b c => do unify' (← a.getVarTyp s) [(← b.getVarTyp s), (← c.getVarTyp s)]

abbrev Ctx := Std.RBMap String Typ compare

mutual

def AST.fillHoles (ctx : Ctx) : AST → Typ → Except String AST
  -- | _ => sorry
  | x, .hole => pure x
  | x, typ => match x with
    | .var ⟨s, typ'⟩ => return .var ⟨s, ← unify typ typ'⟩
    | x@(.lit l) => match (l, typ) with
      | (.nat _, .nat)
      | (.int _, .int)
      | (.bool _, .bool) => return x
      | _ => throw ""
    | .unOp op x => match (op, typ) with
      | (.neg, .int)  => return .unOp .neg (← x.fillHoles ctx .int)
      | (.not, .bool) => return .unOp .not (← x.fillHoles ctx .bool)
      | _ => throw ""
    | b@(.binOp op x y) => do
      let xyTyp ← unify (← x.inferTyp ctx) (← y.inferTyp ctx)
      match op with
      | .add | .mul | .sub | .div | .and | .or => do
        let xyTyp ← unify typ xyTyp
        return .binOp op (← x.fillHoles ctx xyTyp) (← y.fillHoles ctx xyTyp)
      | .lt | .le | .gt | .ge | .eq | .neq => do
        discard $ unify typ .bool
        return .binOp op (← x.fillHoles ctx xyTyp) (← y.fillHoles ctx xyTyp)
    | .fork a b c =>
      return .fork (← a.fillHoles ctx .bool) (← b.fillHoles ctx typ) (← c.fillHoles ctx typ)
    | .letIn ⟨s, sTyp⟩ v b => do
      let sTyp ← unify' sTyp [(← v.inferTyp ctx), (← v.getVarTyp s), (← b.getVarTyp s), typ]
      let ctx := ctx.insert s sTyp
      let b ← b.fillHoles ctx sTyp
      let v ← v.fillHoles ctx sTyp
      return .letIn ⟨s, sTyp⟩ v b
    | .lam ⟨s, sTyp⟩ b => match typ with
      | .pi iTyp oTyp => do
        let sTyp ← unify' sTyp [iTyp, (← b.getVarTyp s)]
        let ctx := ctx.insert s sTyp
        let bTyp ← unify oTyp (← b.inferTyp ctx)
        let b ← b.fillHoles ctx bTyp
        return .lam ⟨s, sTyp⟩ b
      | _ => throw ""
    | x@(.app f a) => do match (← f.inferTyp ctx, ← a.inferTyp ctx) with
      | (.hole, _) => return x
      | (.pi iTyp oTyp, aTyp) =>
        let oTyp ← unify oTyp typ
        let iTyp ← unify iTyp aTyp
        let a ← a.fillHoles ctx iTyp
        let f ← f.fillHoles ctx (.pi iTyp oTyp)
        return .app f a
      | _ => throw ""

def AST.inferTyp (ctx : Ctx := default) : AST → Except String Typ
  -- | _ => sorry
  | .lit l => match l with
    | .nat  _ => return .nat
    | .int  _ => return .int
    | .bool _ => return .bool
  | .var ⟨s, sTyp⟩ => unify sTyp (ctx.find? s)
  | .unOp op x => match op with
    | .neg => do unify .int  (← x.inferTyp ctx)
    | .not => do unify .bool (← x.inferTyp ctx)
  | .binOp op x y => do
    let xyTyp ← unify (← x.inferTyp ctx) (← y.inferTyp ctx)
    match op with
    | .add | .mul | .sub | .div => match xyTyp with
      | .nat => return .nat
      | .int => return .int
      | x => throw s!"Expected nat or int but got {x}"
    | .lt | .le | .gt | .ge => match xyTyp with
      | .nat | .int => return .bool
      | x => throw s!"Expected nat or int but got {x}"
    | .eq | .neq => return .bool
    | .and | .or => unify .bool xyTyp
  | .letIn ⟨s, sTyp⟩ v b => do
    let sTyp ← unify' sTyp [(← v.inferTyp ctx), (← v.getVarTyp s), (← b.getVarTyp s)]
    b.inferTyp $ ctx.insert s sTyp
  | .lam ⟨s, sTyp⟩ b => do match ← unify sTyp (← b.getVarTyp s) with
    | .hole =>
      let bTyp ← b.inferTyp ctx
      let b ← b.fillHoles ctx bTyp
      let sTyp ← b.getVarTyp s
      return .pi sTyp bTyp
    | sTyp =>
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
    | .hole | .bool => unify (← a.inferTyp ctx) (← b.inferTyp ctx)
    | xTyp => throw s!"Expected bool type but got {xTyp}"

end

end Vero.Frontend
