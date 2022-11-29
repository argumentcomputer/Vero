import Vero.Frontend.AST

namespace Vero.Frontend

def unify : Typ → Typ → Except String Typ
  | .hole, typ
  | typ, .hole => pure typ
  | .pi i₁ o₁, .pi i₂ o₂ => return .pi (← unify i₁ i₂) (← unify o₁ o₂)
  | .pair x₁ y₁, .pair x₂ y₂ => return .pair (← unify x₁ x₂) (← unify y₁ y₂)
  | x, y => if x == y then pure x else throw s!"Can't unify {x} and {y}"

def unify' (a b c : Typ) : Except String Typ := do
  unify (← unify a b) c

def AST.getVarTyp (s : String) : AST → Except String Typ
  | .var ⟨s', typ⟩ => if s == s' then pure typ else pure .hole
  | .lit .. => pure .hole
  | .unOp _ x => x.getVarTyp s
  | .binOp _ x y => do unify (← x.getVarTyp s) (← y.getVarTyp s)
  | .lam ⟨s', _⟩ b => if s == s' then pure .hole else b.getVarTyp s
  | .app f a => do unify (← f.getVarTyp s) (← a.getVarTyp s)
  | .fork a b c => do unify' (← a.getVarTyp s) (← b.getVarTyp s) (← c.getVarTyp s)

abbrev Ctx := Std.RBMap String Typ compare

mutual

partial def AST.fillHoles (typ : Typ) (ctx : Ctx) : AST → Except String AST
  | .var ⟨s, typ'⟩ => return .var ⟨s, ← unify typ typ'⟩
  | x@(.lit l) => do discard $ unify typ l.typ; return x
  | .unOp op x => match (op, typ) with
    | (.neg, .int)  => return .unOp .neg (← x.fillHoles .int ctx)
    | (.not, .bool) => return .unOp .not (← x.fillHoles .bool ctx)
    | _ => throw s!"Type mismatch for unary op {op.toString}: {typ}"
  | b@(.binOp op x y) => match op with
    | .add | .mul | .sub | .div => match typ with
      | .nat | .int => return .binOp op (← x.fillHoles typ ctx) (← y.fillHoles typ ctx)
      | _ => throw s!"Type mismatch for binary op {op.toString}: {typ}"
    | .and | .or => match typ with
      | .bool => return .binOp op (← x.fillHoles .bool ctx) (← y.fillHoles .bool ctx)
      | _ => throw s!"Type mismatch for binary op {op.toString}: {typ}"
    | _ => return b
  | .fork a b c =>
    return .fork (← a.fillHoles .bool ctx) (← b.fillHoles typ ctx) (← c.fillHoles typ ctx)
  | .lam ⟨s, sTyp⟩ b => match typ with
    | .hole => do
      let sTyp ← unify sTyp (← b.getVarTyp s)
      let ctx := ctx.insert s sTyp
      let b ← b.fillHoles (← b.inferTyp ctx) ctx
      let sTyp ← unify sTyp (← b.getVarTyp s)
      return .lam ⟨s, sTyp⟩ b
    | .pi iTyp oTyp => do
      let sTyp ← unify' sTyp iTyp (← b.getVarTyp s)
      let ctx := ctx.insert s sTyp
      let oTyp ← unify oTyp (← b.inferTyp ctx)
      let b ← b.fillHoles oTyp ctx
      let sTyp ← unify sTyp (← b.getVarTyp s)
      return .lam ⟨s, sTyp⟩ b
    | _ => throw s!"Invalid type for lam: {typ}"
  | .app f a => do match ← f.inferTyp ctx with
    | .hole =>
      let aTyp ← a.inferTyp ctx
      let f ← f.fillHoles (.pi aTyp typ) ctx
      return .app f a
    | .pi iTyp oTyp =>
      let oTyp ← unify oTyp typ
      let iTyp ← unify iTyp (← a.inferTyp ctx)
      let f ← f.fillHoles (.pi iTyp oTyp) ctx
      let a ← a.fillHoles iTyp ctx
      return .app f a
    | x => throw s!"Invalid type for app function: {x}"

partial def AST.inferTyp (ctx : Ctx := default) : AST → Except String Typ
  | .lit l => return l.typ
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
  | .lam ⟨s, sTyp⟩ b => do
    let sTyp ← unify sTyp (← b.getVarTyp s)
    let ctx := ctx.insert s sTyp
    let bTyp ← b.inferTyp ctx
    let b ← b.fillHoles bTyp ctx
    let sTyp ← unify sTyp (← b.getVarTyp s)
    return .pi sTyp bTyp
  | .app f a => do
    let aTyp ← a.inferTyp ctx
    let (iTyp, oTyp) ← match ← f.inferTyp ctx with
      | .hole => pure (aTyp, .hole)
      | .pi iTyp oTyp => do
        pure (← unify aTyp iTyp, oTyp)
      | x => throw s!"Invalid type for app function: {x}"
    let f' ← f.fillHoles (.pi iTyp oTyp) ctx
    let a' ← a.fillHoles iTyp ctx
    if f' != f || a' != a then inferTyp ctx (.app f' a')
    else pure oTyp
  | .fork x a b => do
    discard $ unify .bool (← x.inferTyp ctx)
    unify (← a.inferTyp ctx) (← b.inferTyp ctx)

end

end Vero.Frontend
