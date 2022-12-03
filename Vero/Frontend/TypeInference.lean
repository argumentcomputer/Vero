import Vero.Frontend.AST

namespace Vero.Frontend

def unify2 : Typ → Typ → Except String Typ
  | .hole, typ
  | typ, .hole => pure typ
  | .pi i₁ o₁, .pi i₂ o₂ => return .pi (← unify2 i₁ i₂) (← unify2 o₁ o₂)
  | .pair x₁ y₁, .pair x₂ y₂ => return .pair (← unify2 x₁ x₂) (← unify2 y₁ y₂)
  | x, y => if x == y then pure x else throw s!"Can't unify2 {x} and {y}"

@[inline] def unify3 (a b c : Typ) : Except String Typ := do
  unify2 (← unify2 a b) c

@[inline] def unify4 (a b c d : Typ) : Except String Typ := do
  unify2 (← unify2 (← unify2 a b) c) d

abbrev Ctx := Std.RBMap String Typ compare

mutual

partial def AST.getVarTyp (s : String) (ctx : Ctx) : AST → Except String Typ
  | .var ⟨s', typ⟩ => if s == s' then pure typ else pure .hole
  | .lit .. => pure .hole
  | .unOp _ x => x.getVarTyp s ctx
  | .binOp _ x y => do unify2 (← x.getVarTyp s ctx) (← y.getVarTyp s ctx)
  | .lam ⟨s', _⟩ b => if s == s' then pure .hole else b.getVarTyp s ctx
  | .app (.var ⟨s', typ⟩) a =>
    if s == s' then do unify2 typ (.pi (← a.inferTyp ctx) .hole)
    else a.getVarTyp s ctx
  | .app f (.var ⟨s', typ⟩) =>
    if s == s' then do match ← f.inferTyp ctx with
      | .hole => return typ
      | .pi iTyp _ => unify2 iTyp typ
      | x => throw s!"Invalid type for app function: {x}"
    else f.getVarTyp s ctx
  | .app f a => do unify2 (← f.getVarTyp s ctx) (← a.getVarTyp s ctx)
  | .fork a b c => do unify3 (← a.getVarTyp s ctx) (← b.getVarTyp s ctx) (← c.getVarTyp s ctx)
  | .lt ⟨s', _⟩ v b => do
    unify2 (← v.getVarTyp s ctx) (if s == s' then .hole else ← b.getVarTyp s ctx)
  | .rc ⟨s', _⟩ v b =>
    if s == s' then pure .hole else do unify2 (← v.getVarTyp s ctx) (← b.getVarTyp s ctx)

partial def AST.fillHoles (typ : Typ) (ctx : Ctx) : AST → Except String AST
  | .var ⟨s, typ'⟩ => return .var ⟨s, ← unify2 typ typ'⟩
  | x@(.lit l) => do discard $ unify2 typ l.typ; return x
  | .unOp op x => match (op, typ) with
    | (.not, .bool) => return .unOp .not (← x.fillHoles .bool ctx)
    | _ => throw s!"Type mismatch for unary op {op.toString}: {typ}"
  | b@(.binOp op x y) => match op with
    | .add | .mul | .sub | .div => match typ with
      | .nat => return .binOp op (← x.fillHoles typ ctx) (← y.fillHoles typ ctx)
      | _ => throw s!"Type mismatch for binary op {op.toString}: {typ}"
    | .and | .or => match typ with
      | .bool => return .binOp op (← x.fillHoles .bool ctx) (← y.fillHoles .bool ctx)
      | _ => throw s!"Type mismatch for binary op {op.toString}: {typ}"
    | _ => return b
  | .fork a b c =>
    return .fork (← a.fillHoles .bool ctx) (← b.fillHoles typ ctx) (← c.fillHoles typ ctx)
  | .lam ⟨s, sTyp⟩ b => match typ with
    | .hole => do
      let sTyp ← unify2 sTyp (← b.getVarTyp s ctx)
      let ctx := ctx.insert s sTyp
      let b ← b.fillHoles (← b.inferTyp ctx) ctx
      let sTyp ← unify2 sTyp (← b.getVarTyp s ctx)
      return .lam ⟨s, sTyp⟩ b
    | .pi iTyp oTyp => do
      let sTyp ← unify3 sTyp iTyp (← b.getVarTyp s ctx)
      let ctx := ctx.insert s sTyp
      let oTyp ← unify2 oTyp (← b.inferTyp ctx)
      let b ← b.fillHoles oTyp ctx
      let sTyp ← unify2 sTyp (← b.getVarTyp s ctx)
      return .lam ⟨s, sTyp⟩ b
    | _ => throw s!"Invalid type for lam: {typ}"
  | .app f a => do match ← f.inferTyp ctx with
    | .hole =>
      let aTyp ← a.inferTyp ctx
      let f ← f.fillHoles (.pi aTyp typ) ctx
      return .app f a
    | .pi iTyp oTyp =>
      let oTyp ← unify2 oTyp typ
      let iTyp ← unify2 iTyp (← a.inferTyp ctx)
      let f ← f.fillHoles (.pi iTyp oTyp) ctx
      let a ← a.fillHoles iTyp ctx
      return .app f a
    | x => throw s!"Invalid type for app function: {x}"
  | .lt ⟨s, sTyp⟩ v b => do
    let sTyp ← unify3 sTyp (← v.inferTyp ctx) (← b.getVarTyp s ctx)
    let ctx := ctx.insert s sTyp
    let bTyp ← unify2 typ (← b.inferTyp ctx)
    let b ← b.fillHoles bTyp ctx
    let sTyp ← unify2 sTyp (← b.getVarTyp s ctx)
    let ctx := ctx.insert s sTyp
    let v ← v.fillHoles sTyp ctx
    return .lt ⟨s, sTyp⟩ v b
  | .rc ⟨s, sTyp⟩ v b => do
    let sTyp ← unify4 sTyp (← v.inferTyp ctx) (← v.getVarTyp s ctx) (← b.getVarTyp s ctx)
    let ctx := ctx.insert s sTyp
    let bTyp ← unify2 typ (← b.inferTyp ctx)
    let b ← b.fillHoles bTyp ctx
    let sTyp ← unify2 sTyp (← b.getVarTyp s ctx)
    let ctx := ctx.insert s sTyp
    let v ← v.fillHoles sTyp ctx
    return .rc ⟨s, sTyp⟩ v b

partial def AST.inferTyp (ctx : Ctx := default) : AST → Except String Typ
  | .lit l => return l.typ
  | .var ⟨s, sTyp⟩ => match ctx.find? s with
    | some typ => unify2 typ sTyp
    | none => pure sTyp
  | .unOp op x => match op with
    | .not => do unify2 .bool (← x.inferTyp ctx)
  | .binOp op x y => do
    let xyTyp ← unify2 (← x.inferTyp ctx) (← y.inferTyp ctx)
    match op with
    | .add | .mul | .sub | .div => unify2 .nat xyTyp
    | .lt  | .le  | .gt  | .ge  => do discard $ unify2 .nat xyTyp; return .bool
    | .eq  | .neq => return .bool
    | .and | .or  => unify2 .bool xyTyp
  | .fork x a b => do
    discard $ unify2 .bool (← x.inferTyp ctx)
    unify2 (← a.inferTyp ctx) (← b.inferTyp ctx)
  | .lam ⟨s, sTyp⟩ b => do
    let sTyp ← unify2 sTyp (← b.getVarTyp s ctx)
    let ctx := ctx.insert s sTyp
    let bTyp ← b.inferTyp ctx
    let b ← b.fillHoles bTyp ctx
    let sTyp ← unify2 sTyp (← b.getVarTyp s ctx)
    return .pi sTyp bTyp
  | .app f a => do
    let aTyp ← a.inferTyp ctx
    let (iTyp, oTyp) ← match ← f.inferTyp ctx with
      | .hole => pure (aTyp, .hole)
      | .pi iTyp oTyp => pure (← unify2 aTyp iTyp, oTyp)
      | x => throw s!"Invalid type for app function: {x}"
    let f' ← f.fillHoles (.pi iTyp oTyp) ctx
    let a' ← a.fillHoles iTyp ctx
    if f' != f || a' != a then inferTyp ctx (.app f' a')
    else pure oTyp
  | .lt ⟨s, sTyp⟩ v b => do
    let sTyp ← unify3 sTyp (← v.inferTyp ctx) (← b.getVarTyp s ctx)
    let ctx := ctx.insert s sTyp
    let v ← v.fillHoles sTyp ctx
    let sTyp ← unify2 sTyp (← v.inferTyp ctx)
    b.inferTyp $ ctx.insert s sTyp
  | .rc ⟨s, sTyp⟩ v b => do
    let sTyp ← unify4 sTyp (← v.inferTyp ctx) (← v.getVarTyp s ctx) (← b.getVarTyp s ctx)
    let ctx := ctx.insert s sTyp
    let v ← v.fillHoles sTyp ctx
    let sTyp ← unify3 sTyp (← v.inferTyp ctx) (← v.getVarTyp s ctx)
    b.inferTyp $ ctx.insert s sTyp

end

end Vero.Frontend
