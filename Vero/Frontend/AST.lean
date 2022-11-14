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

inductive Typ
  | nat
  | int
  | bool
  | pair : Typ → Typ → Typ
  | pi   : Typ → Typ → Typ
  deriving Ord, BEq, Inhabited, Repr

def Typ.toString : Typ → String
  | .nat  => "nat"
  | .int  => "int"
  | .bool => "bool"
  | .pair t₁ t₂ => s!"({t₁.toString} . {t₂.toString})"
  | .pi   t₁ t₂ => s!"({t₁.toString} -> {t₂.toString})"

instance : ToString Typ := ⟨Typ.toString⟩

inductive AST
  | lit : Lit → AST
  | var : Option Typ → String → AST
  | unOp : UnOp → AST → AST
  | binOp : BinOp → AST → AST → AST
  | letIn : String → Option Typ → AST → AST → AST
  | lam : String → Option Typ → AST → AST
  | app : AST → AST → AST
  | fork : AST → AST → AST → AST
  deriving Ord, Inhabited, Repr

def AST.getVarTyp (s : String) : AST → Option Typ
  | .var typ? s' => if s == s' then typ? else none
  | .lit .. => none
  | .unOp _ x => x.getVarTyp s
  | .binOp _ x y => match (x.getVarTyp s, y.getVarTyp s) with
    | (some x, some y) => if x == y then some x else none
    | (some x, none) => some x
    | (none, some y) => some y
    | (none, none) => none
  | .letIn s' _ v b =>
    if s == s' then none
    else match (v.getVarTyp s, b.getVarTyp s) with
      | (some v, some b) => if v == b then some v else none
      | (some v, none) => some v
      | (none, some b) => some b
      | (none, none) => none
  | .lam s' _ b => if s == s' then none else b.getVarTyp s
  | .app f a => match (f.getVarTyp s, a.getVarTyp s) with
    | (some x, some y) => if x == y then some x else none
    | (some x, none) => some x
    | (none, some y) => some y
    | (none, none) => none
  | .fork a b c => match (a.getVarTyp s, b.getVarTyp s, c.getVarTyp s) with
    | (some a, some b, some c) => if a == b && b == c then some a else none
    | (some a, some b, none) => if a == b then some a else none
    | (some a, none, some c) => if a == c then some a else none
    | (none, some b, some c) => if b == c then some b else none
    | (none, none, some c) => some c
    | (none, some b, none) => some b
    | (some a, none, none) => some a
    | (none, none, none) => none

def AST.inferTyp (ctx : Std.RBMap String Typ compare := default) :
    AST → Except String Typ
  | .lit l => match l with
    | .nat  _ => return .nat
    | .int  _ => return .int
    | .bool _ => return .bool
  | .var sTyp? s => match (sTyp?, ctx.find? s) with
    | (some sTyp, some ctxTyp) =>
      if sTyp == ctxTyp then return sTyp
      else throw s!"Type mismatch for {s}: {sTyp} ≠ {ctxTyp}"
    | (some typ, none)
    | (none, some typ) => return typ
    | (none, none) => throw s!"Unable to infer the type of {s}"
  | .unOp .neg x => do match ← x.inferTyp ctx with
    | .int => return .int
    | x => throw s!"Expected type int but got {x}"
  | .unOp .not x => do match ← x.inferTyp ctx with
    | .bool => return .bool
    | x => throw s!"Expected type bool but got {x}"
  | .binOp .add x y
  | .binOp .mul x y
  | .binOp .sub x y
  | .binOp .div x y
  | .binOp .lt x y
  | .binOp .le x y
  | .binOp .gt x y
  | .binOp .ge x y => do match (← x.inferTyp ctx, ← y.inferTyp ctx) with
    | (.nat, .nat) => return .nat
    | (.int, .int) => return .int
    | x => throw s!"Expected a pair of nats or ints but got {x}"
  | .binOp .eq x y
  | .binOp .neq x y => do
    let xTyp ← x.inferTyp ctx
    let yTyp ← y.inferTyp ctx
    if xTyp == yTyp then return xTyp
    else throw s!"Expected the same types but got {xTyp} and {yTyp}"
  | .binOp .and x y
  | .binOp .or x y => do match (← x.inferTyp ctx, ← y.inferTyp ctx) with
    | (.bool, .bool) => return .bool
    | x => throw s!"Expected a pair of bools but got {x}"
  | .letIn s sTyp? v b => do
    let vTyp ← v.inferTyp ctx
    match (sTyp?, b.getVarTyp s) with
    | (some sTyp, some sTyp') =>
      if sTyp == vTyp && vTyp == sTyp' then b.inferTyp $ ctx.insert s sTyp
      else throw s!"Type mismatch for {s}: {sTyp} / {vTyp} / {sTyp'}"
    | (some sTyp, none)
    | (none, some sTyp) =>
      if vTyp == sTyp then b.inferTyp $ ctx.insert s vTyp
      else throw s!"Type mismatch for {s}: {vTyp} / {sTyp}"
    | (none, none) => b.inferTyp ctx
  | .lam s sTyp? b => do
    let (sTyp, bTyp) ← match (sTyp?, b.getVarTyp s) with
      | (some sTyp, some sTyp') =>
        if sTyp == sTyp' then
          pure (sTyp, ← b.inferTyp $ ctx.insert s sTyp)
        else throw s!"Type mismatch for {s}: {sTyp} / {sTyp'}"
      | (some sTyp, none)
      | (none, some sTyp) => pure (sTyp, ← b.inferTyp $ ctx.insert s sTyp)
      | (none, none) => throw "Unable to infer the type of lam"
    return .pi sTyp bTyp
  | .app f a => do match (← f.inferTyp ctx, ← a.inferTyp ctx) with
    | (pi@(.pi inTyp outTyp), aTyp) =>
      if inTyp == aTyp then return outTyp
      else throw s!"Type mismatch when applying {aTyp} to pi type {pi}"
    | (x, _) => throw s!"Expected a pi type but got {x}"
  | .fork a b c => do
    match (← a.inferTyp ctx, ← b.inferTyp ctx, ← c.inferTyp ctx) with
    | (.bool, typ', typ'') =>
      if typ' == typ'' then return typ'
      else throw s!"Type mismatch for {typ'} / {typ''}"
    | (x, _, _) => throw s!"Required bool type but found {x}"

end Vero.Frontend
