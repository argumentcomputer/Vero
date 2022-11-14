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
  | lam : Option Typ → String → Option Typ → AST → AST
  | app : Option Typ → AST → AST → AST
  | fork : Option Typ → AST → AST → AST → AST
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
  | .lam _ s' _ b => if s == s' then none else b.getVarTyp s
  | .app _ f a => match (f.getVarTyp s, a.getVarTyp s) with
    | (some x, some y) => if x == y then some x else none
    | (some x, none) => some x
    | (none, some y) => some y
    | (none, none) => none
  | .fork _ a b c => match (a.getVarTyp s, b.getVarTyp s, c.getVarTyp s) with
    | (some a, some b, some c) => if a == b && b == c then some a else none
    | (some a, some b, none) => if a == b then some a else none
    | (some a, none, some c) => if a == c then some a else none
    | (none, some b, some c) => if b == c then some b else none
    | (none, none, some c) => some c
    | (none, some b, none) => some b
    | (some a, none, none) => some a
    | (none, none, none) => none

def AST.inferTyp (ctx : Std.RBMap String Typ compare := default) :
    AST → Except String (Option Typ)
  | .lit l => match l with
    | .nat  _ => return some .nat
    | .int  _ => return some .int
    | .bool _ => return some .bool
  | .var sTyp? s => match (sTyp?, ctx.find? s) with
    | (some sTyp, some ctxTyp) =>
      if sTyp == ctxTyp then return sTyp
      else throw s!"Type mismatch for {s}: {sTyp} ≠ {ctxTyp}"
    | (some typ, none)
    | (none, some typ) => return some typ
    | (none, none) => return none
  | .unOp .neg x => do match ← x.inferTyp ctx with
    | .some .int => return some .int
    | .some x => throw s!"Expected type int but got {x}"
    | none => return none
  | .unOp .not x => do match ← x.inferTyp ctx with
    | .some .bool => return some .bool
    | .some x => throw s!"Expected type bool but got {x}"
    | none => return none
  | .binOp .add x y
  | .binOp .mul x y
  | .binOp .sub x y
  | .binOp .div x y
  | .binOp .lt x y
  | .binOp .le x y
  | .binOp .gt x y
  | .binOp .ge x y => do match (← x.inferTyp ctx, ← y.inferTyp ctx) with
    | (some .nat, none)
    | (none, some .nat)
    | (some .nat, some .nat) => return some .nat
    | (some .int, none)
    | (none, some .int)
    | (some .int, some .int) => return some .int
    | (none, none) => return .none
    | x => throw s!"Expected a pair of nats or ints but got {x}"
  | .binOp .eq x y
  | .binOp .neq x y => do match (← x.inferTyp ctx, ← y.inferTyp ctx) with
    | (some .nat, none)
    | (none, some .nat)
    | (some .nat, some .nat) => return some .nat
    | (some .int, none)
    | (none, some .int)
    | (some .int, some .int) => return some .int
    | (some .bool, none)
    | (none, some .bool)
    | (some .bool, some .bool) => return some .bool
    | (none, none) => return .none
    | x => throw s!"Expected a pair of nats, ints or bools but got {x}"
  | .binOp .and x y
  | .binOp .or x y => do match (← x.inferTyp ctx, ← y.inferTyp ctx) with
    | (some .bool, none)
    | (none, some .bool)
    | (some .bool, some .bool) => return some .bool
    | (none, none) => return .none
    | x => throw s!"Expected a pair of bools but got {x}"
  | .letIn s sTyp? v b => do match (sTyp?, ← v.inferTyp ctx, b.getVarTyp s) with
    | (some sTyp, some vTyp, some sTyp') =>
      if sTyp == vTyp && vTyp == sTyp' then b.inferTyp $ ctx.insert s sTyp
      else throw s!"Type mismatch for {s}: {sTyp} / {vTyp} / {sTyp'}"
    | (some sTyp, some vTyp, none) =>
      if sTyp == vTyp then b.inferTyp $ ctx.insert s sTyp
      else throw s!"Type mismatch for {s}: {sTyp} / {vTyp}"
    | (some sTyp, none, some sTyp') =>
      if sTyp == sTyp' then b.inferTyp $ ctx.insert s sTyp
      else throw s!"Type mismatch for {s}: {sTyp} / {sTyp'}"
    | (none, some vTyp, some sTyp') =>
      if vTyp == sTyp' then b.inferTyp $ ctx.insert s vTyp
      else throw s!"Type mismatch for {s}: {vTyp} / {sTyp'}"
    | (some typ, none, none)
    | (none, some typ, none)
    | (none, none, some typ) => b.inferTyp $ ctx.insert s typ
    | (none, none, none) => b.inferTyp ctx
  | .lam typ? s sTyp? b => match (typ?, sTyp?, b.getVarTyp s) with
    | (some $ .pi inTyp outTyp, some sTyp, some sTyp') =>
      if inTyp == sTyp && sTyp == sTyp' then do
        match ← b.inferTyp $ ctx.insert s sTyp with
        | some bTyp =>
          if outTyp == bTyp then return some $ .pi inTyp outTyp
          else throw s!"Type mismatch for {s}: {outTyp} / {bTyp}"
        | none => return some $ .pi inTyp outTyp
      else throw s!"Type mismatch for {s}: {inTyp} / {sTyp} / {sTyp'}"
    | (some $ .pi inTyp outTyp, some sTyp, none)
    | (some $ .pi inTyp outTyp, none, some sTyp) =>
      if inTyp == sTyp then do
        match ← b.inferTyp $ ctx.insert s sTyp with
        | some bTyp =>
          if outTyp == bTyp then return some $ .pi inTyp outTyp
          else throw s!"Type mismatch for {s}: {outTyp} / {bTyp}"
        | none => return some $ .pi inTyp outTyp
      else throw s!"Type mismatch for {s}: {inTyp} / {sTyp}"
    | (none, some sTyp, some sTyp') =>
      if sTyp == sTyp' then do
        match ← b.inferTyp $ ctx.insert s sTyp with
        | some bTyp => return some $ .pi sTyp bTyp
        | none => return none
      else throw s!"Type mismatch for {s}: {sTyp} / {sTyp'}"
    | (none, some sTyp, none)
    | (none, none, some sTyp) => do match ← b.inferTyp $ ctx.insert s sTyp with
      | some bTyp => return some $ .pi sTyp bTyp
      | none => return none
    | (none, none, none) => return none
    | (some pi@(.pi ..), none, none) => return some pi
    | (some x, _, _) => throw s!"{x} is not a pi type"
  | .app typ? f a => do match (typ?, ← f.inferTyp ctx, ← a.inferTyp ctx) with
    | (some typ, some $ .pi inTyp outTyp, some aTyp) =>
      if inTyp == aTyp && outTyp == typ then return some typ
      else throw s!"Type mismatch: {inTyp} / {aTyp} or {outTyp} / {typ}"
    | (none, some $ .pi inTyp outTyp, some aTyp) =>
      if inTyp == aTyp then return some outTyp
      else throw s!"Type mismatch: {inTyp} / {aTyp}"
    | _ => return none
  | .fork typ? a b c => do
    match (typ?, ← a.inferTyp ctx, ← b.inferTyp ctx, ← c.inferTyp ctx) with
    | (some typ, some .bool, some typ', some typ'') =>
      if typ == typ' && typ' == typ'' then return typ
      else throw s!"Type mismatch for {typ} / {typ'} / {typ''}"
    | (none, some .bool, some typ', some typ'') =>
      if typ' == typ'' then return typ'
      else throw s!"Type mismatch for {typ'} / {typ''}"
    | (_, some x, _, _) => throw s!"Required bool type but found {x}"
    | _ => return none

end Vero.Frontend

open Vero.Frontend

#eval (AST.lam (some $ .pi .int .nat) "a" (none) (.lit (.nat 4))).inferTyp