import Vero.Frontend.DSL
import Vero.Reduction.TypedExpr

open Vero Frontend.DSL Reduction

def exprs : List Frontend.AST := [
    ⟦let add x y := x + y; add 4000 4000⟧,
    ⟦let sub x y := x - y; sub 4000 2000⟧,
    ⟦let mul x y := x * y; mul 100   100⟧,
    ⟦let div x y := x / y; div 2400  120⟧
]

def benchmark (action : Unit → a) : IO (Nat × a) := do
  let NOW ← IO.monoMsNow
  let res := action ()
  let THEN ← IO.monoMsNow
  pure (THEN-NOW, res)

def main : IO UInt32 := do
  let mut ret : UInt32 := 0
  for ast in exprs do
    match TypedExpr.ofAST ast with
    | .ok te => do
      let (time, val) ← benchmark (fun _ => te.expr.reduce)
      IO.println s!"Expression reduced to {val.toValueOf te.typ} in {(Float.ofNat time) / 1000}s,"

      let (timeEval, norm) ← benchmark (fun _ => te.expr.eval [])
      let (timeQuote, val) ← benchmark (fun _ => Expr.quote norm 0)
      IO.println s!"evaluated strictly to {val.toValueOf te.typ} in {(Float.ofNat timeEval) / 1000}s,"
      IO.println s!"and was quoted in {(Float.ofNat timeQuote) / 1000}s\n"
    | .error _ => IO.println "Cannot infer type"; ret := 1
  pure ret
