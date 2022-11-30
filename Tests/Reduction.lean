import LSpec
import Vero.Frontend.DSL
import Vero.Reduction.TypedExpr

open Vero

open Frontend.DSL in
def pairs : List (Frontend.AST × Value) := [
  (⟦let add x y := x + y; add 3 2⟧, .nat 5),
  (⟦(fun x => x & tt) ff⟧, .bool false),
  -- (⟦let div x y := x / y; div 6 3⟧, .nat 2),                -- TODO : div
  -- (⟦let gap x := if x > 5 then 10 else 1; gap 6⟧, .nat 10), -- FIX  : looping
  (⟦let f x y := x * y; let f3 := f 3; f3 2⟧, .nat 6)
]

open LSpec Reduction in
def main := lspecIO $
  pairs.foldl (init := .done) fun tSeq (ast, expectedVal) => tSeq ++
    withExceptOk s!"TypedExpr of {ast}" (TypedExpr.ofAST ast) fun te =>
      withExceptOk "Scalar reduction succeeds" te.scalarReduce fun scalarVal =>
        test "Scalar reduction matches expectation" (scalarVal == expectedVal) ++
          test "Scalar reduction matches direct reduction" (scalarVal == te.directReduce)
