import LSpec
import Vero.Frontend.DSL
import Vero.Reduction.TypedExpr

open Vero

open Frontend.DSL in
def pairs : List (Frontend.AST × Value) := [
  -- (⟦2 <= 3⟧, .bool true),
  (⟦let add x y := x + y; add 1 1⟧, .nat 2)
  -- (⟦let add x y := x + y; add 3 2⟧, .nat 5),
  -- (⟦let sub x y := x - y; sub 4 2⟧, .nat 2),
  -- (⟦let sub x y := x - y; sub 1 2⟧, .nat 0),
  -- (⟦(fun x => x & tt) ff⟧, .bool false),
  -- (⟦let f x y := x * y; let f3 := f 3; f3 2⟧, .nat 6),
  -- (⟦let div x y := x / y; div 6 3⟧, .nat 2),
  -- (⟦let gap x := if x > 5 then 10 else 1; gap 6⟧, .nat 10),
  -- (⟦rec sum x := if x > 0 then x + (sum (x - 1)) else 0; sum 2⟧, .nat 3)
]

open LSpec Reduction in
def main := lspecIO $
  pairs.foldl (init := .done) fun tSeq (ast, expectedVal) => tSeq ++
    withExceptOk s!"TypedExpr of {ast}" (TypedExpr.ofAST ast) fun te =>
      withExceptOk "Scalar reduction succeeds" te.scalarReduce fun scalarVal =>
        let directVal := te.directReduce
        test s!"Scalar reduced {scalarVal} matches expected {expectedVal}"
            (scalarVal == expectedVal) ++
          test s!"Scalar reduced {scalarVal} matches directly reduced {directVal}"
              (scalarVal == directVal)
