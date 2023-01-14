import LSpec
import Vero.Frontend.Syn.DSL
import Vero.Pipelines.Reduce

open Vero

open Frontend.Syn.DSL Core Pipelines

def pairs : List (Frontend.Syn × Value) := [
  (⟦2 <= 3⟧, .bool true),
  (⟦let add x y := x + y; add 3 2⟧, .nat 5),
  (⟦let sub x y := x - y; sub 4 2⟧, .nat 2),
  (⟦let sub x y := x - y; sub 1 2⟧, .nat 0),
  (⟦(fun x => x & tt) ff⟧, .bool false),
  (⟦let f x y := x * y; let f3 := f 3; f3 2⟧, .nat 6),
  (⟦let div x y := x / y; div 6 3⟧, .nat 2),
  (⟦let gap x := if x > 5 then 10 else 1; gap 6⟧, .nat 10),
  (⟦rec sum x := if x > 0 then x + (sum (x - 1)) else 0; sum 4⟧, .nat 10)
]

open LSpec in
def main := lspecIO $
  pairs.foldl (init := .done) fun tSeq (syn, expectedVal) => tSeq ++
    withExceptOk s!"Input of {syn}" (Input.ofSyn syn) fun inp =>
      withExceptOk "Scalar reduction succeeds" inp.reduceScalar fun scalarVal =>
        let directVal := inp.reduceDirect
        test s!"Scalar reduced {scalarVal} matches expected {expectedVal}"
            (scalarVal == expectedVal) ++
          test s!"Scalar reduced {scalarVal} matches directly reduced {directVal}"
              (scalarVal == directVal)
