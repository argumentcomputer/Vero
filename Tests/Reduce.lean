import LSpec
import Vero.Syntax.Core.Data
import Vero.Scalar.Encoding
import Vero.Scalar.Decoding
import Vero.Reduction.Direct
import Vero.Reduction.Scalar

open Vero

open Syntax.Core.DSL Syntax.Core.AST in
def cases : List $ Syntax.Core.AST × Reduction.ValType × Reduction.Value := [
  (⟦$(NAT 0)⟧, .nat, .nat 0),
  (⟦$NAT.SUCC $(NAT 5)⟧, .nat, .nat 6),
  (⟦$NAT.ADD $(NAT 1) $(NAT 2)⟧, .nat, .nat 3),
  (⟦$NAT.MUL $(NAT 2) $(NAT 3)⟧, .nat, .nat 6)
  -- TODO : add more tests
]

open LSpec in
def main := lspecIO $
  cases.foldl (init := .done) fun acc (ast, type, expec) =>
    acc ++ withExceptOk s!"{ast} converts to Expr" ast.toExpr fun expr =>
      let red := expr.reduce
      let got := red.ofType type
      test s!"Expected {expec} equals {got}" (expec == got) ++
        let (ptr, store) := expr.encode
        withExceptOk "Scalar reduction succeeds" (Scalar.reduce ptr store) fun (ptr, store) =>
          withExceptOk "Decoding succeeds" (Scalar.decode ptr store) fun red' =>
            test s!"Directly reduced {red} equals {red'}" (red == red')
