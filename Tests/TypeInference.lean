import LSpec
import Vero.Frontend.DSL

open Vero Frontend.DSL

def simpleBool := ⟦
  ff & tt
⟧

def pairs : List $ Frontend.AST × (Option Frontend.Typ) := [
  (simpleBool, some .bool)
]

open LSpec in
def main := lspecIO $
  pairs.foldl (init := .done) fun tSeq (ast, expecTyp) =>
    tSeq ++ match expecTyp with
      | some expecTyp =>
        withExceptOk "Type inference succeeds" ast.inferTyp fun gotTyp =>
          test s!"Expected {expecTyp} equals {gotTyp}" (expecTyp == gotTyp)
      | none => withExceptError "Type inference fails" ast.inferTyp fun _ => .done
