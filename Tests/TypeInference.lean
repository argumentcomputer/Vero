import LSpec
import Vero.Frontend.DSL

open Vero Frontend.DSL

def simpleBool := ⟦
  ff & tt
⟧

def simpleLam := ⟦
  f : nat -> int -> nat := n (y : int) => n : nat;
  f
⟧

def simpleLam' := ⟦
  f x (y : nat) := (x : nat) + y;
  f
⟧

def pairs : List $ Frontend.AST × (Option Typ) := [
  (simpleBool, some .bool),
  (simpleLam,  some $ .pi .nat (.pi .int .nat)),
  (simpleLam', some $ .pi .nat (.pi .nat .nat))
  -- TODO : add more tests
]

open LSpec in
def main := lspecIO $
  pairs.foldl (init := .done) fun tSeq (ast, expecTyp) =>
    tSeq ++ match expecTyp with
      | some expecTyp =>
        withExceptOk "Type inference succeeds" ast.inferTyp fun gotTyp =>
          test s!"Expected {expecTyp} equals {gotTyp}" (expecTyp == gotTyp)
      | none => withExceptError "Type inference fails" ast.inferTyp fun _ => .done
