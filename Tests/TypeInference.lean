import LSpec
import Vero.Frontend.DSL
import Vero.Frontend.TypeInference

open Vero Frontend.DSL

def pairs : List $ Frontend.AST × (Option Typ) := [
  (⟦3⟧, some .nat),
  (⟦3 + 3⟧, some .nat),
  (⟦3 + x⟧, some .nat),
  (⟦x + 3⟧, some .nat),
  (⟦x + tt⟧, none),
  (⟦ff & tt⟧, some .bool),
  (⟦if 3 then tt else ff⟧, none),
  (⟦if a < 3 then tt else ff⟧, some .bool),
  (⟦(fun x => x) 1⟧, some ⟪nat⟫),
  (⟦let f x y := x + y; f 3 2⟧, some .nat),
  (⟦let f : _ -> nat := fun x => x; f 3⟧, some ⟪nat⟫),
  (⟦let f : nat -> nat -> nat := fun n y => n; f⟧, some ⟪nat -> nat -> nat⟫),
  (⟦fun (x : nat) y => x + y⟧, some ⟪nat -> nat -> nat⟫),
  (⟦let f : _ -> _ -> _ := fun x (y : nat) => x + y; f⟧, some ⟪nat -> nat -> nat⟫),
  (⟦let f x (y : nat) := x + y; f⟧, some ⟪nat -> nat -> nat⟫),
  (⟦let f (x : nat) y := x + y; f⟧, some ⟪nat -> nat -> nat⟫),
  (⟦(fun x (y : nat) => x) 1⟧, some ⟪nat -> nat⟫),
  (⟦fun x (f : nat -> nat) => f x⟧, some ⟪nat -> (nat -> nat) -> nat⟫),
  (⟦fun x (f : _ -> nat) => f (x : bool)⟧, some ⟪bool -> (bool -> nat) -> nat⟫),
  (⟦let f : nat -> _ := fun x => x; f 3⟧, some ⟪nat⟫),
  (⟦let f : nat -> nat -> _ := fun n y => y; f⟧,  some ⟪nat -> nat -> nat⟫),
  (⟦let f := fun x => x; f 3⟧, some ⟪nat⟫),
  (⟦let f : _ -> _ := fun x => x; f 3⟧, some ⟪nat⟫),
  (⟦let f : _ := fun x => x; f 3⟧, some ⟪nat⟫),
  (⟦rec f : _ -> nat := fun x => f 3; f⟧, some ⟪nat -> nat⟫)
]

open LSpec in
def main := lspecIO $
  pairs.foldl (init := .done) fun tSeq (ast, expecTyp) =>
    tSeq ++ match expecTyp with
      | some expecTyp =>
        withExceptOk "Type inference succeeds" ast.inferTyp fun gotTyp =>
          test s!"Expected {expecTyp} equals {gotTyp}" (expecTyp == gotTyp)
      | none => withExceptError "Type inference fails" ast.inferTyp fun _ => .done
