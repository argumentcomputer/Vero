import LSpec
import Vero.Frontend.DSL

open Vero Frontend.DSL

def pairs : List $ Frontend.AST × (Option Typ) := [
  (⟦3⟧, some .nat),
  (⟦3 + +3⟧, none),
  (⟦3 + x⟧, some .nat),
  (⟦x + +3⟧, some .int),
  (⟦x + tt⟧, none),
  (⟦ff & tt⟧, some .bool),
  (⟦(fun x => x) 1⟧, some ⟪nat⟫),
  (⟦let f : _ -> nat := fun x => x; f 3⟧, some ⟪nat⟫),
  (⟦let f : nat -> int -> nat := fun n y => n; f⟧,  some ⟪nat -> int -> nat⟫),
  (⟦fun (x : nat) y => x + y⟧, some ⟪nat -> nat -> nat⟫),
  (⟦let f : _ -> _ -> _ := fun x (y : nat) => x + y; f⟧, some ⟪nat -> nat -> nat⟫),
  (⟦let f x (y : nat) := x + y; f⟧, some ⟪nat -> nat -> nat⟫),
  (⟦let f (x : nat) y := x + y; f⟧, some ⟪nat -> nat -> nat⟫),
  (⟦(fun x (y : int) => x) 1⟧, some ⟪int -> nat⟫),
  (⟦fun x (f : nat -> int) => f x⟧, some ⟪nat -> (nat -> int) -> int⟫),
  (⟦fun x (f : _ -> int) => f (x : bool)⟧, some ⟪bool -> (bool -> int) -> int⟫),
  (⟦let f : nat -> _ := fun x => x; f 3⟧, some ⟪nat⟫),
  (⟦let f : nat -> int -> _ := fun n y => y; f⟧,  some ⟪nat -> int -> int⟫)
]

-- TODO : fix
-- def pairs : List $ Frontend.AST × (Option Typ) := [
--   (⟦let f := fun x => x; f 3⟧, some ⟪nat⟫),
--   (⟦let f : _ -> _ := fun x => x; f 3⟧, some ⟪nat⟫),
--   (⟦let f : _ := fun x => x; f 3⟧, some ⟪nat⟫)
-- ]

open LSpec in
def main := lspecIO $
  pairs.foldl (init := .done) fun tSeq (ast, expecTyp) =>
    tSeq ++ match expecTyp with
      | some expecTyp =>
        withExceptOk "Type inference succeeds" ast.inferTyp fun gotTyp =>
          test s!"Expected {expecTyp} equals {gotTyp}" (expecTyp == gotTyp)
      | none => withExceptError "Type inference fails" ast.inferTyp fun _ => .done
