import Vero.Frontend.DSL

open Vero.Frontend.DSL in
#eval ⟦
  f x y :=
    z := 1;
    x + y + z;
  2 * (f @ 3, 5)
⟧
