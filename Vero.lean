import Vero.Circuit.Transformer
import Vero.Syntax.DSL

open Vero.Syntax.DSL in
#eval ⟦
  f x y :=
    z := 1;
    x + y + z;
  2 * (f 3 5)
⟧.toCircuit
