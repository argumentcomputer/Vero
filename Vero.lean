import Vero.Circuit.Transformer
import Vero.Syntax.DSL

open Vero.Syntax.DSL in
#eval ⟦
  f x y := x + y;
  2 * (f 3 5)
⟧.toCircuit
