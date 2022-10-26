import Vero.Circuit.Transformer
import Vero.Syntax.DSL

open Vero.Syntax.DSL in
#eval ⟦
  a := x
  2 * a * 3
⟧.toCircuit
