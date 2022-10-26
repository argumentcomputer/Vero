import Vero.Circuit.Compiler
import Vero.Syntax.DSL

open Vero.Syntax.DSL in
#eval ⟦
  a := x
  2 * a * 3
⟧.compile
-- @0 = x
-- @1 = x
-- @2 = 2
-- @3 = 3
-- @4 = 6
-- @5 = x
-- @6 = 6 * x
