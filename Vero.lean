import Vero.Circuit.Compiler
import Vero.Syntax.DSL

open Vero.Syntax.DSL in
#eval ⟦
  a := x
  a * 3 * 5 * 2
⟧.compile
-- @0 = x
-- @1 = x
-- @2 = x
-- @3 = 3
-- @4 = 5
-- @5 = 2
-- @6 = 10
-- @7 = 30
-- @8 = x * 30
