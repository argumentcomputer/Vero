import Vero.Circuit.Compiler
import Vero.Syntax.DSL

open Vero.Syntax.DSL in
#eval ⟦
  a := x
  a * 3 * 5
⟧.compile
-- @0 = x
-- @1 = @0
-- @2 = @1
-- @3 = 3
-- @4 = 5
-- @5 = @3 * @4
-- @6 = @2 * @5
