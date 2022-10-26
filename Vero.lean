import Vero.Circuit.Compiler
import Vero.Syntax.DSL

open Vero.Syntax.DSL in
#eval ⟦
  a := 4
  a * 3 * 5
⟧.compile
-- ok: @0 = 4
-- @1 = @0
-- @2 = @1
-- @3 = 3
-- @4 = 5
-- @5 = @3 * @4
-- @6 = @2 * @5
