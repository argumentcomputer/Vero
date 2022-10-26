namespace Vero

namespace Circuit

mutual

inductive Input
  | const : Nat → Input
  | inner : Gate → Input
  | outer : String → Input
  deriving Inhabited, BEq, Repr

inductive Gate
  | uno : Input → Gate
  | add : Input → Input → Gate
  | mul : Input → Input → Gate
  deriving Inhabited, BEq, Repr

end

end Circuit

abbrev Circuit := Circuit.Gate

end Vero
