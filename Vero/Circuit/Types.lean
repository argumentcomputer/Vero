namespace Vero

namespace Circuit

mutual

inductive Input
  | const : Nat → Input
  | inner : Gate → Input
  | outer : String → Input
  deriving Inhabited, BEq, Repr, Ord

inductive Op
  | add | mul

inductive Gate
  | uno : Input → Gate
  | duo : Op → Input → Input → Gate
  deriving Inhabited, BEq, Repr

end

end Circuit

abbrev Circuit := Circuit.Gate

end Vero
