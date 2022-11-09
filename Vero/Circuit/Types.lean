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

mutual

def Input.toString : Input → String
  | .const x => toString x
  | .inner g => g.toString
  | .outer s => s

def Gate.toString : Gate → String
  | .uno i => i.toString
  | .duo .add i₁ i₂ => s!"({i₁.toString} + {i₂.toString})"
  | .duo .mul i₁ i₂ => s!"({i₁.toString} + {i₂.toString})"

end

end Circuit

abbrev Circuit := Circuit.Gate

end Vero
