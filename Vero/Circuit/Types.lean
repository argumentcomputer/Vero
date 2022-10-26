import Lean

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

def Input.findShortcut : Input → Input
  | inp@(.const _)
  | inp@(.outer _) => inp
  | inp@(.inner g) => match g with
    | .uno inp => inp.findShortcut
    | _ => inp

namespace Gate

def merge : Gate → Gate
  | add (.const c₁) (.const c₂) => uno $ .const (c₁ + c₂)
  | mul (.const c₁) (.const c₂) => uno $ .const (c₁ * c₂)
  | uno (.inner g) => uno (.inner g.merge)
  | add (.inner g₁) (.inner g₂) => add (.inner g₁.merge) (.inner g₂.merge)
  | add (.inner g) i => add (.inner g.merge) i
  | add i (.inner g) => add i (.inner g.merge)
  | mul (.inner g₁) (.inner g₂) => mul (.inner g₁.merge) (.inner g₂.merge)
  | mul (.inner g) i => mul (.inner g.merge) i
  | mul i (.inner g) => mul i (.inner g.merge)
  | g => g

def shortcut : Gate → Gate
  | .uno inp       => .uno inp.findShortcut
  | .add inp₁ inp₂ => .add inp₁.findShortcut inp₂.findShortcut
  | .mul inp₁ inp₂ => .mul inp₁.findShortcut inp₂.findShortcut

partial def optimize (g : Gate) : Gate :=
  let g' := g.merge.shortcut
  if g' != g then g'.optimize
  else g'

end Gate

end Circuit

end Vero
