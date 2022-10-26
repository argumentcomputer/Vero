import Lean

namespace Vero

namespace Circuit

@[inline] def fmtIdx (i : Nat) : String :=
  s!"@{i}"

inductive Input
  | const : Nat → Input
  | inner : Nat → Input
  | outer : String → Input
  deriving Inhabited

def Input.toString : Input → String
  | .const n => ToString.toString n
  | .inner i => fmtIdx i
  | .outer s => s

instance : ToString Input := ⟨Input.toString⟩

inductive Gate
  | uno : Input → Gate
  | add : Input → Input → Gate
  | mul : Input → Input → Gate
  deriving Inhabited

def Gate.toString : Gate → String
  | .uno inp => inp.toString
  | .add inp₁ inp₂ => s!"{inp₁} + {inp₂}"
  | .mul inp₁ inp₂ => s!"{inp₁} * {inp₂}"

instance : ToString Gate := ⟨Gate.toString⟩

end Circuit

abbrev Circuit := Array Circuit.Gate

namespace Circuit

def toString (c : Circuit) : String :=
  "\n".intercalate $ c.data.enum.map fun (i, g) => s!"{fmtIdx i} = {g}"

instance : ToString Circuit := ⟨toString⟩

partial def findShortcut (c : Circuit) : Input → Input
  | inp@(.const _)
  | inp@(.outer _) => inp
  | inp@(.inner i) => match c[i]! with
    | .uno inp => findShortcut c inp
    | _ => inp

def shortcutAt (c : Circuit) (i : Nat) : Circuit :=
  c.set! i $ match c[i]! with
    | .uno inp => .uno (c.findShortcut inp)
    | .add inp₁ inp₂ => .add (c.findShortcut inp₁) (c.findShortcut inp₂)
    | .mul inp₁ inp₂ => .mul (c.findShortcut inp₁) (c.findShortcut inp₂)

def optimize (c : Circuit) : Circuit := Id.run do
  let mut c := c
  let mut i := c.size - 1
  while true do
    c := c.shortcutAt i
    i := i - 1
    if i == 0 then break
  return c

end Circuit

end Vero
