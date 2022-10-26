import Lean

namespace Vero

namespace Circuit

@[inline] def fmtIdx (i : Nat) : String :=
  s!"@{i}"

inductive Input
  | const : Nat → Input
  | inner : Nat → Input
  | outer : String → Input
  deriving Inhabited, BEq

def Input.toString : Input → String
  | .const n => ToString.toString n
  | .inner i => fmtIdx i
  | .outer s => s

instance : ToString Input := ⟨Input.toString⟩

inductive Gate
  | uno : Input → Gate
  | add : Input → Input → Gate
  | mul : Input → Input → Gate
  deriving Inhabited, BEq

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

def merge (c : Circuit) : Circuit :=
  c.map fun g => match g with
    | .add (.const c₁) (.const c₂) => .uno $ .const (c₁ + c₂)
    | .mul (.const c₁) (.const c₂) => .uno $ .const (c₁ * c₂)
    | g => g

partial def findShortcut (c : Circuit) : Input → Input
  | inp@(.const _)
  | inp@(.outer _) => inp
  | inp@(.inner i) => match c[i]! with
    | .uno inp => findShortcut c inp
    | _ => inp

def shortcut (c : Circuit) : Circuit := Id.run do
  let mut c := c
  let mut i := c.size - 1
  while i > 0 do
    c := c.set! i $ match c[i]! with
      | .uno inp => .uno (c.findShortcut inp)
      | .add inp₁ inp₂ => .add (c.findShortcut inp₁) (c.findShortcut inp₂)
      | .mul inp₁ inp₂ => .mul (c.findShortcut inp₁) (c.findShortcut inp₂)
    i := i - 1
  return c

def prune (c : Circuit) : Circuit := Id.run do
  let mut gs : List Gate := []
  ⟨gs⟩

def optimize (c : Circuit) : Circuit := Id.run do
  let mut c  := c
  let mut c' := c.merge.shortcut--.prune
  while c' != c do
    c  := c'
    c' := c.merge.shortcut--.prune
  return c'

end Circuit

end Vero
