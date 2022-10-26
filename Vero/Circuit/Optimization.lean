import Vero.Circuit.Types

namespace Vero.Circuit

def Input.findShortcut : Input → Input
  | i@(.const _)
  | i@(.outer _) => i
  | .inner (.uno i) => i.findShortcut
  | i => i

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
  | uno (.inner g) => g.shortcut
  | uno i => uno i.findShortcut
  | add (.inner g₁) (.inner g₂) =>
    add (Input.inner g₁.shortcut).findShortcut (Input.inner g₂.shortcut).findShortcut
  | add i₁ (.inner g) => add i₁.findShortcut (Input.inner g.shortcut).findShortcut
  | add (.inner g) i₂ => add (Input.inner g.shortcut).findShortcut i₂.findShortcut
  | add i₁ i₂ => add i₁.findShortcut i₂.findShortcut
  | mul (.inner g₁) (.inner g₂) =>
    mul (Input.inner g₁.shortcut).findShortcut (Input.inner g₂.shortcut).findShortcut
  | mul i₁ (.inner g) => mul i₁.findShortcut (Input.inner g.shortcut).findShortcut
  | mul (.inner g) i₂ => mul (Input.inner g.shortcut).findShortcut i₂.findShortcut
  | mul i₁ i₂ => mul i₁.findShortcut i₂.findShortcut

partial def optimize (g : Gate) : Gate :=
  let g' := g.merge.shortcut
  if g' != g then g'.optimize
  else g'

end Gate

def optimize : Circuit → Circuit :=
  Gate.optimize

end Circuit

end Vero
