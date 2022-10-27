import Vero.Circuit.Types

namespace Vero.Circuit

def Input.findShortcut : Input → Input
  | i@(.const _)
  | i@(.outer _) => i
  | .inner (.uno i) => i.findShortcut
  | i => i

namespace Gate

def unifyAdd : Gate → Gate
  | g@(duo .add i₁ i₂) => match compare i₁ i₂ with
    | .eq => duo .mul (.const 2) i₁
    | _ => g
  | uno (.inner g) => uno (.inner g.unifyAdd)
  | duo op (.inner g₁) (.inner g₂) => duo op (.inner g₁.unifyAdd) (.inner g₂.unifyAdd)
  | duo op (.inner g) i => duo op (.inner g.unifyAdd) i
  | duo op i (.inner g) => duo op i (.inner g.unifyAdd)
  | g => g

def mergeConst : Gate → Gate
  | duo .add (.const c₁) (.const c₂) => uno $ .const (c₁ + c₂)
  | duo .mul (.const c₁) (.const c₂) => uno $ .const (c₁ * c₂)
  | uno (.inner g) => uno (.inner g.mergeConst)
  | duo op (.inner g₁) (.inner g₂) =>
    duo op (.inner g₁.mergeConst) (.inner g₂.mergeConst)
  | duo op (.inner g) i => duo op (.inner g.mergeConst) i
  | duo op i (.inner g) => duo op i (.inner g.mergeConst)
  | g => g

open Input in
def shortcut : Gate → Gate
  | uno (.inner g) => g.shortcut
  | uno i => uno i.findShortcut
  | duo op (.inner g₁) (.inner g₂) =>
    duo op (findShortcut (.inner g₁.shortcut)) (findShortcut (.inner g₂.shortcut))
  | duo op i₁ (.inner g) => duo op i₁.findShortcut (findShortcut (.inner g.shortcut))
  | duo op (.inner g) i₂ => duo op (findShortcut (.inner g.shortcut)) i₂.findShortcut
  | duo op i₁ i₂ => duo op i₁.findShortcut i₂.findShortcut

partial def optimize (g : Gate) : Gate :=
  let g' := g.unifyAdd.mergeConst.shortcut
  if g' != g then g'.optimize
  else g'

end Gate

end Circuit

end Vero
