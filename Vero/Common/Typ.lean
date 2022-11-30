namespace Vero

inductive Typ
  | hole
  | nat
  | bool
  | pair : Typ → Typ → Typ
  | pi   : Typ → Typ → Typ
  deriving Ord, BEq, Inhabited

def Typ.toString : Typ → String
  | .hole => "_"
  | .nat  => "nat"
  | .bool => "bool"
  | .pair t₁          t₂ => s!"({t₁.toString} . {t₂.toString})"
  | .pi   pi@(.pi ..) t₂ => s!"({pi.toString}) -> {t₂.toString}"
  | .pi   t₁          t₂ => s!"{t₁.toString} -> {t₂.toString}"

instance : ToString Typ := ⟨Typ.toString⟩

end Vero
