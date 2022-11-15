namespace Vero

inductive Typ
  | nat
  | int
  | bool
  | pair : Typ → Typ → Typ
  | pi   : Typ → Typ → Typ
  deriving Ord, BEq, Inhabited, Repr

def Typ.toString : Typ → String
  | .nat  => "nat"
  | .int  => "int"
  | .bool => "bool"
  | .pair t₁          t₂ => s!"({t₁.toString} . {t₂.toString})"
  | .pi   pi@(.pi ..) t₂ => s!"({pi.toString}) -> {t₂.toString}"
  | .pi   t₁          t₂ => s!"{t₁.toString} -> {t₂.toString}"

instance : ToString Typ := ⟨Typ.toString⟩

end Vero
