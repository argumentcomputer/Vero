import Lean

namespace Vero

namespace Circuit

@[inline] def fmtIdx (i : Nat) : String :=
  s!"@{i}"

inductive Op
  | add | mul
  deriving Repr

def Op.toString : Op → String
  | .add => "+"
  | .mul => "*"

instance : ToString Op := ⟨Op.toString⟩

inductive Input
  | num : Nat → Input
  | var : Nat → Input

def Input.toString : Input → String
  | .num n => ToString.toString n
  | .var i => fmtIdx i

instance : ToString Input := ⟨Input.toString⟩

inductive Gate
  | eqId : Input → Gate
  | eqOp : Op → Input → Input → Gate

def Gate.toString : Gate → String
  | .eqId inp => inp.toString
  | .eqOp op inp₁ inp₂ => s!"{inp₁} {op} {inp₂}"

instance : ToString Gate := ⟨Gate.toString⟩

end Circuit

abbrev Circuit := Array Circuit.Gate

def Circuit.toString (c : Circuit) : String :=
  c.data.enum.foldl (init := "") fun acc (i, g) =>
    s!"{acc}{fmtIdx i} = {g}\n"

instance : ToString Circuit := ⟨Circuit.toString⟩

end Vero
