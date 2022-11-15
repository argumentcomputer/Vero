import Std.Data.RBMap
import YatimaStdLib.Nat

namespace Vero.Scalar

inductive Tag
  | var | lam | app
  deriving Ord, Inhabited

def Tag.toString : Tag → String
  | var => "var"
  | lam => "lam"
  | app => "app"

instance : ToString Tag := ⟨Tag.toString⟩

def N := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

abbrev F := Fin N

def F.asHex (n : F) : String :=
  n.val.asHex 64

instance : Inhabited F := ⟨.ofNat 0⟩

def F.zero : F := default
def F.succ (f : F) : F := f + .ofNat 1
def F.pred (f : F) : F := f - .ofNat 1

def Tag.toF : Tag → F
  | var => .ofNat 0
  | lam => .ofNat 1
  | app => .ofNat 2

structure Ptr where
  tag : Tag
  val : F
  deriving Ord, Inhabited

def Ptr.toString : Ptr → String
  | ⟨.var, n⟩ => s!"(var, {n.val})"
  | ⟨tag, val⟩ => s!"({tag}, {val.asHex})"

instance : ToString Ptr := ⟨Ptr.toString⟩

inductive ExprF where
  | var : F → ExprF
  | lam : Ptr → ExprF
  | app : Ptr → Ptr → ExprF

def ExprF.toString : ExprF → String
  | .var n   => s!"var({n})"
  | .lam b   => s!"lam({b})"
  | .app f a => s!"app({f}, {a})"

instance : ToString ExprF := ⟨ExprF.toString⟩

abbrev StoreF := Std.RBMap Ptr ExprF compare

def StoreF.toString (s : StoreF) : String :=
  let body := ",\n".intercalate $ s.toList.map fun (k, v) => s!"  {k}: {v}"
  "exprs: {\n" ++ body ++ "\n}"

instance : ToString StoreF := ⟨StoreF.toString⟩

end Vero.Scalar
