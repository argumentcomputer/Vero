import Std.Data.RBMap
import YatimaStdLib.Nat

namespace Vero.Core.Scalar

inductive Tag
  | var | lam | app
  | normLam | normNeu
  | envCons | envNil
  deriving Ord, Inhabited

def Tag.toString : Tag → String
  | var => "var"
  | lam => "lam"
  | app => "app"
  | normLam => "normLam"
  | normNeu => "normNeu"
  | envCons => "envCons"
  | envNil  => "envNil"

instance : ToString Tag := ⟨Tag.toString⟩

def N := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

abbrev F := Fin N

def F.asHex (n : F) : String :=
  n.val.asHex 64

instance : Inhabited F := ⟨.ofNat 0⟩

def F.zero : F := default
def F.one  : F := .ofNat 1
def F.succ (f : F) : F := f + .ofNat 1

def Tag.toF : Tag → F
  | var => .ofNat 0
  | lam => .ofNat 1
  | app => .ofNat 2
  | normLam => .ofNat 3
  | normNeu => .ofNat 4
  | envCons => .ofNat 5
  | envNil  => .ofNat 6

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
  | normLam : Ptr → Ptr → ExprF
  | normNeu : F → Ptr → ExprF
  | envCons : Ptr → Ptr → ExprF
  | envNil

def ExprF.toString : ExprF → String
  | .var n   => s!"var({n})"
  | .lam b   => s!"lam({b})"
  | .app f a => s!"app({f}, {a})"
  | normLam f l => s!"normLam({f}, {l})"
  | normNeu v l => s!"normNeu({v}, {l})"
  | envCons h t => s!"envCons({h}, {t})"
  | envNil => "envNil"

instance : ToString ExprF := ⟨ExprF.toString⟩

abbrev StoreF := Std.RBMap Ptr ExprF compare

def StoreF.toString (s : StoreF) : String :=
  let body := ",\n".intercalate $ s.toList.map fun (k, v) => s!"  {k}: {v}"
  "exprs: {\n" ++ body ++ "\n}"

instance : ToString StoreF := ⟨StoreF.toString⟩

end Vero.Core.Scalar
