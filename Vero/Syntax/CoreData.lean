import Vero.Syntax.Core

namespace Vero.Syntax.Core.AST

namespace BOOL

def TT  := ⟦λ x y. x⟧
def FF  := ⟦λ x y. y⟧
def AND := ⟦λ p q. p q p⟧
def OR  := ⟦λ p q. p p q⟧
def NOT := ⟦λ p. p $FF $TT⟧

end BOOL

def nApp (f a : AST) : Nat → AST
  | 0 => a
  | n + 1 => .app f (nApp f a n)

def NAT (n : Nat) : AST :=
  let app := nApp ⟦f⟧ ⟦x⟧ n
  ⟦λ f x. $app⟧

#eval (NAT 3).ppReduce
-- "(λ λ 1 (1 (1 0)))"

namespace NAT

def SUCC := ⟦λ n f x. f (n f x)⟧
def ADD  := ⟦λ m n f x. m f (n f x)⟧
def PLUS  := ⟦λ m n. m $SUCC n⟧

#eval ⟦$ADD $(NAT 1) $(NAT 2)⟧.ppReduce
-- "(λ λ (λ λ 1 0) 1 ((λ λ 1 (1 0)) 1 0))"

#eval ⟦$PLUS $(NAT 1) $(NAT 2)⟧.ppReduce
-- "(λ λ 1 ((λ λ 1 (1 0)) 1 0))"

end NAT

end Vero.Syntax.Core.AST
