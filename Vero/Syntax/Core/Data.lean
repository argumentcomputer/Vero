import Vero.Syntax.Core.AST

namespace Vero.Syntax.Core.AST

def NAT (n : Nat) : AST :=
  let app := nApp ⟦f⟧ ⟦x⟧ n
  ⟦λ f x. $app⟧

namespace NAT

def ADD  := ⟦λ m n f x. m f (n f x)⟧
def MUL  := ⟦λ m n f. m (n f)⟧
def SUCC := ⟦λ n f x. f (n f x)⟧
def PRED := ⟦λ n f x. n (λ g h. h (g f)) (λ u. x) (λ u. u)⟧
def SUB  := ⟦λ m n. n $PRED m⟧

end NAT

namespace BOOL

def TRUE   := ⟦λ x y. x⟧
def FALSE  := ⟦λ x y. y⟧
def AND    := ⟦λ p q. p q p⟧
def OR     := ⟦λ p q. p p q⟧
def NOT    := ⟦λ p. p $FALSE $TRUE⟧
def FORK   := ⟦λ p a b. p a b⟧
def ISZERO := ⟦λ n. n (λ x. $FALSE) $TRUE⟧
def LE     := ⟦λ m n. $ISZERO ($NAT.SUB m n)⟧

end BOOL

end Vero.Syntax.Core.AST
