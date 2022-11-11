import Vero.Syntax.Core

namespace Vero.Syntax.Core.AST

namespace BOOL

def TT  := ⟦λ x y. x⟧
def FF  := ⟦λ x y. y⟧
def AND := ⟦λ p q. p q p⟧
def OR  := ⟦λ p q. p p q⟧
def NOT := ⟦λ p. p $FF $TT⟧

end BOOL

def NAT (n : Nat) : AST :=
  let app := nApp ⟦f⟧ ⟦x⟧ n
  ⟦λ f x. $app⟧

namespace NAT

def SUC := ⟦λ n f x. f (n f x)⟧
def ADD := ⟦λ m n f x. m f (n f x)⟧
def MUL := ⟦λ m n f. m (n f)⟧

end NAT

end Vero.Syntax.Core.AST
