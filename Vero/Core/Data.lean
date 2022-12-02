import Vero.Core.DSL

namespace Vero.Core.Data

open DSL

def NAT : (n : Nat) → AST
| 0 => ⟦λ z s. z⟧
| n+1 =>
  let pred := NAT n
  ⟦λ z s. s $pred⟧

namespace FIX

def Y := ⟦λ f. (λ x. f (x x)) (λ x. f (x x))⟧
def Θ := ⟦(λ x y. y (x x y)) (λ x y. y (x x y))⟧
def Z := ⟦λ f. (λ x. f (λ v. x x v)) (λ x. f (λ v. x x v))⟧

def fix (expr : AST) : AST := .app Z expr

end FIX

namespace NAT

-- Constructors
def ZERO := ⟦λ z s. z⟧
def SUCC := ⟦λ n z s. s n⟧

-- Functions on Nat
def PRED := ⟦λ n. n $ZERO (λ pred. pred)⟧
def ADD  := FIX.fix ⟦λ add n. n (λ m. m) (λ pred m. add pred (succ m))⟧
def MUL  := FIX.fix ⟦λ mul n. n (λ m. m) (λ pred m. $ADD m (mul pred m))⟧
def SUB  := FIX.fix ⟦λ sub n m. m n (λ pred. sub ($PRED n) pred)⟧
def DIV : AST := ⟦srry⟧

end NAT

namespace BOOL

def TRUE  := ⟦λ x y. x⟧
def FALSE := ⟦λ x y. y⟧
def AND   := ⟦λ p q. p q p⟧
def OR    := ⟦λ p q. p p q⟧
def NOT   := ⟦λ p a b. p b a⟧
def XOR   := ⟦λ a b. a ($NOT b) b⟧

def ISZ := ⟦λ n. n $TRUE (λ x. $FALSE)⟧
def LE  := ⟦λ m n. $ISZ ($NAT.SUB m n)⟧
def LT  := ⟦λ m n. $ISZ ($NAT.SUB ($NAT.SUCC m) n)⟧
def EQ  := ⟦λ m n. $AND ($LE m n) ($LE n m)⟧
def NEQ := ⟦λ m n. $NOT ($AND ($LE m n) ($LE n m))⟧

end BOOL

def FLOW.FORK := ⟦λ p a b. p a b⟧

namespace PAIR

def PROD := ⟦λ a b f. f a b⟧
def FST  := ⟦λ p. p (λ x y. x)⟧
def SND  := ⟦λ p. p (λ x y. y)⟧

end PAIR

/--
A `true` on the first component means a negative number. This simplifies
multiplication and division by avoiding a `not` on the `xor` for the signal.
-/
def INT : Int → AST
  | .ofNat   n => ⟦$PAIR.PROD $BOOL.FALSE $(NAT n)⟧
  | .negSucc n => ⟦$PAIR.PROD $BOOL.TRUE  $(NAT (n + 1))⟧

namespace INT

open PAIR BOOL

def NEG := ⟦λ a. $PROD ($NOT ($FST a)) ($SND a)⟧
def MUL := ⟦λ a b. $PROD ($XOR ($FST a) ($FST b)) ($NAT.MUL ($SND a) ($SND b))⟧
-- def DIV := ⟦λ a b. $PROD ($XOR ($FST a) ($FST b)) ($NAT.DIV ($SND a) ($SND b))⟧

-- def ADD : AST := sorry
-- def SUB := ⟦λ a b. $ADD a ($NEG b)⟧

end INT

end Vero.Core.Data
