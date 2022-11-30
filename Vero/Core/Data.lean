import Vero.Core.DSL

namespace Vero.Core.Data

open DSL

def NAT (n : Nat) : AST :=
  let app := nApp ⟦f⟧ ⟦x⟧ n
  ⟦λ f x. $app⟧

namespace NAT

def SUCC := ⟦λ n f x. f (n f x)⟧
def PRED := ⟦λ n f x. n (λ g h. h (g f)) (λ u. x) (λ u. u)⟧
def ADD  := ⟦λ m n f x. m f (n f x)⟧
def MUL  := ⟦λ m n f. m (n f)⟧
def SUB  := ⟦λ m n. n $PRED m⟧
def DIV  := ADD -- fix
-- def DIV  := ⟦λ n. ((λ f. (λ x. x x) (λ x. f (x x)))
--                     (λ c. λ n. λ m. λ f. λ x.
--                       (λ d. (λ n. n (λ x. (λ a. λ b. b)) (λ a.λ b. a)) d ((λ f.λ x. x) f x) (f (c d m f x)))
--                       ((λ m. λ n. n (λ n. λ f. λ x. n (λ g.λ h. h (g f)) (λ u. x) (λ u. u)) m) n m)))
--                   ((λ n. λ f. λ x. f (n f x)) n)⟧

end NAT

namespace BOOL

def TRUE  := ⟦λ x y. x⟧
def FALSE := ⟦λ x y. y⟧
def AND   := ⟦λ p q. p q p⟧
def OR    := ⟦λ p q. p p q⟧
def NOT   := ⟦λ p a b. p b a⟧
def XOR   := ⟦λ a b. a ($NOT b) b⟧

def ISZ := ⟦λ n. n (λ x. $FALSE) $TRUE⟧
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
