import Vero.Frontend.Lam.DSL

namespace Vero.Frontend.Lam.Data

open DSL

def NAT : Nat → Lam
| 0     => ⟦λ z s. z⟧
| n + 1 => ⟦λ z s. s $(NAT n)⟧

def FIX (e : Lam) : Lam :=
  .app ⟦λ f. (λ x. f (λ v. x x v)) (λ x. f (λ v. x x v))⟧ e

namespace NAT

-- Constructors
def ZERO := ⟦λ z s. z⟧
def SUCC := ⟦λ n z s. s n⟧

-- Functions on Nat
def PRED := ⟦λ n. n $ZERO (λ pred. pred)⟧
def ADD  := FIX ⟦λ add n. n (λ m. m) (λ pred m. add pred ($SUCC m))⟧
def MUL  := FIX ⟦λ mul n. n (λ m. $ZERO) (λ pred m. $ADD m (mul pred m))⟧
def SUB  := FIX ⟦λ sub n m. m n (λ pred. sub ($PRED n) pred)⟧

/--
Extracted from:

let div n d :=
  if d = 0 then 0 else
    rec aux n d acc :=
      if n < d then acc else aux (n - d) d (acc + 1);
    aux n d 0;
div
-/
def DIV  := ⟦λ n d. ((λ p a b. (p a b)) ((λ m n. (λ p q. (p q p)) (((λ m n. (λ n. (n (λ x y. x) (λ x x y. y))) (((λ f. ((λ x. (f (λ v. (x x v)))) (λ x. (f (λ v. (x x v)))))) (λ sub n m. (m n (λ pred. (sub ((λ n. (n (λ z s. z) (λ pred. pred))) n) pred)))) m n))) m n)) (((λ m n. (λ n. (n (λ x y. x) (λ x x y. y))) (((λ f. ((λ x. (f (λ v. (x x v)))) (λ x. (f (λ v. (x x v)))))) (λ sub n m. (m n (λ pred. (sub ((λ n. (n (λ z s. z) (λ pred. pred))) n) pred)))) m n))) n m))) d (λ z s. z)) (λ ζ z s. z) (λ ζ. (λ aux. (aux n d (λ z s. z))) (((λ f. ((λ x. (f (λ v. (x x v)))) (λ x. (f (λ v. (x x v)))))) (λ aux n d acc. ((λ p a b. (p a b)) ((λ m n. (λ n. (n (λ x y. x) (λ x x y. y))) (((λ f. ((λ x. (f (λ v. (x x v)))) (λ x. (f (λ v. (x x v)))))) (λ sub n m. (m n (λ pred. (sub ((λ n. (n (λ z s. z) (λ pred. pred))) n) pred)))) ((λ n z s. (s n)) m) n))) n d) (λ ζ. acc) (λ ζ. (aux ((λ f. ((λ x. (f (λ v. (x x v)))) (λ x. (f (λ v. (x x v)))))) (λ sub n m. (m n (λ pred. (sub ((λ n. (n (λ z s. z) (λ pred. pred))) n) pred)))) n d) d) (((λ n z s. (s n)) acc))) ζ))))) ζ)⟧

end NAT

namespace BOOL

def TT  := ⟦λ x y. x⟧
def FF  := ⟦λ x y. y⟧
def AND := ⟦λ p q. p q p⟧
def OR  := ⟦λ p q. p p q⟧
def NOT := ⟦λ p a b. p b a⟧
def XOR := ⟦λ a b. a ($NOT b) b⟧

def ISZ := ⟦λ n. n $TT (λ x. $FF)⟧
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
def INT : Int → Lam
  | .ofNat   n => ⟦$PAIR.PROD $BOOL.FF $(NAT n)⟧
  | .negSucc n => ⟦$PAIR.PROD $BOOL.TT $(NAT (n + 1))⟧

namespace INT

open PAIR BOOL

def NEG := ⟦λ a. $PROD ($NOT ($FST a)) ($SND a)⟧
def MUL := ⟦λ a b. $PROD ($XOR ($FST a) ($FST b)) ($NAT.MUL ($SND a) ($SND b))⟧
-- def DIV := ⟦λ a b. $PROD ($XOR ($FST a) ($FST b)) ($NAT.DIV ($SND a) ($SND b))⟧

-- def ADD : Lam := sorry
-- def SUB := ⟦λ a b. $ADD a ($NEG b)⟧

end INT

end Vero.Frontend.Lam.Data
