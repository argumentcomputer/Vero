import Vero.Core.Expr

namespace Vero.Frontend

inductive Lam
  | var : String → Lam
  | lam : String → Lam → Lam
  | app : Lam → Lam → Lam
  deriving Ord, Inhabited

class ToLam (α : Type _) where
  toLam : α → Lam

export ToLam (toLam)

instance : ToLam Lam := ⟨id⟩

namespace Lam

def telescopeLam (acc : Array String) : Lam → (Array String) × Lam
  | .lam n b => b.telescopeLam $ acc.push n
  | x => (acc, x)

def telescopeApp (acc : List Lam) : Lam → List Lam
  | .app f a => f.telescopeApp (a :: acc)
  | x => x :: acc

partial def toString : Lam → String
  | .var n => n
  | .lam n b =>
    let (ns, b) := b.telescopeLam #[n]
    s!"(λ {" ".intercalate ns.data}. {b.toString})"
  | .app f a@(.app ..) => s!"{f.toString} ({a.toString})"
  | .app f a =>
    let as := f.telescopeApp [a]
    s!"({" ".intercalate (as.map toString)})"

instance : ToString Lam where 
  toString := Lam.toString

end Lam

end Vero.Frontend
