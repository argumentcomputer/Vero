import Vero.Scalar.Datatypes
import YatimaStdLib.Fin
import Poseidon.ForLurk

namespace Vero.Scalar

def hashPtrPair (x y : Ptr) : F :=
  .ofInt $ Poseidon.Lurk.hash x.tag.toF x.val y.tag.toF y.val

def hashFPtr (f : F) (x : Ptr) : F :=
  -- use a simpler hashing function instead
  .ofInt $ Poseidon.Lurk.hash (.ofNat 7) f x.tag.toF x.val

def hashPtr (x : Ptr) : F :=
  -- use a simpler hashing function instead
  .ofInt $ Poseidon.Lurk.hash (.ofNat 8) F.zero x.tag.toF x.val

end Vero.Scalar
