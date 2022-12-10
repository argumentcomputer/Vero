import Vero.Scalar.Datatypes
import YatimaStdLib.Fin
import Poseidon.ForLurk

namespace Vero.Scalar

def hashPtrPair (x y : Ptr) : F :=
  .ofInt $ Poseidon.Lurk.hash x.tag.toF x.val y.tag.toF y.val

def hashFPtr (f : F) (x : Ptr) : F :=
  hashPtrPair ⟨.envNil, f⟩ x -- use a simpler hashing function instead

def hashPtr (x : Ptr) : F :=
  hashPtrPair x default -- use a simpler hashing function instead

end Vero.Scalar
