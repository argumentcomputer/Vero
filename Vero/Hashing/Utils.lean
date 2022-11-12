import Vero.Hashing.Datatypes
import YatimaStdLib.Fin
import Poseidon.ForLurk

namespace Vero.Hashing

def hashPtrPair (x y : Ptr) : F :=
  .ofInt $ Poseidon.Lurk.hash x.tag.toF x.val y.tag.toF y.val

def hashPtr (x : Ptr) : F :=
  hashPtrPair x default -- use a simpler hashing function instead

end Vero.Hashing
