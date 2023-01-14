import Lake
open Lake DSL

package vero

lean_lib Vero

@[default_target]
lean_exe vero where
  root := `Main

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "704823e421b333ea9960347e305c60f654618422"

require std from git
  "https://github.com/leanprover/std4/" @ "fde95b16907bf38ea3f310af406868fc6bcf48d1"

require Poseidon from git
  "https://github.com/yatima-inc/Poseidon.lean" @ "cfda9cb724febf6894af59515860b34426a970d9"

lean_exe Tests.Reduction
lean_exe Tests.TypeInference
