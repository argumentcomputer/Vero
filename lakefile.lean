import Lake
open Lake DSL

package vero {
  -- add package configuration options here
}

lean_lib Vero {
  -- add library configuration options here
}

@[default_target]
lean_exe vero {
  root := `Main
}

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "02e423d02d2ba1b76bed3cf6459a5c2d7a13afb8"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "2b914196a8c67838e63c1c1e44eaf339b8a50eb7"

require std from git
  "https://github.com/leanprover/std4/" @ "22327ae0520d4e499503429565f79f179f83437a"

require Poseidon from git
  "https://github.com/yatima-inc/Poseidon.lean" @ "44fac19cebc3cb11e61526e824913a7ed842d435"

lean_exe Tests.Reduce
