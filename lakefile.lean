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

require std from git
  "https://github.com/leanprover/std4/" @ "22327ae0520d4e499503429565f79f179f83437a"