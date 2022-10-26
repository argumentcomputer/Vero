import Lake
open Lake DSL

package vero {
  -- add package configuration options here
}

lean_lib Vero {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe vero {
  root := `Main
}
