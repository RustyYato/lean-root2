import Lake
open Lake DSL

package «root2» {
  -- add package configuration options here
}

lean_lib «Root2» {
  -- add library configuration options here
}

@[default_target]
lean_exe «root2» {
  root := `Main
}
