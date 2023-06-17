import Lake
open Lake DSL

package «safeIdx» {
  -- add package configuration options here
}

lean_lib «SafeIdx» {
  -- add library configuration options here
}

@[default_target]
lean_exe «safeIdx» {
  root := `Main
}
