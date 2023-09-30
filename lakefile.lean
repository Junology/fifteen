import Lake
open Lake DSL

package «fifteen» {
  -- add package configuration options here
}

lean_lib «Fifteen» {
  -- add library configuration options here
}

require std from git
  "https://github.com/leanprover/std4" @ "v4.0.0"

require proofwidgets from git
  "https://github.com/EdAyers/ProofWidgets4" @ "v0.0.16"

@[default_target]
lean_exe «fifteen» {
  root := `Main
}
