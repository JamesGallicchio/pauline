import Lake
open System Lake DSL

package pauline {
  precompileModules := true
}

@[default_target]
lean_lib Pauline

@[default_target]
lean_exe test {
  root := `Main
}

-- require std from git "https://github.com/leanprover/std4" @ "v4.5.0"
require leancolls from git "https://github.com/T-Brick/LeanColls" @ "bump-v4.5.0"
-- require leancolls from git "https://github.com/JamesGallicchio/LeanColls" @ "main"
