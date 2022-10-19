import Lake
open System Lake DSL

package pauline {
  precompileModules := true
}

@[defaultTarget]
lean_lib Pauline

@[defaultTarget]
lean_exe test {
  root := `Main
}

require std from git "https://github.com/JamesGallicchio/std4" @ "nonempty-lists"
