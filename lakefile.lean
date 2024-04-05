import Lake
open Lake DSL

package matroids {
  moreServerOptions := #[⟨`autoImplicit, false⟩, ⟨`pp.structureInstances, false⟩]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Matroids {
  globs := #[.submodules `Matroids]
  moreLeanArgs := #["-DautoImplicit=false"]
}
