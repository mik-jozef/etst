import Lake
open Lake DSL

-- (I forgot what it stands for. (Extensional triset theory?))
package Etst {
  moreLeanArgs := #["-DautoImplicit=false"]
}

@[default_target]
lean_lib Etst {
  globs := #[.submodules `Etst]
}

lean_lib old {}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
