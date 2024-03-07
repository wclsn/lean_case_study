import Lake
open Lake DSL

package «lean_case_study» {
  -- add package configuration options here
}
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.3.0-rc2"


@[default_target]
lean_lib «Lean_Case_Study» {
  -- add library configuration options here
}
