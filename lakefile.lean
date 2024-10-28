import Lake
open Lake DSL

package «subterm_data» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require lean_extras from git 
  "https://github.com/adamtopaz/lean_extras.git"

@[default_target]
lean_exe «subterm_data» where
  root := `Main
  supportInterpreter := true
