import Lake
open Lake DSL

require «lean-gccjit» from git "https://github.com/schrodingerzhu/lean-gccjit" @ "a35ccb2ad8ede0425967e6f905b867d80b6ca729"

package «LeanGccBackend» where
  -- add package configuration options here

lean_lib «LeanGccBackend» where
  -- add library configuration options here

@[default_target]
lean_exe «leangccbackend» where
  root := `Main
  moreLinkArgs := #["-lgccjit"] -- add this line
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
