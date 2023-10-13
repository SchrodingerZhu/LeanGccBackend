import Lake
open Lake DSL

require «lean-gccjit» from git "https://github.com/schrodingerzhu/lean-gccjit" @ "0.1.3"

package «LeanGccBackend» where
  -- add package configuration options here

lean_lib «LeanGccBackend» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-testc» where
  srcDir := "bin"
  root := `LeanTestC
  moreLinkArgs := #["-lgccjit"] -- add this line
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
