import Lake
open Lake DSL

package «morpho-midnight-verity» where
  version := v!"0.1.0"

require verity from git
  "https://github.com/lfglabs-dev/verity.git"@"c8764d6b9ee09480fbf0227b2f38c5e006686fd3"

@[default_target]
lean_lib «MorphoMidnight» where
  globs := #[.andSubmodules `MorphoMidnight]

lean_exe morpho_diff where
  root := `DiffMain
