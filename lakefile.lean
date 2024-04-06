import Lake
open Lake DSL

package «adele-ring_locally-compact» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require local_class_field_theory from git
  "https://github.com/mariainesdff/LocalClassFieldTheory.git"

@[default_target]
lean_lib «AdeleRingLocallyCompact» {
  -- add any library configuration options here
}

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
