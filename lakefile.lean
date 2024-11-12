import Lake
open Lake DSL

package «adele-ring_locally-compact» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "caac5b13fb72ba0c5d0b35a0067de108db65e964"

@[default_target]
lean_lib «AdeleRingLocallyCompact» {
  -- add any library configuration options here
}

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.10.0-rc1"
