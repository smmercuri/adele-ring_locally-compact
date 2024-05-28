import Lake
open Lake DSL

package «adele-ring_locally-compact» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "eaede86aa7777630a3826cd8f3fbf0cbaafa53e6"

@[default_target]
lean_lib «AdeleRingLocallyCompact» {
  -- add any library configuration options here
}

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "a34d3c1f7b72654c08abe5741d94794db40dbb2e"
