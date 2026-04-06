import Lake
open Lake DSL

package «kan-tactics» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «KanTactics» where
  roots := #[`KanTactics]

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
