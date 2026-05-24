import Lake
open Lake DSL

package «kan-tactics» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «comp-cat-theory» from git
  "https://github.com/MavenRain/comp-cat-theory.git" @ "f521081"

@[default_target]
lean_lib «KanTactics» where
  roots := #[`KanTactics]

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
