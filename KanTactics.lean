-- Categorical foundation: depend on comp-cat-theory for Category, Functor,
-- NatTrans, LeftKanExtension, RightKanExtension.
import CompCatTheory

-- Tactic layer: each tactic shown to be an instance of `kanExtend`.
import KanTactics.Tactic.Core
import KanTactics.Tactic.Identity
import KanTactics.Tactic.Precomposition
import KanTactics.Tactic.AdjUnit
import KanTactics.Tactic.Transport
import KanTactics.Tactic.Normalize
import KanTactics.Tactic.Colimit
import KanTactics.Tactic.Decompose
import KanTactics.Tactic.InitialAlgebra

-- Worked examples illustrating the Mac Lane dictum.
import KanTactics.Examples.LanAlongIdentity
import KanTactics.Examples.SmokeTest
