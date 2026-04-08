import KanTactics.Tactic.Core
import KanTactics.Tactic.Identity
import KanTactics.Tactic.Precomposition

/-!
# KanTactics.Tactic.Colimit

Tactics derived from colimit injection Kan extensions:
`kan_constructor`, `kan_use`, and `kan_exists`.

All three are derived from the primitives `kan_apply` and `kan_exact`.

## constructor as coproduct injection (Derived)

An inductive type T with constructors c1, ..., cn is a coproduct
(sum type) of the constructor argument types:

    T ~= A1 + A2 + ... + An

where Ai is the (dependent) product of arguments for constructor ci.

The functor K : coprod Ai -> T is the fold of the constructor
injections.  The Kan extension Lan_K Id at a goal of type T
selects a constructor ci and produces subgoals for its arguments.

Derived by looking up the first constructor name and delegating
to `kan_apply`.

## use/exists as existential injection (Derived)

For (Exists x, P(x)), the single constructor is Exists.intro.
Providing a witness a selects the specific injection

    iota_a : P(a) -> Exists x, P(x)

and produces the subgoal P(a).

Derived as `kan_constructor; kan_exact witness`.
`kan_exists` is a synonym for `kan_use`.
-/


open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Apply the first constructor of the goal's inductive type.
    Derived from `kan_apply`: looks up the constructor name,
    then delegates. -/
elab "kan_constructor" : tactic => do
  let mvarId <- getMainGoal
  let target <- instantiateMVars (<- mvarId.getType)
  let ctorName <- (<- firstCtorOf target).elim
    (pure `True)
    pure
  let stx := mkIdent ctorName
  evalTactic (<- `(tactic| kan_apply $stx))

/-- Provide a witness for an existential or constructor argument.
    Derived as `kan_constructor; kan_exact witness`. -/
elab "kan_use " e:term : tactic => do
  evalTactic (<- `(tactic| kan_constructor))
  evalTactic (<- `(tactic| kan_exact $e))

/-- Provide a witness for an existential (synonym for kan_use).
    Derived as `kan_constructor; kan_exact witness`. -/
elab "kan_exists " e:term : tactic => do
  evalTactic (<- `(tactic| kan_use $e))
