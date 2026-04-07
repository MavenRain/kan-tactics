import KanTactics.Tactic.Core

/-!
# KanTactics.Tactic.Colimit

Tactics derived from colimit injection Kan extensions:
`kan_constructor`, `kan_use`, and `kan_exists`.

## constructor as coproduct injection

An inductive type T with constructors c1, ..., cn is a coproduct
(sum type) of the constructor argument types:

    T ~= A1 + A2 + ... + An

where Ai is the (dependent) product of arguments for constructor ci.

The functor K : coprod Ai -> T is the fold of the constructor
injections.  The Kan extension Lan_K Id at a goal of type T
selects a constructor ci and produces subgoals for its arguments.

The comma category (K | T) has one object per constructor.
`constructor` picks the first one.

## use/exists as existential injection

For (Exists x, P(x)), the single constructor is Exists.intro.
Providing a witness a selects the specific injection

    iota_a : P(a) -> Exists x, P(x)

and produces the subgoal P(a).

Categorically, `use a` is the Kan extension that restricts the
comma category to the single injection at a, then extends.
-/


open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Apply the first constructor of the goal's inductive type. -/
elab "kan_constructor" : tactic => kanExtend .colimitInjection

/-- Provide a witness for an existential or constructor argument. -/
elab "kan_use " e:term : tactic => kanExtend (.colimitInjectionUse e)

/-- Provide a witness for an existential (synonym for kan_use). -/
elab "kan_exists " e:term : tactic => kanExtend (.colimitInjectionUse e)
