import KanTactics.Tactic.Core

/-!
# KanTactics.Tactic.Decompose

Tactics derived from colimit decomposition Kan extensions:
`kan_cases` and `kan_rcases`.

## cases as coproduct elimination

An inductive type T ~= A1 + A2 + ... + An is a coproduct.
To prove P given h : T, we must prove P for each component:

    P given h matches c1(args1)
    P given h matches c2(args2)
    ...
    P given h matches cn(argsn)

The functor K maps each Ai to T via the constructor injection ci.
To map *out* of the coproduct, we need a map from each component.
The Kan extension at goal P decomposes the comma category:

    (K | h : T) has one object per constructor ci

Each object contributes a subgoal: prove P with the constructor's
arguments in context.  The assembly uses the type's recursor to
combine the per-constructor proofs.

## rcases as iterated decomposition

rcases recursively applies cases, decomposing nested inductive
types in one step.  This is the composition of multiple Kan extensions,
one per level of nesting.  Since Kan extensions compose, the recursive
decomposition is itself a single Kan extension.

NOTE: Full rcases pattern syntax (as in Mathlib) requires a custom
parser.  This implementation provides basic recursive decomposition.
-/


open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Case analysis: decompose a hypothesis into one subgoal per constructor. -/
elab "kan_cases " e:term : tactic => kanExtend (.colimitDecomposition e)

/-- Recursive case analysis (basic form; equivalent to kan_cases). -/
elab "kan_rcases " e:term : tactic => kanExtend (.colimitDecomposition e)
