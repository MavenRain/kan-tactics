import KanTactics.Tactic.Core

/-!
# KanTactics.Tactic.Precomposition

Tactics derived from precomposition Kan extensions: `kan_apply` and `kan_refine`.

Both are primitive; neither is expressible in terms of the other due to
their different elaboration strategies.

## apply as precomposition (Primitive)

Given a proof term f : A1 -> A2 -> ... -> An -> B, the functor K maps
the product (A1, ..., An) to B by applying f.  The identity functor F
preserves the domain types as subgoals.

The comma category (K | B) has a single object when the return type
of f unifies with B.  This object projects to n subgoals, one per
argument Ai of f that cannot be inferred.

The colimit assembly applies f to the subgoal proofs:

    f proof_A1 proof_A2 ... proof_An : B

Uses unconstrained elaboration (`elabTerm stx none`) followed by
`forallMetaTelescopeReducing` (to introduce metavars for each
argument position) and `isDefEq` (to unify the return type with
the goal).  This is a restricted subset of Lean's `apply`: it does
not perform auto-intro, does not backtrack, and does not replicate
`apply`'s implicit-argument heuristics.  Within that subset, it
provides the exact precomposition semantics described above.

## refine as partial precomposition (Primitive)

Like apply, but the term e may contain metavariable placeholders
(?_ or _).  Each placeholder becomes an independent subgoal in the
comma category.  This computes a partial Kan extension where some
components of the colimit are left undetermined, to be filled in
by subsequent tactic steps.

Uses goal-directed elaboration (`elabTerm stx (some target)`) followed
by direct assignment and metavariable collection.  This elaboration
strategy differs fundamentally from `kan_apply`; there exist terms
where one succeeds and the other fails.
-/


open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Apply: reduce the goal by backward extension along a morphism.  (Primitive) -/
elab "kan_apply " e:term : tactic => kanExtend (.precomposition e)

/-- Refine: partial precomposition with placeholders for missing components.  (Primitive) -/
elab "kan_refine " e:term : tactic => kanExtend (.precompositionRefine e)
