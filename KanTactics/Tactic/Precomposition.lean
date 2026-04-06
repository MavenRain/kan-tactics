import KanTactics.Tactic.Core

/-!
# KanTactics.Tactic.Precomposition

Tactics derived from precomposition Kan extensions: `kan_apply` and `kan_refine`.

## apply as precomposition

Given a proof term f : A1 -> A2 -> ... -> An -> B, the functor K maps
the product (A1, ..., An) to B by applying f.  The identity functor F
preserves the domain types as subgoals.

The comma category (K | B) has a single object when the return type
of f unifies with B.  This object projects to n subgoals, one per
argument Ai of f that cannot be inferred.

The colimit assembly applies f to the subgoal proofs:

    f proof_A1 proof_A2 ... proof_An : B

## refine as partial precomposition

Like apply, but the term e may contain metavariable placeholders
(?_ or _).  Each placeholder becomes an independent subgoal in the
comma category.  This computes a partial Kan extension where some
components of the colimit are left undetermined, to be filled in
by subsequent tactic steps.
-/


open Lean Meta Elab Tactic

set_option autoImplicit false

/-- Apply as backward extension along a morphism.

    Given e whose type unifies with the goal after filling arguments:
    1. Comma category: unify the return type of e with the goal
    2. Subgoals: one per unsolved argument of e
    3. Assembly: e applied to all argument proofs -/
def applyKan (stx : Syntax) : KanComputation where
  name := "precomposition (apply)"
  kind := .precomposition
  execute := fun mvarId => do
    let e <- Lean.Elab.Term.elabTerm stx none
    mvarId.apply e

/-- Refine as partial precomposition with explicit holes.

    The term e may contain _ or ?_ placeholders.  Each placeholder is
    an undetermined component of the colimit, becoming a subgoal.

    Categorically: a partial section of the colimit cocone, with
    the missing components recorded as new proof obligations. -/
def refineKan (stx : Syntax) : KanComputation where
  name := "precomposition (refine)"
  kind := .precomposition
  execute := fun mvarId => do
    let target <- mvarId.getType
    let e <- Lean.Elab.Term.elabTerm stx (some target)
    mvarId.assign e
    -- Collect unassigned metavariables as new subgoals via filterM
    let unassigned <- (<- getMVars e).filterM fun m => do
      return !(<- m.isAssigned)
    pure unassigned.toList

/-- Apply: reduce the goal by backward extension along a morphism. -/
elab "kan_apply " e:term : tactic => kanExtend (applyKan e)

/-- Refine: partial precomposition with placeholders for missing components. -/
elab "kan_refine " e:term : tactic => kanExtend (refineKan e)
